package types_test

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	abci "github.com/cometbft/cometbft/abci/types"

	"github.com/cosmos/interchain-security/v4/testutil/crypto"
	"github.com/cosmos/interchain-security/v4/x/ccv/types"
)

func TestPacketDataValidateBasic(t *testing.T) {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	cId := crypto.NewCryptoIdentityFromIntSeed(4732894342)
	validSlashAck := cId.SDKValConsAddress().String()
	tooLongSlashAck := string(make([]byte, 1024))

	cases := []struct {
		name       string
		expError   bool
		packetData types.ValidatorSetChangePacketData
	}{
		{
			"invalid: nil packet data",
			true,
			types.NewValidatorSetChangePacketData(nil, 1, nil),
		},
		{
			"valid: empty packet data",
			false,
			types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 2, nil),
		},
		{
			"invalid: slash ack not consensus address",
			true,
			types.NewValidatorSetChangePacketData(
				[]abci.ValidatorUpdate{
					{
						PubKey: pk1,
						Power:  30,
					},
				},
				3,
				[]string{
					"some_string",
				},
			),
		},
		{
			"valid: packet data with valid slash ack",
			false,
			types.NewValidatorSetChangePacketData(
				[]abci.ValidatorUpdate{
					{
						PubKey: pk2,
						Power:  20,
					},
				},
				4,
				[]string{
					validSlashAck,
				},
			),
		},
		{
			"invalid: slash ack is too long",
			true,
			types.NewValidatorSetChangePacketData(
				[]abci.ValidatorUpdate{
					{
						PubKey: pk2,
						Power:  20,
					},
				},
				5,
				[]string{
					tooLongSlashAck,
				},
			),
		},
		{
			"valid: packet data with nil slash ack",
			false,
			types.NewValidatorSetChangePacketData(
				[]abci.ValidatorUpdate{
					{
						PubKey: pk1,
						Power:  30,
					},
					{
						PubKey: pk2,
						Power:  20,
					},
				},
				6,
				nil,
			),
		},
	}

	for _, c := range cases {
		err := c.packetData.Validate()
		if c.expError {
			require.Error(t, err, "%s invalid but passed Validate", c.name)
		} else {
			require.NoError(t, err, "%s valid but Validate returned error: %w", c.name, err)
		}
	}
}

func TestMarshalPacketData(t *testing.T) {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	vpd := types.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: pk1,
				Power:  30,
			},
			{
				PubKey: pk2,
				Power:  20,
			},
		},
		1,
		nil,
	)

	bz, err := vpd.Marshal()
	require.NoError(t, err, "marshalling packet data returned error")

	recovered := types.ValidatorSetChangePacketData{}
	err = recovered.Unmarshal(bz)
	require.Nil(t, err)
	require.Equal(t, vpd, recovered, "unmarshaled packet data does not equal original value")
}

// TestVSCPacketDataWireBytes is a regression test that the JSON schema
// for ValidatorSetChangePacketData (sent over the wire) does not change.
func TestVSCPacketDataWireBytes(t *testing.T) {
	cId1 := crypto.NewCryptoIdentityFromIntSeed(4732894)
	cId2 := crypto.NewCryptoIdentityFromIntSeed(4732895)

	pd := types.NewValidatorSetChangePacketData(
		[]abci.ValidatorUpdate{
			{
				PubKey: cId1.TMProtoCryptoPublicKey(),
				Power:  30,
			},
			{
				PubKey: cId2.TMProtoCryptoPublicKey(),
				Power:  20,
			},
		},
		73,
		[]string{"slash", "acks", "example"},
	)

	jsonBz := pd.GetBytes()
	str := string(jsonBz)

	// Expected string formatted for human readability
	expectedStr := `{
		"validator_updates": [
			{
				"pub_key": {
					"ed25519": "SMxP2pXAuxQC7FmBn4dh4Kt5eYdQFWC/wN7oWobZKds="
				},
				"power": "30"
			},
			{
				"pub_key": {
					"ed25519": "J/nGy0vCXhgVbr8S71B4ZgHi4fsMqtDxDlERZ+gG238="
				},
				"power": "20"
			}
		],
		"valset_update_id": "73",
		"slash_acks": ["slash", "acks", "example"]
	}`

	// Remove newlines, tabs, and spaces for comparison
	expectedStr = strings.ReplaceAll(expectedStr, "\n", "")
	expectedStr = strings.ReplaceAll(expectedStr, "\t", "")
	expectedStr = strings.ReplaceAll(expectedStr, " ", "")

	require.Equal(t, expectedStr, str)
}

// TestSlashPacketDataWireBytes is a regression test that the JSON schema
// for SlashPacketData (sent over the wire) does not change.
func TestSlashPacketDataWireBytes(t *testing.T) {
	// Construct consumer packet data wrapping slash packet data
	cId := crypto.NewCryptoIdentityFromIntSeed(4732894342)
	slashPacketData := types.NewSlashPacketData(
		abci.Validator{
			Address: cId.SDKValConsAddress(),
			Power:   int64(4328),
		},
		uint64(894732),
		stakingtypes.Infraction_INFRACTION_DOUBLE_SIGN,
	)

	// The type that'd be JSON marshaled and sent over the wire
	cpd := types.NewConsumerPacketData(
		types.SlashPacket,
		&types.ConsumerPacketData_SlashPacketData{
			SlashPacketData: slashPacketData,
		},
	)

	jsonBz := cpd.GetBytes()
	str := string(jsonBz)

	// Expected string formatted for human readability
	expectedStr := `{
		"type": "CONSUMER_PACKET_TYPE_SLASH",
		"slashPacketData": {
			"validator": {
				"address": "BP9q4oXCgubvoujOKyxIxd+3IwM=",
				"power": "4328"
			},
			"valset_update_id": "894732",
			"infraction": "INFRACTION_TYPE_DOUBLE_SIGN"
		}
	}`

	// Remove newlines, tabs, and spaces for comparison
	expectedStr = strings.ReplaceAll(expectedStr, "\n", "")
	expectedStr = strings.ReplaceAll(expectedStr, "\t", "")
	expectedStr = strings.ReplaceAll(expectedStr, " ", "")

	require.Equal(t, expectedStr, str)
}

// TestVSCMaturedPacketDataWireBytes is a regression test that the JSON schema
// for VSCMaturedPacketData (sent over the wire) does not change.
func TestVSCMaturedPacketDataWireBytes(t *testing.T) {
	// Construct consumer packet data wrapping vsc matured packet data
	cpd := types.ConsumerPacketData{
		Type: types.VscMaturedPacket,
		Data: &types.ConsumerPacketData_VscMaturedPacketData{
			VscMaturedPacketData: types.NewVSCMaturedPacketData(84923),
		},
	}

	jsonBz := cpd.GetBytes()
	str := string(jsonBz)

	// Expected string formatted for human readability
	expectedStr := `{
		"type": "CONSUMER_PACKET_TYPE_VSCM",
		"vscMaturedPacketData": {
			"valset_update_id": "84923"
		}	
	}`

	// Remove newlines, tabs, and spaces for comparison
	expectedStr = strings.ReplaceAll(expectedStr, "\n", "")
	expectedStr = strings.ReplaceAll(expectedStr, "\t", "")
	expectedStr = strings.ReplaceAll(expectedStr, " ", "")

	require.Equal(t, expectedStr, str)
}
