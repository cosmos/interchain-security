package core_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	"github.com/cosmos/interchain-security/core"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
)

func TestPacketDataValidateBasic(t *testing.T) {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	cases := []struct {
		name       string
		expError   bool
		packetData core.ValidatorSetChangePacketData
	}{
		{
			"nil packet data",
			true,
			core.NewValidatorSetChangePacketData(nil, 1, nil),
		},
		{
			"empty packet data",
			true,
			core.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 2, nil),
		},
		{
			"valid packet data",
			false,
			core.NewValidatorSetChangePacketData(
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
				3,
				nil,
			),
		},
	}

	for _, c := range cases {
		err := c.packetData.ValidateBasic()
		if c.expError {
			require.Error(t, err, "%s invalid but passed ValidateBasic", c.name)
		} else {
			require.NoError(t, err, "%s valid but ValidateBasic returned error: %w", c.name, err)
		}
	}
}

func TestMarshalPacketData(t *testing.T) {
	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)
	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	require.NoError(t, err)

	vpd := core.NewValidatorSetChangePacketData(
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

	recovered := core.ValidatorSetChangePacketData{}
	err = recovered.Unmarshal(bz)
	require.Nil(t, err)
	require.Equal(t, vpd, recovered, "unmarshaled packet data does not equal original value")
}
