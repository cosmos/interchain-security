package types_test

import (
	"testing"

	"github.com/cosmos/interchain-security/testutil/crypto"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
)

func TestPacketDataValidateBasic(t *testing.T) {

	cId1 := crypto.NewCryptoIdentityFromRandSeed()
	cId2 := crypto.NewCryptoIdentityFromRandSeed()

	cases := []struct {
		name       string
		expError   bool
		packetData types.ValidatorSetChangePacketData
	}{
		{
			"nil packet data",
			true,
			types.NewValidatorSetChangePacketData(nil, 1, nil),
		},
		{
			"empty packet data",
			true,
			types.NewValidatorSetChangePacketData([]abci.ValidatorUpdate{}, 2, nil),
		},
		{
			"valid packet data",
			false,
			types.NewValidatorSetChangePacketData(
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

	cId1 := crypto.NewCryptoIdentityFromRandSeed()
	cId2 := crypto.NewCryptoIdentityFromRandSeed()

	vpd := types.NewValidatorSetChangePacketData(
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
