package types_test

import (
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	cryptoutil "github.com/cosmos/interchain-security/v5/testutil/crypto"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	"github.com/stretchr/testify/require"
)

func TestMsgAssignConsumerKeyValidateBasic(t *testing.T) {
	cId1 := cryptoutil.NewCryptoIdentityFromIntSeed(35443543534)
	cId2 := cryptoutil.NewCryptoIdentityFromIntSeed(65465464564)

	valOpAddr1 := cId1.SDKValOpAddress()
	acc1 := sdk.AccAddress(valOpAddr1.Bytes()).String()
	acc2 := sdk.AccAddress(cId2.SDKValOpAddress().Bytes()).String()

	longChainId := "abcdefghijklmnopqrstuvwxyz"
	for i := 0; i < 3; i++ {
		longChainId += longChainId
	}

	testCases := []struct {
		name         string
		chainId      string
		providerAddr string
		signer       string
		consumerKey  string
		expErr       bool
	}{
		{
			name:   "chain Id empty",
			expErr: true,
		},
		{
			name:    "chain Id too long",
			chainId: longChainId,
			expErr:  true,
		},
		{
			name:    "invalid provider address",
			chainId: "chainId",
			expErr:  true,
		},
		{
			name:         "invalid signer address: must be the same as the provider address",
			chainId:      "chainId",
			providerAddr: valOpAddr1.String(),
			signer:       acc2,
			expErr:       true,
		},
		{
			name:         "invalid consumer pubkey",
			chainId:      "chainId",
			providerAddr: valOpAddr1.String(),
			signer:       acc1,
			expErr:       true,
		},
		{
			name:         "valid assign consumer key msg",
			chainId:      "chainId",
			providerAddr: valOpAddr1.String(),
			consumerKey:  "{\"@type\": \"/cosmos.crypto.ed25519.PubKey\", \"key\": \"e3BehnEIlGUAnJYn9V8gBXuMh4tXO8xxlxyXD1APGyk=\"}",
			signer:       acc1,
			expErr:       false,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {

			msg := types.MsgAssignConsumerKey{
				ChainId:      tc.chainId,
				ConsumerKey:  tc.consumerKey,
				ProviderAddr: tc.providerAddr,
				Signer:       tc.signer,
			}

			err := msg.ValidateBasic()
			if tc.expErr {
				require.Error(t, err)
			} else {
				require.NoError(t, err)
			}
		})
	}
}
