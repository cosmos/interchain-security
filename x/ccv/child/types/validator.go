package types

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

func NewCCValidator(change abci.ValidatorUpdate) *CrossChainValidator {
	return &CrossChainValidator{
		Address:         utils.GetChangePubKeyAddress(change),
		ValidatorUpdate: change,
	}
}

func (v CrossChainValidator) PublicKey() cryptotypes.PubKey {
	pk, err := cryptocodec.FromTmProtoPublicKey(v.ValidatorUpdate.PubKey)
	if err != nil {
		panic(err)
	}
	return pk
}
