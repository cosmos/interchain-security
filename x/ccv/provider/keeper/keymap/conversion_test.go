package keymap

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TODO:
func TestConversion(t *testing.T) {
	originalPK := ed25519.GenPrivKey().PubKey()
	arb, err := cryptocodec.ToTmProtoPublicKey(originalPK)
	if err != nil {
		t.Fatalf("Bad")
	}
	update := abci.ValidatorUpdate{PubKey: arb, Power: 42}
	addr := utils.GetChangePubKeyAddress(update)
	cons := sdk.ConsAddress(addr)
	_ = cons
	// v := abci.Validator{}
	// cons := sdk.ConsAddress(v.Address)
}

// TODO: id like to test the real interaction here
func TestConversionRealistic(t *testing.T) {

}
