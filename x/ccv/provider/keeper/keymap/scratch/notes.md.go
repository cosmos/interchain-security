// The slash packet contains

// Validator
type Validator struct {
	Address []byte `protobuf:"bytes,1,opt,name=address,proto3" json:"address,omitempty"`
	// PubKey pub_key = 2 [(gogoproto.nullable)=false];
	Power int64 `protobuf:"varint,3,opt,name=power,proto3" json:"power,omitempty"`
}

// I can get a consAddress via

consAddr := sdk.ConsAddress(validator.Address)

// I can use

func ToTmProtoPublicKey(pk cryptotypes.PubKey) (tmprotocrypto.PublicKey, error) {
	switch pk := pk.(type) {
	case *ed25519.PubKey:
		return tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Ed25519{
				Ed25519: pk.Key,
			},
		}, nil
	case *secp256k1.PubKey:
		return tmprotocrypto.PublicKey{
			Sum: &tmprotocrypto.PublicKey_Secp256K1{
				Secp256K1: pk.Key,
			},
		}, nil
	default:
		return tmprotocrypto.PublicKey{}, sdkerrors.Wrapf(sdkerrors.ErrInvalidType, "cannot convert %v to Tendermint public key", pk)
	}
}

// to get a tendermint PublicKey


// Alternate:
// I think I can use


// get ConsAddress from pubkey
func GetConsAddress(pubkey cryptotypes.PubKey) ConsAddress {
	return ConsAddress(pubkey.Address())
}

// inside keymap to implement the reverse lookup


/////////////////////// OK
// When a consumer receives an update, it receives the tendermint public key
// it does THIS
addr := utils.GetChangePubKeyAddress(change)
consAddr := sdk.ConsAddress(addr)
// to get the cons address

// if I change keymap to store a map of cons addresses, then
// the slash will send a cons address
// the reverse cons address can be looked up


// in order to send updates, convert the output of the staking module
// to the address using the above function