package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctesting "github.com/cosmos/ibc-go/testing"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestValidatorByConsAddr
func (s *KeeperTestSuite) TestValidatorByConsAddr() {
	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.childChain.GetContext()

	// create validator
	pubKey := ed25519.GenPrivKey().PubKey()
	expConsAddr := sdk.ConsAddress(pubKey.Address())
	votingPower := int64(1)

	// expect unfound
	_, found := childKeeper.GetValidatorByConsAddr(ctx, expConsAddr)
	s.Require().False(found)

	// create and store validator by consensus address
	val, err := types.NewValidator(pubKey, votingPower)

	s.Require().NoError(err)
	s.Require().NotZero(val)
	childKeeper.SetValidatorByConsAddr(ctx, val)

	// get validator by consensus address
	res, found := childKeeper.GetValidatorByConsAddr(ctx, expConsAddr)
	s.Require().True(found)
	s.Require().NotZero(res)

	consAddr, err := res.GetConsAddr()
	s.Require().NoError(err)

	s.Require().EqualValues(expConsAddr, consAddr)

	gotPK, err := res.ConsPubKey()
	s.Require().NoError(err)

	s.Require().EqualValues(pubKey, gotPK)
}

func (s *KeeperTestSuite) TestGetAllValidators() {
	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.childChain.GetContext()

	// create and persist three validators
	vals := map[string]types.Validator{}

	for i := 0; i < 3; i++ {
		pubKey := ed25519.GenPrivKey().PubKey()
		val, err := types.NewValidator(pubKey, int64(i+1))
		s.Require().NoError(err)
		vals[val.ConsensusAddress] = val
		childKeeper.SetValidatorByConsAddr(ctx, val)
	}

	gotVals := childKeeper.GetAllValidators(ctx)
	s.Require().Len(vals, 3)

	for _, v := range gotVals {
		val, ok := vals[v.ConsensusAddress]
		s.Require().True(ok)
		s.Require().Equal(v.ConsensusAddress, val.ConsensusAddress)
		s.Require().Equal(v.VotingPower, val.VotingPower)
		s.Require().EqualValues(v.ConsensusPubkey.Value, val.ConsensusPubkey.Value)
	}
}

// TestValidatorsToValset
func (s *KeeperTestSuite) TestGetValsetFromValidators() {
	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.childChain.GetContext()
	vals := map[string]types.Validator{}

	for i := 0; i < 3; i++ {
		pubKey := ed25519.GenPrivKey().PubKey()
		val, err := types.NewValidator(pubKey, int64(i+1))
		vals[val.ConsensusAddress] = val
		s.Require().NoError(err)
		childKeeper.SetValidatorByConsAddr(ctx, val)
	}

	valset, err := childKeeper.GetValsetFromValidators(ctx)
	s.Require().NoError(err)
	s.Require().NotNil(valset.Validators)
	s.Require().Len(valset.Validators, 3)
	s.Require().Equal(valset.TotalVotingPower(), int64(6))

	for _, v := range valset.Validators {
		consAddr, err := sdk.ConsAddressFromHex(v.Address.String())
		s.Require().NoError(err)
		val, ok := vals[consAddr.String()]
		s.Require().True(ok)
		s.Require().Equal(consAddr.String(), val.ConsensusAddress)
		s.Require().Equal(v.VotingPower, val.VotingPower)
		pubkey, err := val.ConsPubKey()
		s.Require().NoError(err)
		s.Require().EqualValues(v.PubKey.Bytes(), pubkey.Bytes())
	}
}

func (s *KeeperTestSuite) TestApplyChanges() {
	ibctesting.ValidatorsPerChain = 5
	s.SetupTest()

	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.childChain.GetContext()

	// get valset from childchain
	valset := s.childChain.Vals

	// create validator updates
	valUpdates := []abci.ValidatorUpdate{}

	pk1, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	s.Require().NoError(err)
	valUpdates = append(valUpdates, abci.ValidatorUpdate{PubKey: pk1, Power: int64(20)})

	pk2, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	s.Require().NoError(err)
	valUpdates = append(valUpdates, abci.ValidatorUpdate{PubKey: pk2, Power: int64(30)})

	newVals, err := utils.GetNewChanges(valUpdates, *valset)
	s.Require().NoError(err)
	s.Require().NotNil(newVals)
	s.Require().Len(newVals, 2)

	changeSet, err := tmtypes.PB2TM.ValidatorUpdates(valUpdates)
	s.Require().NoError(err)

	// apply valset changes - with removals
	valset.UpdateWithChangeSet(changeSet)

	childKeeper.SetValidatorsFromValset(ctx, *valset)
	s.Require().NoError(err)

	valsUpdated := childKeeper.GetAllValidators(ctx)
	s.Require().Len(valsUpdated, 7)
}
