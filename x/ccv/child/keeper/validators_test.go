package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	ibctesting "github.com/cosmos/ibc-go/testing"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TestValidatorByConsAddr
func (s *KeeperTestSuite) TestValidatorByConsAddr() {
	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.ctx

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
	ctx := s.ctx

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
	ctx := s.ctx
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

func (s KeeperTestSuite) TestInitGenesis() {
	ibctesting.ValidatorsPerChain = 2
	s.SetupTest()

	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.ctx

	// check that child genesis state meaning
	// the parent validators are sotre into child CCV module
	tmVals := s.parentChain.Vals.Validators
	s.Require().Len(tmVals, 2)
	vals := childKeeper.GetAllValidators(ctx)
	s.Require().Len(vals, 2)

	for i, v := range vals {
		got, err := types.FromTmValidator(*tmVals[i])
		s.Require().NoError(err)
		s.Require().True(v.GetConsensusPubkey().Equal(got.GetConsensusPubkey()))
		s.Require().Equal(v.VotingPower, got.VotingPower)
		s.Require().Equal(v.ConsensusAddress, got.ConsensusAddress)
	}
}

func (s KeeperTestSuite) TestApplyValidatorChanges() {
	ibctesting.ValidatorsPerChain = 3
	s.SetupTest()

	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.ctx

	// expect an error if the change contains
	// a new validator with voting power 0
	pk, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	s.Require().NoError(err)
	_, err = childKeeper.ApplyValidatorChanges(ctx, []abci.ValidatorUpdate{{PubKey: pk, Power: 0}})
	s.Require().Error(err)

	vals := childKeeper.GetAllValidators(ctx)

	// create 4 changes:
	// 2 new bondings, 1 delegation, 1 jailing
	changes := []abci.ValidatorUpdate{}
	expVotingPower := int64(0)

	for i, val := range vals {
		val.VotingPower = int64(i * 10)
		change, err := val.ToChange()
		s.Require().NoError(err)
		changes = append(changes, change)
		expVotingPower += val.VotingPower
	}

	// Append three new bonded validators
	for i := 1; i < 4; i++ {
		pk, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
		s.Require().NoError(err)
		changes = append(changes, abci.ValidatorUpdate{PubKey: pk, Power: int64(i * 10)})
		expVotingPower += int64(i * 10)
	}

	// apply changes
	newValidators, err := childKeeper.ApplyValidatorChanges(ctx, changes)
	s.Require().NoError(err)
	s.Require().Len(newValidators, 3)

	// check that the validator changes
	valset, err := childKeeper.GetValsetFromValidators(ctx)
	s.Require().NoError(err)
	s.Require().Len(valset.Validators, 5)
	s.Require().Equal(valset.TotalVotingPower(), expVotingPower)
}

func (s KeeperTestSuite) TestHandleNewBondings() {
	ibctesting.ValidatorsPerChain = 3
	s.SetupTest()

	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.ctx
	vals := childKeeper.GetAllValidators(ctx)

	addrs := []sdk.ConsAddress{}

	for _, val := range vals {

		consAddr, err := val.GetConsAddr()
		s.Require().NoError(err)
		addrs = append(addrs, consAddr)
	}

	for _, addr := range addrs {
		childKeeper.PenaltySentToProvider(ctx, addr)
	}

	childKeeper.HandleNewBondings(ctx, addrs)

	for _, addr := range addrs {
		s.Require().False(childKeeper.IsPenaltySentToProvider(ctx, addr))
	}
}
