package keeper_test

import (
	"bytes"
	"errors"
	"sort"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	testkeeper "github.com/cosmos/interchain-security/v5/testutil/keeper"
	providertypes "github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
	"github.com/stretchr/testify/require"
)

// TestConsumerId tests setters and getters of consumer id (i.e., `FetchAndIncrementConsumerId` and `GetConsumerId`)
func TestConsumerId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, found := providerKeeper.GetConsumerId(ctx)
	require.False(t, found)

	consumerId := providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "0", consumerId)
	consumerIdNum, found := providerKeeper.GetConsumerId(ctx)
	require.Equal(t, uint64(1), consumerIdNum)
	require.True(t, found)

	consumerId = providerKeeper.FetchAndIncrementConsumerId(ctx)
	require.Equal(t, "1", consumerId)
	consumerIdNum, found = providerKeeper.GetConsumerId(ctx)
	require.Equal(t, uint64(2), consumerIdNum)
	require.True(t, found)
}

// TestConsumerChainId tests the getter, setter, and deletion of the consumer to chain id methods
func TestConsumerChainId(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.Error(t, err, "failed to retrieve chain id")

	providerKeeper.SetConsumerChainId(ctx, "chainId", "chainId")
	chainId, err := providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.NoError(t, err)
	require.Equal(t, "chainId", chainId)

	// write under a different key
	providerKeeper.SetConsumerChainId(ctx, "consumerId2", "chainId")
	chainId, err = providerKeeper.GetConsumerChainId(ctx, "consumerId2")
	require.NoError(t, err)
	require.Equal(t, "chainId", chainId)

	// assert that overwriting the current key works
	providerKeeper.SetConsumerChainId(ctx, "chainId", "chainId2")
	chainId, err = providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.NoError(t, err)
	require.Equal(t, "chainId2", chainId)

	providerKeeper.DeleteConsumerChainId(ctx, "chainId")
	_, err = providerKeeper.GetConsumerChainId(ctx, "chainId")
	require.Error(t, err, "failed to retrieve chain id")
}

// TestConsumerOwnerAddress tests the getter, setter, and deletion of the consumer to owner address methods
func TestConsumerOwnerAddress(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerOwnerAddress(ctx, "ownerAddress")
	require.Error(t, err, "failed to retrieve owner address")

	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner address")
	ownerAddress, err := providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// write under a different key
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId2", "owner address")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId2")
	require.NoError(t, err)
	require.Equal(t, "owner address", ownerAddress)

	// assert that overwriting the current key works
	providerKeeper.SetConsumerOwnerAddress(ctx, "consumerId", "owner address2")
	ownerAddress, err = providerKeeper.GetConsumerOwnerAddress(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, "owner address2", ownerAddress)

	providerKeeper.DeleteConsumerOwnerAddress(ctx, "consumerId")
	_, err = providerKeeper.GetConsumerChainId(ctx, "consumerId")
	require.Error(t, err, "failed to retrieve owner address")
}

// TestConsumerMetadata tests the getter, setter, and deletion of the consumer id to consumer metadata methods
func TestConsumerMetadata(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.Error(t, err)

	expectedMetadata := providertypes.ConsumerMetadata{
		Name:        "name",
		Description: "description",
		Metadata:    "metadata",
		//ChainId:     "chain_id",
	}
	providerKeeper.SetConsumerMetadata(ctx, "consumerId", expectedMetadata)
	actualMetadata, err := providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	// assert that overwriting the current registration record works
	expectedMetadata = providertypes.ConsumerMetadata{
		Name:        "name 2",
		Description: "description 2",
		Metadata:    "metadata 2",
		//ChainId:     "chain_id2",
	}
	providerKeeper.SetConsumerMetadata(ctx, "consumerId", expectedMetadata)
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedMetadata, actualMetadata)

	providerKeeper.DeleteConsumerMetadata(ctx, "consumerId")
	actualMetadata, err = providerKeeper.GetConsumerMetadata(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerMetadata{}, actualMetadata)
}

// TestConsumerInitializationParameters tests the getter, setter, and deletion of the consumer id to initialization parameters methods
func TestConsumerInitializationParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	_, err := providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.Error(t, err)

	expectedInitializationParameters := providertypes.ConsumerInitializationParameters{
		InitialHeight:                     types.Height{RevisionNumber: 1, RevisionHeight: 2},
		GenesisHash:                       []byte{0, 1},
		BinaryHash:                        []byte{2, 3},
		SpawnTime:                         time.Unix(1, 2).UTC(),
		UnbondingPeriod:                   time.Duration(3456),
		CcvTimeoutPeriod:                  time.Duration(789),
		TransferTimeoutPeriod:             time.Duration(101112),
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction",
		BlocksPerDistributionTransmission: 123,
		HistoricalEntries:                 456,
		DistributionTransmissionChannel:   "distribution_transmission_channel",
	}
	providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", expectedInitializationParameters)
	actualInitializationParameters, err := providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	// assert that overwriting the current initialization record works
	expectedInitializationParameters = providertypes.ConsumerInitializationParameters{
		InitialHeight:                     types.Height{RevisionNumber: 2, RevisionHeight: 3},
		GenesisHash:                       []byte{2, 3},
		BinaryHash:                        []byte{4, 5},
		SpawnTime:                         time.Unix(2, 3).UTC(),
		UnbondingPeriod:                   time.Duration(789),
		CcvTimeoutPeriod:                  time.Duration(101112),
		TransferTimeoutPeriod:             time.Duration(131415),
		ConsumerRedistributionFraction:    "consumer_redistribution_fraction2",
		BlocksPerDistributionTransmission: 456,
		HistoricalEntries:                 789,
		DistributionTransmissionChannel:   "distribution_transmission_channel2",
	}
	providerKeeper.SetConsumerInitializationParameters(ctx, "consumerId", expectedInitializationParameters)
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.NoError(t, err)
	require.Equal(t, expectedInitializationParameters, actualInitializationParameters)

	providerKeeper.DeleteConsumerInitializationParameters(ctx, "consumerId")
	actualInitializationParameters, err = providerKeeper.GetConsumerInitializationParameters(ctx, "consumerId")
	require.Error(t, err)
	require.Equal(t, providertypes.ConsumerInitializationParameters{}, actualInitializationParameters)
}

// TestConsumerPowerShapingParameters tests the getter and setter of the consumer id to power-shaping parameters methods
func TestConsumerPowerShapingParameters(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	consumerId := "consumerId"
	consAddrs := []string{
		"cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
		"cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
		"cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
		"cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
		"cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
		"cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
	}
	providerConsAddr := []providertypes.ProviderConsAddress{}
	for _, addr := range consAddrs {
		ca, _ := sdk.ConsAddressFromBech32(addr)
		providerConsAddr = append(providerConsAddr, providertypes.NewProviderConsAddress(ca))
	}
	sortProviderConsAddr := func(consAddrs []providertypes.ProviderConsAddress) {
		sort.Slice(consAddrs, func(i, j int) bool {
			return bytes.Compare(consAddrs[i].Address, consAddrs[j].Address) < 0
		})
	}

	_, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.Error(t, err)
	require.True(t, errors.Is(err, ccvtypes.ErrStoreKeyNotFound))

	expectedPowerShapingParameters := providertypes.PowerShapingParameters{
		Top_N:              10,
		ValidatorsPowerCap: 34,
		ValidatorSetCap:    10,
		Allowlist:          []string{consAddrs[0], consAddrs[1]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           234,
		AllowInactiveVals:  true,
	}
	expectedAllowlist := []providertypes.ProviderConsAddress{providerConsAddr[0], providerConsAddr[1]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist := []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err := providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))

	// assert that overwriting the current initialization record works
	expectedPowerShapingParameters = providertypes.PowerShapingParameters{
		Top_N:              12,
		ValidatorsPowerCap: 67,
		ValidatorSetCap:    20,
		Allowlist:          []string{consAddrs[4], consAddrs[5]},
		Denylist:           []string{consAddrs[2], consAddrs[3]},
		MinStake:           567,
		AllowInactiveVals:  false,
	}
	expectedAllowlist = []providertypes.ProviderConsAddress{providerConsAddr[4], providerConsAddr[5]}
	sortProviderConsAddr(expectedAllowlist)
	expectedDenylist = []providertypes.ProviderConsAddress{providerConsAddr[2], providerConsAddr[3]}
	sortProviderConsAddr(expectedDenylist)
	err = providerKeeper.SetConsumerPowerShapingParameters(ctx, consumerId, expectedPowerShapingParameters)
	require.NoError(t, err)
	actualPowerShapingParameters, err = providerKeeper.GetConsumerPowerShapingParameters(ctx, consumerId)
	require.NoError(t, err)
	require.Equal(t, expectedPowerShapingParameters, actualPowerShapingParameters)
	require.Equal(t, expectedAllowlist, providerKeeper.GetAllowList(ctx, consumerId))
	require.Equal(t, expectedDenylist, providerKeeper.GetDenyList(ctx, consumerId))
}

// TestConsumerPhase tests the getter, setter, and deletion of the consumer id to phase methods
func TestConsumerPhase(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	phase := providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_UNSPECIFIED, phase)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED)
	phase = providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_INITIALIZED, phase)

	providerKeeper.SetConsumerPhase(ctx, "consumerId", providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED)
	phase = providerKeeper.GetConsumerPhase(ctx, "consumerId")
	require.Equal(t, providertypes.ConsumerPhase_CONSUMER_PHASE_LAUNCHED, phase)
}

// TestOptedInConsumerIds tests the `GetOptedInConsumerIds`, `AppendOptedInConsumerId`, and `RemoveOptedInConsumerId` methods
func TestGetOptedInConsumerIds(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	consumers, err := providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Empty(t, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId1")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1"},
	}, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId2")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId2"},
	}, consumers)

	err = providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, "consumerId3")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId2", "consumerId3"},
	}, consumers)

	// remove all the consumer ids
	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId2")
	require.NoError(t, err)
	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Equal(t, providertypes.ConsumerIds{
		Ids: []string{"consumerId1", "consumerId3"},
	}, consumers)

	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId3")
	require.NoError(t, err)

	err = providerKeeper.RemoveOptedInConsumerId(ctx, providerAddr, "consumerId1")
	require.NoError(t, err)

	consumers, err = providerKeeper.GetOptedInConsumerIds(ctx, providerAddr)
	require.NoError(t, err)
	require.Empty(t, consumers)
}

func TestIsValidatorOptedInToChain(t *testing.T) {
	providerKeeper, ctx, ctrl, _ := testkeeper.GetProviderKeeperAndCtx(t, testkeeper.NewInMemKeeperParams(t))
	defer ctrl.Finish()

	chainId := "chainId"
	providerAddr := providertypes.NewProviderConsAddress([]byte("providerAddr"))
	_, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.False(t, found)

	expectedConsumerId := "consumerId"
	providerKeeper.SetConsumerChainId(ctx, expectedConsumerId, chainId)
	providerKeeper.SetOptedIn(ctx, expectedConsumerId, providerAddr)
	providerKeeper.AppendOptedInConsumerId(ctx, providerAddr, expectedConsumerId)
	actualConsumerId, found := providerKeeper.IsValidatorOptedInToChainId(ctx, providerAddr, chainId)
	require.True(t, found)
	require.Equal(t, expectedConsumerId, actualConsumerId)
}
