package chainsuite

import (
	"context"
	"encoding/json"
	"fmt"
	"path"
	"strconv"
	"strings"
	"sync"

	sdkmath "cosmossdk.io/math"
	abci "github.com/cometbft/cometbft/abci/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"golang.org/x/sync/errgroup"
)

// This moniker is hardcoded into interchaintest
const ValidatorMoniker = "validator"
const TestMonikerPrefix = "testAccount"

type Chain struct {
	*cosmos.CosmosChain
	ValidatorWallets []ValidatorWallet
	RelayerWallet    ibc.Wallet
	TestWallets      []ibc.Wallet
}

type ValidatorWallet struct {
	Moniker        string
	Address        string
	ValoperAddress string
}

func chainFromCosmosChain(cosmos *cosmos.CosmosChain, relayerWallet ibc.Wallet, testWallets []ibc.Wallet) (*Chain, error) {
	c := &Chain{CosmosChain: cosmos}
	wallets, err := getValidatorWallets(context.Background(), c)
	if err != nil {
		return nil, err
	}
	c.ValidatorWallets = wallets
	c.RelayerWallet = relayerWallet
	c.TestWallets = testWallets
	return c, nil
}

// CreateProviderChain creates a single new chain with the given version and returns the chain object.
func CreateProviderChain(ctx context.Context, testName interchaintest.TestName, spec *interchaintest.ChainSpec) (*Chain, error) {
	cf := interchaintest.NewBuiltinChainFactory(
		GetLogger(ctx),
		[]*interchaintest.ChainSpec{spec},
	)

	chains, err := cf.Chains(testName.Name())
	if err != nil {
		return nil, err
	}
	cosmosChain := chains[0].(*cosmos.CosmosChain)

	// build relayer wallet
	relayerWallet, err := cosmosChain.BuildRelayerWallet(ctx, "relayer-"+cosmosChain.Config().ChainID)
	if err != nil {
		return nil, err
	}

	ic := interchaintest.NewInterchain().AddChain(cosmosChain, ibc.WalletAmount{
		Address: relayerWallet.FormattedAddress(),
		Denom:   cosmosChain.Config().Denom,
		Amount:  sdkmath.NewInt(TotalValidatorFunds),
	})

	dockerClient, dockerNetwork := GetDockerContext(ctx)

	if err := ic.Build(ctx, GetRelayerExecReporter(ctx), interchaintest.InterchainBuildOptions{
		Client:    dockerClient,
		NetworkID: dockerNetwork,
		TestName:  testName.Name(),
	}); err != nil {
		return nil, err
	}

	// build test wallets
	testWallets, err := setupTestWallets(ctx, cosmosChain, TestWalletsNumber)
	if err != nil {
		return nil, err
	}
	chain, err := chainFromCosmosChain(cosmosChain, relayerWallet, testWallets)
	if err != nil {
		return nil, err
	}

	return chain, nil
}

func setupTestWallets(ctx context.Context, cosmosChain *cosmos.CosmosChain, walletCount int) ([]ibc.Wallet, error) {
	wallets := make([]ibc.Wallet, walletCount)
	eg := new(errgroup.Group)
	for i := 0; i < walletCount; i++ {
		keyName := TestMonikerPrefix + strconv.Itoa(i)
		wallet, err := cosmosChain.BuildWallet(ctx, keyName, "")
		if err != nil {
			return nil, err
		}
		wallets[i] = wallet
		eg.Go(func() error {
			return cosmosChain.SendFunds(ctx, interchaintest.FaucetAccountKeyName, ibc.WalletAmount{
				Amount:  sdkmath.NewInt(int64(ValidatorFunds)),
				Denom:   cosmosChain.Config().Denom,
				Address: wallet.FormattedAddress(),
			})
		})
	}
	err := eg.Wait()
	if err != nil {
		return nil, err
	}

	return wallets, nil
}

func getValidatorWallets(ctx context.Context, chain *Chain) ([]ValidatorWallet, error) {
	wallets := make([]ValidatorWallet, len(chain.Validators))
	lock := new(sync.Mutex)
	eg := new(errgroup.Group)
	for i := 0; i < len(chain.Validators); i++ {
		i := i
		eg.Go(func() error {
			// This moniker is hardcoded into the chain's genesis process.
			moniker := ValidatorMoniker
			address, err := chain.Validators[i].KeyBech32(ctx, moniker, "acc")
			if err != nil {
				return err
			}
			valoperAddress, err := chain.Validators[i].KeyBech32(ctx, moniker, "val")
			if err != nil {
				return err
			}
			lock.Lock()
			defer lock.Unlock()
			wallets[i] = ValidatorWallet{
				Moniker:        moniker,
				Address:        address,
				ValoperAddress: valoperAddress,
			}
			return nil
		})
	}
	if err := eg.Wait(); err != nil {
		return nil, err
	}
	return wallets, nil
}

func (c *Chain) WaitForProposalStatus(ctx context.Context, proposalID string, status govv1.ProposalStatus) error {
	propID, err := strconv.ParseInt(proposalID, 10, 64)
	if err != nil {
		return err
	}
	chainHeight, err := c.Height(ctx)
	if err != nil {
		return err
	}
	maxHeight := chainHeight + UpgradeDelta
	_, err = cosmos.PollForProposalStatusV1(ctx, c.CosmosChain, chainHeight, maxHeight, uint64(propID), status)
	return err
}

func (c *Chain) VoteForProposal(ctx context.Context, proposalID string, vote string) error {
	propID, err := strconv.ParseInt(proposalID, 10, 64)
	if err != nil {
		return err
	}
	err = c.VoteOnProposalAllValidators(ctx, uint64(propID), vote)
	if err != nil {
		return err
	}

	return nil
}

func (c *Chain) SubmitAndVoteForProposal(ctx context.Context, prop cosmos.TxProposalv1, vote string) (string, error) {

	propTx, err := c.SubmitProposal(ctx, ValidatorMoniker, prop)
	if err != nil {
		return "", err
	}

	if err := c.WaitForProposalStatus(ctx, propTx.ProposalID, govv1.StatusVotingPeriod); err != nil {
		return "", err
	}

	if err := c.VoteForProposal(ctx, propTx.ProposalID, vote); err != nil {
		return "", err
	}

	return propTx.ProposalID, nil
}

// builds proposal message, submits, votes and wait for proposal expected status
func (c *Chain) ExecuteProposalMsg(ctx context.Context, proposalMsg cosmos.ProtoMessage, proposer string, chainName string, vote string, expectedStatus govv1.ProposalStatus, expedited bool) error {
	proposal, err := c.BuildProposal([]cosmos.ProtoMessage{proposalMsg}, chainName, "summary", "", GovMinDepositString, proposer, false)
	if err != nil {
		return err
	}

	// submit and vote for the proposal
	proposalId, err := c.SubmitAndVoteForProposal(ctx, proposal, vote)
	if err != nil {
		return err
	}

	if err = c.WaitForProposalStatus(ctx, proposalId, expectedStatus); err != nil {
		return err
	}

	return nil
}

func (c *Chain) CreateConsumer(ctx context.Context, msg *providertypes.MsgCreateConsumer, keyName string) (string, error) {
	content, err := json.Marshal(msg)
	if err != nil {
		return "", err
	}
	jsonFile := "create-consumer.json"
	if err = c.GetNode().WriteFile(ctx, content, jsonFile); err != nil {
		return "", err
	}

	filePath := path.Join(c.GetNode().HomeDir(), jsonFile)
	txHash, err := c.GetNode().ExecTx(ctx, keyName, "provider", "create-consumer", filePath)
	if err != nil {
		return "", err
	}

	response, err := c.GetNode().TxHashToResponse(ctx, txHash)
	if err != nil {
		return "", err
	}

	consumerId, found := getEvtAttribute(response.Events, providertypes.EventTypeCreateConsumer, providertypes.AttributeConsumerId)
	if !found {
		return "", fmt.Errorf("consumer id is not found")
	}

	return consumerId, err
}

func (c *Chain) UpdateConsumer(ctx context.Context, msg *providertypes.MsgUpdateConsumer, ownerKeyName string) error {
	content, err := json.Marshal(msg)
	if err != nil {
		return err
	}
	jsonFile := "update-consumer.json"
	if err = c.GetNode().WriteFile(ctx, content, jsonFile); err != nil {
		return err
	}

	filePath := path.Join(c.GetNode().HomeDir(), jsonFile)

	_, err = c.GetNode().ExecTx(ctx, ownerKeyName, "provider", "update-consumer", filePath)
	if err != nil {
		return err
	}

	return err
}

func (c *Chain) RemoveConsumer(ctx context.Context, consumerId string, keyName string) error {
	_, err := c.GetNode().ExecTx(ctx, keyName, "provider", "remove-consumer", consumerId)
	return err
}

func (c *Chain) OptIn(ctx context.Context, consumerID string, valIndex int) error {
	_, err := c.Validators[valIndex].ExecTx(ctx, ValidatorMoniker, "provider", "opt-in", consumerID)
	return err
}

func (c *Chain) OptOut(ctx context.Context, consumerID string, valIndex int) error {
	_, err := c.Validators[valIndex].ExecTx(ctx, ValidatorMoniker, "provider", "opt-out", consumerID)
	return err
}

func (c *Chain) AssignKey(ctx context.Context, consumerID string, valIndex int, consensusPubKey string) error {
	_, err := c.Validators[valIndex].ExecTx(ctx, ValidatorMoniker, "provider", "assign-consensus-key", consumerID, consensusPubKey)
	return err
}

func (c *Chain) ValidatorConsumerAddress(ctx context.Context, consumerID string, providerConsensusAddress string) (ValidatorConsumerAddressResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "validator-consumer-key", consumerID, providerConsensusAddress,
	)
	if err != nil {
		return ValidatorConsumerAddressResponse{}, err
	}

	var queryResponse ValidatorConsumerAddressResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return ValidatorConsumerAddressResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) ValidatorProviderAddress(ctx context.Context, consumerID string, consumerConsensusAddress string) (ValidatorProviderAddressResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "validator-provider-key", consumerID, consumerConsensusAddress,
	)
	if err != nil {
		return ValidatorProviderAddressResponse{}, err
	}

	var queryResponse ValidatorProviderAddressResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return ValidatorProviderAddressResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) ListConsumerChains(ctx context.Context) (ListConsumerChainsResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "list-consumer-chains",
	)
	if err != nil {
		return ListConsumerChainsResponse{}, err
	}

	var queryResponse ListConsumerChainsResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return ListConsumerChainsResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) GetConsumerChain(ctx context.Context, consumerId string) (ConsumerResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "consumer-chain", consumerId,
	)
	if err != nil {
		return ConsumerResponse{}, err
	}

	var queryResponse ConsumerResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return ConsumerResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) GetConsumerGenesis(ctx context.Context, consumerId string) (ConsumerGenesisResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "consumer-genesis", consumerId,
	)
	if err != nil {
		return ConsumerGenesisResponse{}, err
	}

	var queryResponse ConsumerGenesisResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return ConsumerGenesisResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) GetConsumerChainByChainId(ctx context.Context, chainId string) (ConsumerChain, error) {
	chains, err := c.ListConsumerChains(ctx)
	if err != nil {
		return ConsumerChain{}, err
	}

	for _, chain := range chains.Chains {
		if chain.ChainID == chainId {
			return chain, nil
		}
	}
	return ConsumerChain{}, fmt.Errorf("chain not found")
}

func (c *Chain) GetOptInValidators(ctx context.Context, consumerId string) (OptInValidatorsResponse, error) {
	queryRes, _, err := c.GetNode().ExecQuery(
		ctx,
		"provider", "consumer-opted-in-validators", consumerId,
	)
	if err != nil {
		return OptInValidatorsResponse{}, err
	}

	var queryResponse OptInValidatorsResponse
	err = json.Unmarshal([]byte(queryRes), &queryResponse)
	if err != nil {
		return OptInValidatorsResponse{}, err
	}

	return queryResponse, nil
}

func (c *Chain) GetValidatorConsAddress(ctx context.Context, validatorIndex int) (string, error) {
	queryRes, _, err := c.Validators[validatorIndex].ExecBin(
		ctx,
		"comet", "show-address",
	)
	if err != nil {
		return "", err
	}

	address := strings.TrimSpace(string(queryRes))

	return address, nil
}

func (c *Chain) GetValidatorKey(ctx context.Context, validatorIndex int) (string, error) {
	queryRes, _, err := c.Validators[validatorIndex].ExecBin(
		ctx,
		"comet", "show-validator",
	)
	if err != nil {
		return "", err
	}

	address := strings.TrimSpace(string(queryRes))

	return address, nil
}

func getEvtAttribute(events []abci.Event, evtType string, key string) (string, bool) {
	for _, evt := range events {
		if evt.GetType() == evtType {
			for _, attr := range evt.Attributes {
				if attr.Key == key {
					return attr.Value, true
				}
			}
		}
	}

	return "", false
}
