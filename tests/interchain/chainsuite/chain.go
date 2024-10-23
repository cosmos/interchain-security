package chainsuite

import (
	"context"
	"encoding/json"
	"fmt"
	"strconv"
	"sync"

	sdkmath "cosmossdk.io/math"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"golang.org/x/sync/errgroup"
)

// This moniker is hardcoded into interchaintest
const validatorMoniker = "validator"

type Chain struct {
	*cosmos.CosmosChain
	ValidatorWallets []ValidatorWallet
	RelayerWallet    ibc.Wallet
}

type ValidatorWallet struct {
	Moniker        string
	Address        string
	ValoperAddress string
}

func chainFromCosmosChain(cosmos *cosmos.CosmosChain, relayerWallet ibc.Wallet) (*Chain, error) {
	c := &Chain{CosmosChain: cosmos}
	wallets, err := getValidatorWallets(context.Background(), c)
	if err != nil {
		return nil, err
	}
	c.ValidatorWallets = wallets
	c.RelayerWallet = relayerWallet
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

	chain, err := chainFromCosmosChain(cosmosChain, relayerWallet)
	if err != nil {
		return nil, err
	}
	return chain, nil
}

func getValidatorWallets(ctx context.Context, chain *Chain) ([]ValidatorWallet, error) {
	wallets := make([]ValidatorWallet, len(chain.Validators))
	lock := new(sync.Mutex)
	eg := new(errgroup.Group)
	for i := 0; i < len(chain.Validators); i++ {
		i := i
		eg.Go(func() error {
			// This moniker is hardcoded into the chain's genesis process.
			moniker := validatorMoniker
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

	propTx, err := c.SubmitProposal(ctx, validatorMoniker, prop)
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

func (c *Chain) OptIn(ctx context.Context, consumerID string, valIndex int) error {
	_, err := c.Validators[valIndex].ExecTx(ctx, validatorMoniker, "provider", "opt-in", consumerID)
	return err
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
