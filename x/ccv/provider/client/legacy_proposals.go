package client

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"

	"github.com/cosmos/cosmos-sdk/client"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

type ConsumerAdditionProposalJSON struct {
	Title         string             `json:"title"`
	Summary       string             `json:"summary"`
	ChainId       string             `json:"chain_id"`
	InitialHeight clienttypes.Height `json:"initial_height"`
	GenesisHash   []byte             `json:"genesis_hash"`
	BinaryHash    []byte             `json:"binary_hash"`
	SpawnTime     time.Time          `json:"spawn_time"`

	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	HistoricalEntries                 int64         `json:"historical_entries"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`

	Deposit string `json:"deposit"`

	TopN               uint32   `json:"top_N"`
	ValidatorsPowerCap uint32   `json:"validators_power_cap"`
	ValidatorSetCap    uint32   `json:"validator_set_cap"`
	Allowlist          []string `json:"allowlist"`
	Denylist           []string `json:"denylist"`
}

type ConsumerAdditionProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`

	Title         string             `json:"title"`
	Description   string             `json:"description"`
	ChainId       string             `json:"chainId"`
	InitialHeight clienttypes.Height `json:"initialHeight"`
	GenesisHash   []byte             `json:"genesisHash"`
	BinaryHash    []byte             `json:"binaryHash"`
	SpawnTime     time.Time          `json:"spawnTime"`

	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	HistoricalEntries                 int64         `json:"historical_entries"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`

	Deposit sdk.Coins `json:"deposit"`
}

func ParseConsumerAdditionProposalJSON(proposalFile string) (ConsumerAdditionProposalJSON, error) {
	proposal := ConsumerAdditionProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}

type ConsumerRemovalProposalJSON struct {
	Title    string    `json:"title"`
	Summary  string    `json:"summary"`
	ChainId  string    `json:"chain_id"`
	StopTime time.Time `json:"stop_time"`
	Deposit  string    `json:"deposit"`
}

type ConsumerRemovalProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`

	Title       string `json:"title"`
	Description string `json:"description"`
	ChainId     string `json:"chainId"`

	StopTime time.Time `json:"stopTime"`
	Deposit  sdk.Coins `json:"deposit"`
}

func ParseConsumerRemovalProposalJSON(proposalFile string) (ConsumerRemovalProposalJSON, error) {
	proposal := ConsumerRemovalProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}

type ChangeRewardDenomsProposalJSON struct {
	Summary string `json:"summary"`
	types.ChangeRewardDenomsProposal
	Deposit string `json:"deposit"`
}

type ChangeRewardDenomsProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`
	types.ChangeRewardDenomsProposal
	Deposit sdk.Coins `json:"deposit"`
}

func ParseChangeRewardDenomsProposalJSON(proposalFile string) (ChangeRewardDenomsProposalJSON, error) {
	proposal := ChangeRewardDenomsProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}
	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}
	return proposal, nil
}

func CheckPropUnbondingPeriod(clientCtx client.Context, propUnbondingPeriod time.Duration) {
	queryClient := stakingtypes.NewQueryClient(clientCtx)

	res, err := queryClient.Params(context.Background(), &stakingtypes.QueryParamsRequest{})
	if err != nil {
		fmt.Println(err.Error())
		return
	}

	providerUnbondingTime := res.Params.UnbondingTime

	if providerUnbondingTime < propUnbondingPeriod {
		fmt.Fprintf(
			os.Stderr,
			`consumer unbonding period is advised to be smaller than provider unbonding period, but is longer.
This is not a security risk, but will effectively lengthen the unbonding period on the provider.
consumer unbonding: %s
provider unbonding: %s`,
			propUnbondingPeriod,
			providerUnbondingTime)
	}
}

type ConsumerModificationProposalJSON struct {
	Title   string `json:"title"`
	Summary string `json:"summary"`
	ChainId string `json:"chain_id"`

	TopN               uint32   `json:"top_N"`
	ValidatorsPowerCap uint32   `json:"validators_power_cap"`
	ValidatorSetCap    uint32   `json:"validator_set_cap"`
	Allowlist          []string `json:"allowlist"`
	Denylist           []string `json:"denylist"`

	Deposit string `json:"deposit"`
}

func ParseConsumerModificationProposalJSON(proposalFile string) (ConsumerModificationProposalJSON, error) {
	proposal := ConsumerModificationProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}
