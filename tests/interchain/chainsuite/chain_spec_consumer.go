package chainsuite

import (
	"context"
	"strconv"
	"time"

	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	providertypes "github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"github.com/strangelove-ventures/interchaintest/v8/testutil"
)

func GetConsumerSpec(ctx context.Context, providerChain *Chain, proposalMsg *providertypes.MsgCreateConsumer, optInValIndexes []int) *interchaintest.ChainSpec {
	fullNodes := FullNodeCount
	validators := ValidatorCount

	return &interchaintest.ChainSpec{
		ChainName:     ConsumerChainID,
		NumFullNodes:  &fullNodes,
		NumValidators: &validators,
		ChainConfig: ibc.ChainConfig{
			ChainID:        ConsumerChainID,
			Bin:            ConsumerBin,
			Denom:          Stake,
			Type:           CosmosChainType,
			GasPrices:      GasPrices + Stake,
			GasAdjustment:  2.0,
			TrustingPeriod: "336h",
			CoinType:       "118",
			Images: []ibc.DockerImage{
				{
					Repository: ImageName,
					Version:    ImageVersion,
					UIDGID:     "1025:1025",
				},
			},
			ConfigFileOverrides: map[string]any{
				"config/config.toml": DefaultConfigToml(),
			},
			PreGenesis: func(consumer ibc.Chain) error {
				// submit proposal and wait for the spawn time
				if err := providerChain.ExecuteProposalMsg(ctx, proposalMsg, GovModuleAddress, ConsumerChainID, cosmos.ProposalVoteYes, govv1.StatusPassed, false); err != nil {
					return err
				}
				consumerChain, err := providerChain.GetConsumerChainByChainId(ctx, proposalMsg.ChainId)
				if err != nil {
					return err
				}

				if len(optInValIndexes) == 0 {
					//todo: top n chain
				} else {
					for _, index := range optInValIndexes {
						if err := providerChain.OptIn(ctx, consumerChain.ConsumerID, index); err != nil {
							return err
						}
					}
				}

				time.Sleep(time.Until(proposalMsg.InitializationParameters.SpawnTime))
				if err := testutil.WaitForBlocks(ctx, 2, providerChain); err != nil {
					return err
				}

				return nil
			},
			Bech32Prefix:         Bech32Prefix,
			ModifyGenesisAmounts: DefaultGenesisAmounts(Stake),
			ModifyGenesis:        cosmos.ModifyGenesis(consumerModifiedGenesis()),
			InterchainSecurityConfig: ibc.ICSConfig{
				ConsumerCopyProviderKey: func(int) bool { return true },
				//ProviderVerOverride:     "v4.1.0",
			},
		},
	}
}

func consumerModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.slashing.params.signed_blocks_window", strconv.Itoa(SlashingWindowConsumer)),
		cosmos.NewGenesisKV("consensus.params.block.max_gas", "50000000"),
		cosmos.NewGenesisKV("app_state.ccvconsumer.params.soft_opt_out_threshold", "0.0"),
		cosmos.NewGenesisKV("app_state.globalfee.params.minimum_gas_prices", []interface{}{
			map[string]interface{}{
				"amount": GasPrices,
				"denom":  Stake,
			},
		}),
		cosmos.NewGenesisKV("app_state.feemarket.params.min_base_gas_price", GasPrices),
		cosmos.NewGenesisKV("app_state.feemarket.state.base_gas_price", GasPrices),
		cosmos.NewGenesisKV("app_state.feemarket.params.fee_denom", Stake),
	}
}
