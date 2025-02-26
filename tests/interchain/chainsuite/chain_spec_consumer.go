package chainsuite

import (
	"context"
	"errors"
	"strconv"
	"time"

	providertypes "github.com/cosmos/interchain-security/v7/x/ccv/provider/types"
	"github.com/strangelove-ventures/interchaintest/v8"
	"github.com/strangelove-ventures/interchaintest/v8/chain/cosmos"
	"github.com/strangelove-ventures/interchaintest/v8/ibc"
	"github.com/strangelove-ventures/interchaintest/v8/testutil"
)

func GetConsumerSpec(ctx context.Context, providerChain *Chain, proposalMsg *providertypes.MsgCreateConsumer) *interchaintest.ChainSpec {
	fullNodes := FullNodeCount
	validators := 1

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
					Repository: ConsumerImageName(),
					Version:    ConsumerImageVersion(),
					UIDGID:     "1025:1025",
				},
			},
			ConfigFileOverrides: map[string]any{
				"config/config.toml": DefaultConfigToml(),
			},
			PreGenesis: func(consumer ibc.Chain) error {
				// note that if Top_N>0 proposal will be rejected. If there is a need to support this in the future,
				// it is necessary to first submit a create message with Top_N=0 and then an update message with Top_N>0
				consumerID, err := providerChain.CreateConsumer(ctx, proposalMsg, ValidatorMoniker)
				if err != nil {
					return err
				}

				for index := 0; index < len(providerChain.Validators); index++ {
					if err := providerChain.OptIn(ctx, consumerID, index); err != nil {
						return err
					}
				}

				// speed up chain launch by submitting update msg with current time as a spawn time
				proposalMsg.InitializationParameters.SpawnTime = time.Now()
				updateMsg := &providertypes.MsgUpdateConsumer{
					ConsumerId:               consumerID,
					Owner:                    providerChain.ValidatorWallets[0].Address,
					NewOwnerAddress:          providerChain.ValidatorWallets[0].Address,
					InitializationParameters: proposalMsg.InitializationParameters,
					PowerShapingParameters:   proposalMsg.PowerShapingParameters,
				}
				if err := providerChain.UpdateConsumer(ctx, updateMsg, ValidatorMoniker); err != nil {
					return err
				}

				if err := testutil.WaitForBlocks(ctx, 2, providerChain); err != nil {
					return err
				}

				consumerChain, err := providerChain.GetConsumerChainByChainId(ctx, proposalMsg.ChainId)
				if err != nil {
					return err
				}

				if consumerChain.Phase != providertypes.CONSUMER_PHASE_LAUNCHED.String() {
					return errors.New("consumer chain is not launched")
				}

				return nil
			},
			Bech32Prefix:         Bech32PrefixConsumer,
			ModifyGenesisAmounts: DefaultGenesisAmounts(Stake),
			ModifyGenesis:        cosmos.ModifyGenesis(consumerModifiedGenesis()),
			InterchainSecurityConfig: ibc.ICSConfig{
				ConsumerCopyProviderKey: func(int) bool { return true },
			},
		},
	}
}

func consumerModifiedGenesis() []cosmos.GenesisKV {
	return []cosmos.GenesisKV{
		cosmos.NewGenesisKV("app_state.slashing.params.signed_blocks_window", strconv.Itoa(SlashingWindowConsumer)),
		cosmos.NewGenesisKV("consensus.params.block.max_gas", "50000000"),
		cosmos.NewGenesisKV("app_state.ccvconsumer.params.soft_opt_out_threshold", "0.0"),
		cosmos.NewGenesisKV("app_state.ccvconsumer.params.blocks_per_distribution_transmission", BlocksPerDistribution),
		cosmos.NewGenesisKV("app_state.ccvconsumer.params.reward_denoms", []string{Stake}),
	}
}
