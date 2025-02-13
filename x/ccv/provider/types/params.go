package types

import (
	"fmt"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v9/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v9/modules/light-clients/07-tendermint"

	"cosmossdk.io/math"

	sdk "github.com/cosmos/cosmos-sdk/types"
	paramtypes "github.com/cosmos/cosmos-sdk/x/params/types"

	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

const (
	// DefaultMaxClockDrift defines how much new (untrusted) header's Time can drift into the future.
	// This default is only used in the default template client param.
	DefaultMaxClockDrift = 10 * time.Second

	// DefaultTrustingPeriodFraction is the default fraction used to compute TrustingPeriod
	// as UnbondingPeriod * TrustingPeriodFraction
	DefaultTrustingPeriodFraction = "0.66"

	// DefaultSlashMeterReplenishPeriod defines the default period for which the slash gas meter is replenished
	DefaultSlashMeterReplenishPeriod = time.Hour

	// DefaultSlashMeterReplenishFraction defines the default fraction of total voting power
	// that is replenished to the slash meter every replenish period. This param also serves as a maximum
	// fraction of total voting power that the slash meter can hold.
	DefaultSlashMeterReplenishFraction = "0.05"

	// DefaultBlocksPerEpoch defines the default blocks that constitute an epoch. Assuming we need 6 seconds per block,
	// an epoch corresponds to 1 hour (6 * 600 = 3600 seconds).
	// forcing int64 as the Params KeyTable expects an int64 and not int.
	DefaultBlocksPerEpoch = int64(600)

	// DefaultNumberOfEpochsToStartReceivingRewards defines the default minimum number of epochs required by a validator to validate
	// during so that the validator can start receiving rewards. This would mean that a validator has to be a consumer validator for at least
	// `DefaultNumberOfEpochsToStartReceivingRewards * DefaultBlocksPerEpoch` on a consumer chain to start receiving rewards from the chain.
	// Note that after a validator starts receiving rewards, the validator would keep receiving rewards every time the
	// consumer chain sends an IBC transfer over to the provider. This value only sets a constraint on when a validator
	// can first start receiving rewards to avoid cases where a validator just opts in to receive rewards and then opts out
	// immediately afterward.
	// Current default values for blocks per epoch corresponds to about 1 hour, so with 24 being the
	// minimum amount of epochs, this would imply that a validator has to validate at least for 1 day to receive rewards.
	DefaultNumberOfEpochsToStartReceivingRewards = int64(24)

	// DefaultMaxProviderConsensusValidators is the default maximum number of validators that will
	// be passed on from the staking module to the consensus engine on the provider.
	DefaultMaxProviderConsensusValidators = 180
)

// Reflection based keys for params subspace
// Legacy: usage of x/params for parameters is deprecated.
// Use x/ccv/provider/keeper/params instead
// [DEPRECATED]
var (
	KeyTemplateClient                        = []byte("TemplateClient")
	KeyTrustingPeriodFraction                = []byte("TrustingPeriodFraction")
	KeySlashMeterReplenishPeriod             = []byte("SlashMeterReplenishPeriod")
	KeySlashMeterReplenishFraction           = []byte("SlashMeterReplenishFraction")
	KeyConsumerRewardDenomRegistrationFee    = []byte("ConsumerRewardDenomRegistrationFee")
	KeyBlocksPerEpoch                        = []byte("BlocksPerEpoch")
	KeyNumberOfEpochsToStartReceivingRewards = []byte("NumberOfEpochsToStartReceivingRewards")
	KeyMaxProviderConsensusValidators        = []byte("MaxProviderConsensusValidators")
)

// ParamKeyTable returns a key table with the necessary registered provider params
func ParamKeyTable() paramtypes.KeyTable {
	return paramtypes.NewKeyTable().RegisterParamSet(&Params{})
}

// NewParams creates new provider parameters with provided arguments
func NewParams(
	cs *ibctmtypes.ClientState,
	trustingPeriodFraction string,
	ccvTimeoutPeriod time.Duration,
	slashMeterReplenishPeriod time.Duration,
	slashMeterReplenishFraction string,
	consumerRewardDenomRegistrationFee sdk.Coin,
	blocksPerEpoch int64,
	numberOfEpochsToStartReceivingRewards int64,
	maxProviderConsensusValidators int64,
) Params {
	return Params{
		TemplateClient:                        cs,
		TrustingPeriodFraction:                trustingPeriodFraction,
		CcvTimeoutPeriod:                      ccvTimeoutPeriod,
		SlashMeterReplenishPeriod:             slashMeterReplenishPeriod,
		SlashMeterReplenishFraction:           slashMeterReplenishFraction,
		ConsumerRewardDenomRegistrationFee:    consumerRewardDenomRegistrationFee,
		BlocksPerEpoch:                        blocksPerEpoch,
		NumberOfEpochsToStartReceivingRewards: numberOfEpochsToStartReceivingRewards,
		MaxProviderConsensusValidators:        maxProviderConsensusValidators,
	}
}

// DefaultTemplateClient is the default template client
func DefaultTemplateClient() *ibctmtypes.ClientState {
	return ibctmtypes.NewClientState(
		"", // chainID
		ibctmtypes.DefaultTrustLevel,
		0, // trusting period
		0, // unbonding period
		DefaultMaxClockDrift,
		clienttypes.Height{}, // latest(initial) height
		commitmenttypes.GetSDKSpecs(),
		[]string{"upgrade", "upgradedIBCState"},
	)
}

// DefaultParams is the default params for the provider module
func DefaultParams() Params {
	// create default client state with chainID, trusting period, unbonding period, and initial height zeroed out.
	// these fields will be populated during proposal handler.
	return NewParams(
		DefaultTemplateClient(),
		DefaultTrustingPeriodFraction,
		ccvtypes.DefaultCCVTimeoutPeriod,
		DefaultSlashMeterReplenishPeriod,
		DefaultSlashMeterReplenishFraction,
		// Defining this inline because it's not possible to define a constant of type sdk.Coin.
		// Following the pattern from cosmos-sdk/staking/types/params.go
		sdk.Coin{
			Denom:  sdk.DefaultBondDenom,
			Amount: math.NewInt(10000000),
		},
		DefaultBlocksPerEpoch,
		DefaultNumberOfEpochsToStartReceivingRewards,
		DefaultMaxProviderConsensusValidators,
	)
}

// Validate all ccv-provider module parameters
func (p Params) Validate() error {
	if p.TemplateClient == nil {
		return fmt.Errorf("template client is nil")
	}
	if err := ValidateTemplateClient(*p.TemplateClient); err != nil {
		return err
	}
	if err := ccvtypes.ValidateStringFractionNonZero(p.TrustingPeriodFraction); err != nil {
		return fmt.Errorf("trusting period fraction is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.CcvTimeoutPeriod); err != nil {
		return fmt.Errorf("ccv timeout period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateDuration(p.SlashMeterReplenishPeriod); err != nil {
		return fmt.Errorf("slash meter replenish period is invalid: %s", err)
	}
	if err := ccvtypes.ValidateStringFractionNonZero(p.SlashMeterReplenishFraction); err != nil {
		return fmt.Errorf("slash meter replenish fraction is invalid: %s", err)
	}
	if err := ValidateCoin(p.ConsumerRewardDenomRegistrationFee); err != nil {
		return fmt.Errorf("consumer reward denom registration fee is invalid: %s", err)
	}
	if err := ccvtypes.ValidatePositiveInt64(p.BlocksPerEpoch); err != nil {
		return fmt.Errorf("blocks per epoch is invalid: %s", err)
	}
	if err := ccvtypes.ValidatePositiveInt64(p.NumberOfEpochsToStartReceivingRewards); err != nil {
		return fmt.Errorf("number of epochs to start receiving rewards is invalid: %s", err)
	}

	if err := ccvtypes.ValidatePositiveInt64(p.MaxProviderConsensusValidators); err != nil {
		return fmt.Errorf("max provider consensus validators is invalid: %s", err)
	}
	return nil
}

// ParamSetPairs implements params.ParamSet
func (p *Params) ParamSetPairs() paramtypes.ParamSetPairs {
	return paramtypes.ParamSetPairs{
		paramtypes.NewParamSetPair(KeyTemplateClient, p.TemplateClient, ValidateTemplateClient),
		paramtypes.NewParamSetPair(KeyTrustingPeriodFraction, p.TrustingPeriodFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(ccvtypes.KeyCCVTimeoutPeriod, p.CcvTimeoutPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishPeriod, p.SlashMeterReplenishPeriod, ccvtypes.ValidateDuration),
		paramtypes.NewParamSetPair(KeySlashMeterReplenishFraction, p.SlashMeterReplenishFraction, ccvtypes.ValidateStringFraction),
		paramtypes.NewParamSetPair(KeyConsumerRewardDenomRegistrationFee, p.ConsumerRewardDenomRegistrationFee, ValidateCoin),
		paramtypes.NewParamSetPair(KeyBlocksPerEpoch, p.BlocksPerEpoch, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(KeyNumberOfEpochsToStartReceivingRewards, p.NumberOfEpochsToStartReceivingRewards, ccvtypes.ValidatePositiveInt64),
		paramtypes.NewParamSetPair(KeyMaxProviderConsensusValidators, p.MaxProviderConsensusValidators, ccvtypes.ValidatePositiveInt64),
	}
}

func ValidateTemplateClient(i interface{}) error {
	cs, ok := i.(ibctmtypes.ClientState)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T, expected: %T", i, ibctmtypes.ClientState{})
	}

	// copy clientstate to prevent changing original pointer
	copiedClient := cs

	// populate zeroed fields with valid fields
	copiedClient.ChainId = "chainid"

	trustPeriod, err := ccvtypes.CalculateTrustPeriod(ccvtypes.DefaultConsumerUnbondingPeriod, DefaultTrustingPeriodFraction)
	if err != nil {
		return fmt.Errorf("invalid TrustPeriodFraction: %T", err)
	}
	copiedClient.TrustingPeriod = trustPeriod

	copiedClient.UnbondingPeriod = ccvtypes.DefaultConsumerUnbondingPeriod
	copiedClient.LatestHeight = clienttypes.NewHeight(0, 1)

	if err := copiedClient.Validate(); err != nil {
		return err
	}
	return nil
}

func ValidateCoin(i interface{}) error {
	v, ok := i.(sdk.Coin)
	if !ok {
		return fmt.Errorf("invalid parameter type: %T", i)
	}

	if !v.IsValid() {
		return fmt.Errorf("invalid consumer reward denom registration fee: %s", v)
	}

	return nil
}
