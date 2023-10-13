package types

import (
	context "context"
	"time"

	transfertypes "github.com/cosmos/ibc-go/v8/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	conntypes "github.com/cosmos/ibc-go/v8/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v8/modules/core/04-channel/types"
	ibcexported "github.com/cosmos/ibc-go/v8/modules/core/exported"

	"cosmossdk.io/math"

	"github.com/cosmos/cosmos-sdk/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	capabilitytypes "github.com/cosmos/ibc-go/modules/capability/types"

	abci "github.com/cometbft/cometbft/abci/types"
)

// StakingKeeper defines the contract expected by provider-chain ccv module from a Staking Module that will keep track
// of the provider validator set. This version of the interchain-security protocol will mirror the provider chain's changes
// so we do not need a registry module between the staking module and CCV.
type StakingKeeper interface {
	GetValidatorUpdates(ctx context.Context) ([]abci.ValidatorUpdate, error)
	UnbondingCanComplete(ctx context.Context, id uint64) error
	UnbondingTime(ctx context.Context) (time.Duration, error)
	GetValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.Validator, error)
	GetLastValidatorPower(ctx context.Context, operator sdk.ValAddress) (int64, error)
	// slash the validator and delegators of the validator, specifying offence height, offence power, and slash fraction
	Jail(context.Context, sdk.ConsAddress) error // jail a validator
	Slash(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec) (math.Int, error)
	SlashWithInfractionReason(ctx context.Context, consAddr sdk.ConsAddress, infractionHeight, power int64, slashFactor math.LegacyDec, infraction stakingtypes.Infraction) (math.Int, error)
	Unjail(ctx context.Context, addr sdk.ConsAddress) error
	GetValidator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.Validator, error)
	IterateLastValidatorPowers(ctx context.Context, cb func(addr sdk.ValAddress, power int64) (stop bool)) error
	IterateValidators(ctx context.Context, f func(index int64, validator stakingtypes.ValidatorI) (stop bool)) error
	PowerReduction(ctx context.Context) math.Int
	PutUnbondingOnHold(ctx context.Context, id uint64) error
	Validator(ctx context.Context, addr sdk.ValAddress) (stakingtypes.ValidatorI, error)
	IsValidatorJailed(ctx context.Context, addr sdk.ConsAddress) (bool, error)
	ValidatorByConsAddr(ctx context.Context, consAddr sdk.ConsAddress) (stakingtypes.ValidatorI, error)
	Delegation(ctx context.Context, addr sdk.AccAddress, valAddr sdk.ValAddress) (stakingtypes.DelegationI, error)
	MaxValidators(ctx context.Context) (uint32, error)
	GetLastTotalPower(ctx context.Context) (math.Int, error)
	GetLastValidators(ctx context.Context) ([]stakingtypes.Validator, error)
	GetUnbondingType(ctx context.Context, id uint64) (stakingtypes.UnbondingType, error)
	BondDenom(ctx context.Context) (string, error)
}
type EvidenceKeeper interface {
	// NOTE: REFACTOR OR REMOVE @MSalopek this is deprecated, or otherwise not aviailable in v50
	// HandleEquivocationEvidence(ctx sdk.Context, evidence *evidencetypes.Equivocation)
}

// SlashingKeeper defines the contract expected to perform ccv slashing
type SlashingKeeper interface {
	JailUntil(context.Context, sdk.ConsAddress, time.Time) error // called from provider keeper only
	GetValidatorSigningInfo(context.Context, sdk.ConsAddress) (slashingtypes.ValidatorSigningInfo, error)
	DowntimeJailDuration(context.Context) (time.Duration, error)
	SlashFractionDowntime(context.Context) (math.LegacyDec, error)
	SlashFractionDoubleSign(context.Context) (math.LegacyDec, error)
	Tombstone(context.Context, sdk.ConsAddress) error
	IsTombstoned(context.Context, sdk.ConsAddress) bool
}

// ChannelKeeper defines the expected IBC channel keeper
type ChannelKeeper interface {
	GetChannel(ctx sdk.Context, srcPort, srcChan string) (channel channeltypes.Channel, found bool)
	GetNextSequenceSend(ctx sdk.Context, portID, channelID string) (uint64, bool)
	SendPacket(
		ctx sdk.Context,
		chanCap *capabilitytypes.Capability,
		sourcePort string,
		sourceChannel string,
		timeoutHeight clienttypes.Height,
		timeoutTimestamp uint64,
		data []byte,
	) (sequence uint64, err error)
	WriteAcknowledgement(ctx sdk.Context, chanCap *capabilitytypes.Capability, packet ibcexported.PacketI, acknowledgement ibcexported.Acknowledgement) error
	ChanCloseInit(ctx sdk.Context, portID, channelID string, chanCap *capabilitytypes.Capability) error
	GetChannelConnection(ctx sdk.Context, portID, channelID string) (string, ibcexported.ConnectionI, error)
}

// PortKeeper defines the expected IBC port keeper
type PortKeeper interface {
	BindPort(ctx sdk.Context, portID string) *capabilitytypes.Capability
}

// ConnectionKeeper defines the expected IBC connection keeper
type ConnectionKeeper interface {
	GetConnection(ctx sdk.Context, connectionID string) (conntypes.ConnectionEnd, bool)
}

// ClientKeeper defines the expected IBC client keeper
type ClientKeeper interface {
	CreateClient(ctx sdk.Context, clientState ibcexported.ClientState, consensusState ibcexported.ConsensusState) (string, error)
	GetClientState(ctx sdk.Context, clientID string) (ibcexported.ClientState, bool)
	GetLatestClientConsensusState(ctx sdk.Context, clientID string) (ibcexported.ConsensusState, bool)
	GetSelfConsensusState(ctx sdk.Context, height ibcexported.Height) (ibcexported.ConsensusState, error)
}

// DistributionKeeper defines the expected interface of the distribution keeper
type DistributionKeeper interface {
	FundCommunityPool(ctx context.Context, amount sdk.Coins, sender sdk.AccAddress) error
}

// ConsumerHooks event hooks for newly bonded cross-chain validators
type ConsumerHooks interface {
	AfterValidatorBonded(ctx context.Context, consAddr sdk.ConsAddress, valAddresses sdk.ValAddress) error
}

// BankKeeper defines the expected interface needed to retrieve account balances.
type BankKeeper interface {
	GetBalance(ctx context.Context, addr sdk.AccAddress, denom string) sdk.Coin
	GetAllBalances(ctx context.Context, addr sdk.AccAddress) sdk.Coins
	SendCoinsFromModuleToModule(ctx context.Context, senderModule, recipientModule string, amt sdk.Coins) error
}

// AccountKeeper defines the expected account keeper used for simulations
type AccountKeeper interface {
	GetModuleAccount(ctx context.Context, name string) types.ModuleAccountI
}

// IBCTransferKeeper defines the expected interface needed for distribution transfer
// of tokens from the consumer to the provider chain
type IBCTransferKeeper interface {
	Transfer(context.Context, *transfertypes.MsgTransfer) (*transfertypes.MsgTransferResponse, error)
}

// IBCKeeper defines the expected interface needed for openning a
// channel
type IBCCoreKeeper interface {
	ChannelOpenInit(
		goCtx context.Context,
		msg *channeltypes.MsgChannelOpenInit,
	) (*channeltypes.MsgChannelOpenInitResponse, error)
}

type ScopedKeeper interface {
	GetCapability(ctx sdk.Context, name string) (*capabilitytypes.Capability, bool)
	AuthenticateCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) bool
	ClaimCapability(ctx sdk.Context, cap *capabilitytypes.Capability, name string) error
}
