package testing

import (
	"time"

	connectiontypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	"github.com/cosmos/ibc-go/v7/modules/core/exported"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/ibc-go/v7/testing/mock"
)

/*
TODO: Remove after upgrading to ibc-go v5
legacy_ibc_testing is temporarily copied into the interchain-security repository for the purpose of testing only.
The integration test suites rely on modifications to ibc-go's test framework that cannot be back-ported to the canonical version that ics will rely on.
These files will be deprecated once ICS is able to upgrade to ibc-go v5.
*/

type ClientConfig interface {
	GetClientType() string
}

type TendermintConfig struct {
	TrustLevel                   ibctmtypes.Fraction
	TrustingPeriod               time.Duration
	UnbondingPeriod              time.Duration
	MaxClockDrift                time.Duration
	AllowUpdateAfterExpiry       bool
	AllowUpdateAfterMisbehaviour bool
}

func NewTendermintConfig() *TendermintConfig {
	return &TendermintConfig{
		TrustLevel:                   DefaultTrustLevel,
		TrustingPeriod:               TrustingPeriod,
		UnbondingPeriod:              UnbondingPeriod,
		MaxClockDrift:                MaxClockDrift,
		AllowUpdateAfterExpiry:       false,
		AllowUpdateAfterMisbehaviour: false,
	}
}

func (tmcfg *TendermintConfig) GetClientType() string {
	return exported.Tendermint
}

type ConnectionConfig struct {
	DelayPeriod uint64
	Version     *connectiontypes.Version
}

func NewConnectionConfig() *ConnectionConfig {
	return &ConnectionConfig{
		DelayPeriod: DefaultDelayPeriod,
		Version:     ConnectionVersion,
	}
}

type ChannelConfig struct {
	PortID  string
	Version string
	Order   channeltypes.Order
}

func NewChannelConfig() *ChannelConfig {
	return &ChannelConfig{
		PortID:  mock.PortID,
		Version: DefaultChannelVersion,
		Order:   channeltypes.UNORDERED,
	}
}
