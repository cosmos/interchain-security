package testing

import (
	"time"

	ibctransfertypes "github.com/cosmos/ibc-go/v7/modules/apps/transfer/types"
	connectiontypes "github.com/cosmos/ibc-go/v7/modules/core/03-connection/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/cosmos/ibc-go/v7/testing/mock"
)

/*
TODO: Remove after upgrading to ibc-go v5
legacy_ibc_testing is temporarily copied into the interchain-security repository for the purpose of testing only.
The integration test suites rely on modifications to ibc-go's test framework that cannot be back-ported to the canonical version that ics will rely on.
These files will be deprecated once ICS is able to upgrade to ibc-go v5.
*/

const (
	FirstChannelID    = "channel-0"
	FirstConnectionID = "connection-0"

	// Default params constants used to create a TM client
	TrustingPeriod     time.Duration = time.Hour * 24 * 7 * 2
	UnbondingPeriod    time.Duration = time.Hour * 24 * 7 * 3
	MaxClockDrift      time.Duration = time.Second * 10
	DefaultDelayPeriod uint64        = 0

	DefaultChannelVersion = mock.Version
	InvalidID             = "IDisInvalid"

	// Application Ports
	TransferPort = ibctransfertypes.ModuleName
	MockPort     = mock.ModuleName

	// used for testing proposals
	Title       = "title"
	Description = "description"
)

var (
	DefaultOpenInitVersion *connectiontypes.Version

	// Default params variables used to create a TM client
	DefaultTrustLevel ibctmtypes.Fraction = ibctmtypes.DefaultTrustLevel

	UpgradePath = []string{"upgrade", "upgradedIBCState"}

	ConnectionVersion = connectiontypes.ExportedVersionsToProto(connectiontypes.GetCompatibleVersions())[0]

	MockAcknowledgement = mock.MockAcknowledgement.Acknowledgement()
	MockPacketData      = mock.MockPacketData
)
