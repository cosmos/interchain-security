package types

import (
	"crypto/rand"
	"encoding/binary"
	"testing"
	time "time"

	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	"github.com/stretchr/testify/require"
	abci "github.com/tendermint/tendermint/abci/types"
)

//
// test_helpers.go contains helper functions for unit or integration tests,
// where certain populated structs are generated.
//

func GetTestConsumerAdditionProp() *ConsumerAdditionProposal {
	prop := NewConsumerAdditionProposal(
		"chainID",
		"description",
		"chainID",
		clienttypes.NewHeight(4, 5),
		[]byte("gen_hash"),
		[]byte("bin_hash"),
		time.Now(),
		DefaultConsumerRedistributeFrac,
		DefaultBlocksPerDistributionTransmission,
		DefaultHistoricalEntries,
		DefaultCCVTimeoutPeriod,
		DefaultTransferTimeoutPeriod,
		DefaultConsumerUnbondingPeriod,
	).(*ConsumerAdditionProposal)

	return prop
}

// Obtains a CrossChainValidator with a newly generated key, and randomized field values
func GetNewCrossChainValidator(t *testing.T) CrossChainValidator {
	t.Helper()
	b1 := make([]byte, 8)
	_, _ = rand.Read(b1)
	power := int64(binary.BigEndian.Uint64(b1))
	privKey := ed25519.GenPrivKey()
	validator, err := NewCCValidator(privKey.PubKey().Address(), power, privKey.PubKey())
	require.NoError(t, err)
	return validator
}

// Obtains slash packet data with a newly generated key, and randomized field values
func GetNewSlashPacketData() SlashPacketData {
	b1 := make([]byte, 8)
	_, _ = rand.Read(b1)
	b2 := make([]byte, 8)
	_, _ = rand.Read(b2)
	b3 := make([]byte, 8)
	_, _ = rand.Read(b3)
	return SlashPacketData{
		Validator: abci.Validator{
			Address: ed25519.GenPrivKey().PubKey().Address(),
			Power:   int64(binary.BigEndian.Uint64(b1)),
		},
		ValsetUpdateId: binary.BigEndian.Uint64(b2),
		Infraction:     stakingtypes.InfractionType(binary.BigEndian.Uint64(b2) % 3),
	}
}

// Obtains vsc matured packet data with a newly generated key
func GetNewVSCMaturedPacketData() VSCMaturedPacketData {
	b := make([]byte, 8)
	_, _ = rand.Read(b)
	return VSCMaturedPacketData{ValsetUpdateId: binary.BigEndian.Uint64(b)}
}
