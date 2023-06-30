package types

import (
	"testing"

	abci "github.com/cometbft/cometbft/abci/types"
	"github.com/cometbft/cometbft/libs/bytes"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/stretchr/testify/require"
)

func TestConsumerPacketDataMarshalling(t *testing.T) {
	// create and marshal a consumer packet as proto bytes -> uses "new" Infraction enum
	newSlashFormat := NewSlashPacketData(
		abci.Validator{Address: bytes.HexBytes{}, Power: int64(1)},
		uint64(1),
		stakingtypes.Infraction_INFRACTION_DOWNTIME,
	)
	newPacketFormat := ConsumerPacketData{
		Type: SlashPacket,
		Data: &ConsumerPacketData_SlashPacketData{
			SlashPacketData: newSlashFormat, // -> uses "new" Infraction enum
		},
	}
	newPacketFormatBytes, err := newPacketFormat.Marshal()
	if err != nil {
		require.NoError(t, err, "could not marshal v47bytes")
		t.FailNow()
	}
	require.NotZero(t, newPacketFormatBytes, "newPacketFormatBytes should not be zero")

	var oldPacketFormat ConsumerPacketDataV1
	err = oldPacketFormat.Unmarshal(newPacketFormatBytes)
	if err != nil {
		require.NoError(t, err, "could not unmarshal newPacketFormatBytes")
		t.FailNow()
	}
	require.NotZero(t, oldPacketFormat, "oldPacketFormat should not be zero")

	oldPacketFormatBytes, err := oldPacketFormat.Marshal()
	if err != nil {
		require.NoError(t, err, "could not marshal oldPacketFormat")
		t.FailNow()
	}
	require.NotZero(t, oldPacketFormatBytes, "oldPacketFormatBytes should not be zero")

	// allow visually confirming that these are the same bytes
	t.Log("oldPacketFormatBytes", oldPacketFormatBytes) // [8 1 18 8 10 2 24 1 16 1 24 2] -> same byte array
	t.Log("newPacketFormatBytes", newPacketFormatBytes) // [8 1 18 8 10 2 24 1 16 1 24 2] -> same byte array
	// check that the old packet format is the same as the new packet format
	require.Equal(t, newPacketFormatBytes, oldPacketFormatBytes, "oldPacketFormatBytes should be the same as newPacketFormatBytes")

	// compare JSON strings
	newPacketFormatJSON := ModuleCdc.MustMarshalJSON(&newPacketFormat)
	oldPacketFormatJSON := ModuleCdc.MustMarshalJSON(&oldPacketFormat)

	t.Log("oldPacketFormatJSON", string(newPacketFormatJSON)) // {"type":"CONSUMER_PACKET_TYPE_SLASH","slashPacketData":{"validator":{"address":"","power":"1"},"valset_update_id":"1","infraction":"INFRACTION_DOWNTIME"}} -> different byte array
	t.Log("newPacketFormatJSON", string(oldPacketFormatJSON)) // {"type":"CONSUMER_PACKET_TYPE_SLASH","slashPacketData":{"validator":{"address":null,"power":"1"},"valset_update_id":"1","infraction":"INFRACTION_TYPE_DOWNTIME"}} -> different byte array

	require.NotEqual(t, newPacketFormatJSON, oldPacketFormatJSON, "oldPacketFormatJSON and newPacketFormatJSON are the same")
}
