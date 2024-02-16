package provider_test

import (
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v7/modules/core/04-channel/types"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider"
	"github.com/stretchr/testify/require"
)

func TestGetProviderDenom(t *testing.T) {
	testCases := []struct {
		name             string
		denom            string
		packet           channeltypes.Packet
		expProviderDenom string
	}{
		{
			name:  "returns base denom with destination port and channel as prefix",
			denom: "stake",
			packet: channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			expProviderDenom: "dstPort/dstChannel/stake",
		},
		{
			name:  "returns base denom if the prefix denom corresponds to the packet's port and channel source",
			denom: "srcPort/srcChannel/stake",
			packet: channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			expProviderDenom: "stake",
		},
		{
			name:  "returns prefixed denom updated with destination port and channel as prefix",
			denom: "dstPort/dstChannel/stake",
			packet: channeltypes.NewPacket(
				[]byte{},
				0,
				"srcPort",
				"srcChannel",
				"dstPort",
				"dstChannel",
				clienttypes.NewHeight(1, 1),
				0,
			),
			expProviderDenom: "dstPort/dstChannel/dstPort/dstChannel/stake",
		},
	}

	channeltypes.NewPacket(
		[]byte{},
		0,
		"srcPort",
		"srcChannel",
		"dstPort",
		"dstChannel",
		clienttypes.NewHeight(1, 1),
		0,
	)
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			res := provider.GetProviderDenom(
				tc.denom,
				tc.packet,
			)

			require.Equal(t, tc.expProviderDenom, res)
		})
	}
}
