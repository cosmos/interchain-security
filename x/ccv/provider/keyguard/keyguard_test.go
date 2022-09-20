package keyguard

import (
	"testing"
)

type TraceState struct {
	Mapping      map[LK]FK
	LocalUpdates []update
	TP           int
	TC           int
	TM           int
}

type Driver struct {
	lastTP int
	lastTC int
	lastTM int
}

func (d *Driver) runTrace(t *testing.T, trace []TraceState) {
	kg := KeyGuard{}
	// TODO:

	// These are the critical properties
	// 1. All validator sets on consumer are a validator set for provider for an earlier
	// time, mapped through the effective mapping at that time.
	// 2. It is always possible to fetch a local key, given a foreign key, if the foreign
	// key is still known to the consumer

	// My thinking now is that I can test by doing the following
	// If the trace TP increases than there is a new mapping and local updates
	// the local updates aggregate to create a local validator set
	// record that validator set, and the relevant mapping to time T=TP
	// If TC increases to time T, can check the ACTUAL validator set in C
	//	 It should be be possible to query kg for every validator foreign key
	//    in any intermediate val set in [TM+1, TP]
	// It should not be possible to query kg for any validator that does not appear
	// 		in any intermediate vla set in [0, TM]
	for _, s := range trace {
		if d.lastTP < s.TP {
			// TODO: impl all endblock shenanigans

		}
		if d.lastTC < s.TC {
			// TODO: do 'slash' checks
		}
		if d.lastTM < s.TM {
			// prune and do slash checks
		}
	}
}

func TestKeyDelegation(t *testing.T) {
	traces := [][]TraceState{}
	for _, trace := range traces {
		d := Driver{}
		d.runTrace(t, trace)
	}
}
