package main

import "time"

type Stats struct {
	highestObservedValPower int64

	maxNumInFlightPackets int

	numStartedChains int
	numStops         int
	numTimeouts      int

	numSentPackets int
	numBlocks      int
	numTxs         int

	totalBlockTimePassedPerTrace time.Duration

	numKeyAssignments int
}
