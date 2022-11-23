package e2e

import (
	"testing"

	"github.com/stretchr/testify/require"
	"github.com/stretchr/testify/suite"
)

type ExperimentSuite struct {
	CCVTestSuite
}

func TestExperimentSuite(t *testing.T) {
	suite.Run(t, new(ExperimentSuite))
}

// TestPacketRoundtrip tests a CCV packet roundtrip when tokens are bonded on provider
func (s *ExperimentSuite) TestExperiment() {
	s.SetupCCVChannel()
	require.True(s.T(), false)
}
