package interchain

import (
	"testing"

	"github.com/stretchr/testify/suite"
)

func TestConsumerSuite(t *testing.T) {
	s := &ConsumerSuite{}

	suite.Run(t, s)
}
