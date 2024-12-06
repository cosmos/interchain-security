package interchain

import (
	"testing"

	"github.com/stretchr/testify/suite"
)

type MultiValidatorProviderSuite struct {
	ProviderSuite
}

func TestMultiValidatorProviderSuite(t *testing.T) {
	s := &MultiValidatorProviderSuite{}
	s.ValidatorNodes = 2

	suite.Run(t, s)
}
