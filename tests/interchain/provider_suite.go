package interchain

import (
	"context"
	"cosmos/interchain-security/tests/interchain/chainsuite"
	"fmt"
	"sync"

	"github.com/stretchr/testify/suite"
)

type ProviderSuite struct {
	suite.Suite
	Provider     *chainsuite.Chain
	ctx          context.Context
	walletMtx    sync.Mutex
	walletsInUse map[int]bool
}

func (s *ProviderSuite) SetupSuite() {
	s.walletsInUse = make(map[int]bool)
	ctx, err := chainsuite.NewSuiteContext(&s.Suite)
	s.Require().NoError(err)
	s.ctx = ctx

	// create and start provider chain
	s.Provider, err = chainsuite.CreateProviderChain(s.GetContext(), s.T(), chainsuite.GetProviderSpec())
	s.Require().NoError(err)
}

func (s *ProviderSuite) GetContext() context.Context {
	s.Require().NotNil(s.ctx, "Tried to GetContext before it was set. SetupSuite must run first")
	return s.ctx
}

// GetUnusedTestingAddresss retrieves an unused wallet address and its key name safely
func (s *ProviderSuite) GetUnusedTestingAddresss() (formattedAddress string, keyName string, err error) {
	s.walletMtx.Lock()
	defer s.walletMtx.Unlock()

	for i, wallet := range s.Provider.TestWallets {
		if !s.walletsInUse[i] {
			s.walletsInUse[i] = true
			return wallet.FormattedAddress(), wallet.KeyName(), nil
		}
	}

	return "", "", fmt.Errorf("no unused wallets available")
}
