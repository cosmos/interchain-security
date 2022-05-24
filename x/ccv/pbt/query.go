func (s *PBTTestSuite) ctx(chain string) sdk.Context {
	return s.chain(chain).GetContext()
}

func (s *PBTTestSuite) chain(chain string) *ibctesting.TestChain {
	chains := make(map[string]*ibctesting.TestChain)
	chains["provider"] = s.providerChain
	chains["consumer"] = s.consumerChain
	return chains[chain]
}

func (s *PBTTestSuite) height(chain string) int64 {
	return s.chain(chain).CurrentHeader.GetHeight()
}

func (s *PBTTestSuite) endpoint(chain string) *ibctesting.Endpoint {
	endpoints := make(map[string]*ibctesting.Endpoint)
	endpoints["provider"] = s.path.EndpointB
	endpoints["consumer"] = s.path.EndpointA
	return endpoints[chain]
}

func (s *PBTTestSuite) delegator() sdk.AccAddress {
	delAddr := s.providerChain.SenderAccount.GetAddress()
	return delAddr
}

func (s *PBTTestSuite) validator(i int64) sdk.ValAddress {
	tmValidator := s.providerChain.Vals.Validators[i]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	return valAddr
}

func (s *PBTTestSuite) consAddr(i int64) sdk.ConsAddress {
	val := s.providerChain.Vals.Validators[i]
	consAddr := sdk.ConsAddress(val.Address)
	return consAddr
}

func (s *PBTTestSuite) validatorStatus(chain string, i int64) stakingtypes.BondStatus {
	addr := s.validator(i)
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(s.ctx(chain), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.GetStatus()
}

func (s *PBTTestSuite) delegatorBalance() int64 {
	del := s.delegator()
	app := s.providerChain.App.(*appProvider.App)
	bal := app.BankKeeper.GetBalance(s.ctx(P), del, denom)
	return bal.Amount.Int64()
}

func (s *PBTTestSuite) validatorTokens(chain string, i int64) int64 {
	addr := s.validator(i)
	val, found := s.chain(chain).App.GetStakingKeeper().GetValidator(s.ctx(chain), addr)
	if !found {
		s.T().Fatal("Couldn't GetValidator")
	}
	return val.Tokens.Int64()
}

func (s *PBTTestSuite) delegation(i int64) int64 {
	addr := s.delegator()
	del, found := s.providerChain.App.GetStakingKeeper().GetDelegation(s.ctx(P), addr, s.validator(i))
	if !found {
		s.T().Fatal("Couldn't GetDelegation")
	}
	return del.Shares.TruncateInt64()
}

func equalHeights(s *PBTTestSuite) {
	ph := s.height(P)
	ch := s.height(C)
	if ph != ch {
		s.T().Fatal("Bad test")
	}
}