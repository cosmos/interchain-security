
// TODO: clear up these hacks after stripping provider/consumer
func (s *PBTTestSuite) DisableConsumerDistribution() {
	cChain := s.consumerChain
	cApp := cChain.App.(*appConsumer.App)
	for i, moduleName := range cApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			cApp.MM.OrderBeginBlockers = append(cApp.MM.OrderBeginBlockers[:i], cApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func adjustParams(s *PBTTestSuite) {
	params := s.providerChain.App.GetStakingKeeper().GetParams(s.ctx(P))
	params.MaxValidators = maxValidators
	s.providerChain.App.GetStakingKeeper().SetParams(s.ctx(P), params)
}

func (s *PBTTestSuite) TestAssumptions() {

	adjustParams(s)

	s.jumpNBlocks(JumpNBlocks{P, 1, 5})
	// TODO: Is it correct to catch the consumer up with the provider here?
	s.jumpNBlocks(JumpNBlocks{C, 2, 5})

	equalHeights(s)

	/*
		delegatorBalance() overflows int64 because it is set to a number greater than 2^63 in genesis.
		It's easiest to assume we have enough funds.
	*/

	maxValsE := uint32(3)
	maxVals := s.providerChain.App.GetStakingKeeper().GetParams(s.ctx(P)).MaxValidators

	if maxValsE != maxVals {
		s.T().Fatal("Bad test")
	}

	for i := 0; i < 4; i++ {
		// This is the genesis delegation
		delE := int64(1)
		del := s.delegation(int64(i))
		if delE != del {
			s.T().Fatal("Bad test")
		}
	}

	step := int64(1)

	for i := 0; i < 3; i++ {
		s.delegate(Delegate{int64(i), (3 - int64(i)) * step, true})
	}

	for i := 0; i < 4; i++ {
		delE := (3-int64(i))*step + int64(1)
		del := s.delegation(int64(i))
		if delE != del {
			s.T().Fatal("Bad test")
		}
	}

	for i := 0; i < maxValidators; i++ {
		// First ones should be bonded
		A := s.validatorStatus(P, int64(i))
		E := stakingtypes.Bonded
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	for i := maxValidators; i < 4; i++ {
		A := s.validatorStatus(P, int64(i))
		// Last one is unbonding
		E := stakingtypes.Unbonding
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	equalHeights(s)

	for i := 0; i < maxValidators; i++ {
		A := s.validatorTokens(P, int64(i))
		E := (3-int64(i))*step + int64(1)
		if E != A {
			s.T().Fatal("Bad test")
		}
	}

	// validator tokens are 4,3,2,1

}

func executeTrace(s *PBTTestSuite, trace []Action) {

	for _, a := range trace {
		// succeed := a.succeed
		switch a.kind {
		case "delegate":
			s.delegate(Delegate{
				a.val,
				a.amt,
			})
		case "undelegate":
			s.undelegate(Undelegate{
				a.val,
				a.amt,
			})
		case "jumpNBlocks":
			s.jumpNBlocks(JumpNBlocks{
				a.chains,
				a.n,
				a.secondsPerBlock,
			})
		case "deliver":
			s.deliver(Deliver{a.chain})
		case "providerSlash":
			s.providerSlash(ProviderSlash{
				a.val,
				a.power,
				a.height,
				a.factor,
			})
		case "consumerSlash":
			s.consumerSlash(ConsumerSlash{
				a.val,
				a.height,
				a.power,
				a.isDowntime,
			})
		}
	}
}

func (s *PBTTestSuite) TestTraceHC() {

	trace := []Action{
		{
			kind: "delegate",
			val:  0,
			amt:  1,
		},
		{
			kind: "undelegate",
			val:  0,
			amt:  1,
		},
		{
			kind:            "jumpNBlocks",
			chains:          []string{P},
			n:               8,
			secondsPerBlock: 5,
		},
		{
			kind:  "deliver",
			chain: P,
		},
		{
			kind:   "providerSlash",
			val:    0,
			power:  22,
			height: 0,
			factor: 5,
		},
		{
			kind:       "consumerSlash",
			val:        0,
			power:      22,
			height:     0,
			isDowntime: true,
		},
	}

	executeTrace(s, trace)

}
