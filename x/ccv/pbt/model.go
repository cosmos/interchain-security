type Action struct {
	kind            string
	val             int64
	amt             int64
	chains          []string
	n               int64
	secondsPerBlock int64
	chain           string
	power           int64
	height          int64
	factor          int64
	isDowntime      bool
}
type Delegate struct {
	val int64
	amt int64
}
type Undelegate struct {
	val int64
	amt int64
}
type JumpNBlocks struct {
	chains          []string
	n               int64
	secondsPerBlock int64
}
type Deliver struct {
	chain string
}
type ProviderSlash struct {
	val    int64
	power  int64
	height int64
	factor int64
}
type ConsumerSlash struct {
	val        int64
	height     int64
	power      int64
	isDowntime bool
}

func (s *PBTTestSuite) delegate(a Delegate) {
	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgDelegate(del, val, amt)
	pskServer.Delegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) undelegate(a Undelegate) {

	psk := s.providerChain.App.GetStakingKeeper()
	pskServer := stakingkeeper.NewMsgServerImpl(psk)
	amt := sdk.NewCoin(denom, sdk.NewInt(a.amt))
	del := s.delegator()
	val := s.validator(a.val)
	msg := stakingtypes.NewMsgUndelegate(del, val, amt)
	pskServer.Undelegate(sdk.WrapSDKContext(s.ctx(P)), msg)
}

func (s *PBTTestSuite) endBlock(chain string) {

}
func (s *PBTTestSuite) increaseSeconds(seconds int64) {
	s.coordinator.IncrementTimeBy(time.Second * time.Duration(seconds))
}
func (s *PBTTestSuite) deliver(a Deliver) {
	// TODO:!
}

func (s *PBTTestSuite) jumpNBlocks(a JumpNBlocks) {
	for i := int64(0); i < a.n; i++ {
		for _, c := range a.chains {
			s.endBlock(c)
		}
		s.increaseSeconds(a.secondsPerBlock)
	}
}

func (s *PBTTestSuite) providerSlash(a ProviderSlash) {
	psk := s.providerChain.App.GetStakingKeeper()
	val := s.consAddr(a.val)
	h := int64(a.height)
	power := int64(a.power)
	factor := sdk.NewDec(int64(a.factor))
	psk.Slash(s.ctx(P), val, h, power, factor, -1) // TODO: check params here!
}

func (s *PBTTestSuite) consumerSlash(a ConsumerSlash) {
	cccvk := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	val := s.consAddr(a.val)
	h := int64(a.height)
	power := int64(a.power)
	kind := stakingtypes.Downtime
	if !a.isDowntime {
		kind = stakingtypes.DoubleSign
	}
	cccvk.Slash(s.ctx(C), val, h, power, sdk.Dec{}, kind) // TODO: check params here!
}