package difftest

type Action struct {
	Amt              int      `json:"amt,omitempty"`
	Chain            string   `json:"chain,omitempty"`
	Chains           []string `json:"chains,omitempty"`
	InfractionHeight int      `json:"infractionHeight,omitempty"`
	IsDowntime       bool     `json:"isDowntime"`
	Kind             string   `json:"kind"`
	N                int      `json:"n,omitempty"`
	NumPackets       int      `json:"numPackets,omitempty"`
	SecondsPerBlock  int      `json:"secondsPerBlock,omitempty"`
	Val              int      `json:"val,omitempty"`
}

type Snapshot struct {
	DelegatorTokens int `json:"delegatorTokens"`
	H               struct {
		Consumer int `json:"consumer"`
		Provider int `json:"provider"`
	} `json:"h"`
	Jailed []*int `json:"jailed"`
	Outbox struct {
		C [][]interface{} `json:"C"`
		P [][]interface{} `json:"P"`
	} `json:"outbox"`
	Power  []*int   `json:"power"`
	Status []string `json:"status"`
	T      struct {
		Consumer int `json:"consumer"`
		Provider int `json:"provider"`
	} `json:"t"`
	Tokens        []int `json:"tokens"`
	UndelegationQ []struct {
		Balance        int  `json:"balance"`
		CompletionTime int  `json:"completionTime"`
		CreationHeight int  `json:"creationHeight"`
		Expired        bool `json:"expired"`
		InitialBalance int  `json:"initialBalance"`
		OnHold         bool `json:"onHold"`
		OpID           int  `json:"opID"`
		Val            int  `json:"val"`
	} `json:"undelegationQ"`
	ValidatorQ []struct {
		Expired         bool `json:"expired"`
		OnHold          bool `json:"onHold"`
		OpID            int  `json:"opID"`
		UnbondingHeight int  `json:"unbondingHeight"`
		UnbondingTime   int  `json:"unbondingTime"`
		Val             int  `json:"val"`
	} `json:"validatorQ"`
}

type Block struct {
	H        int      `json:"h"`
	T        int      `json:"t"`
	Snapshot Snapshot `json:"snapshot"`
}

type Blocks struct {
	Consumer []Block `json:"consumer"`
	Provider []Block `json:"provider"`
}

type HLastCommit struct {
	Consumer int `json:"consumer"`
	Provider int `json:"provider"`
}

type TraceData struct {
	Actions []struct {
		Action      Action      `json:"action"`
		HLastCommit HLastCommit `json:"hLastCommit"`
	} `json:"actions"`
	Blocks    Blocks `json:"blocks"`
	Constants struct {
		BlockSeconds           int    `json:"BLOCK_SECONDS"`
		C                      string `json:"C"`
		CcvTimeoutTimestamp    int    `json:"CCV_TIMEOUT_TIMESTAMP"`
		InitialDelegatorTokens int    `json:"INITIAL_DELEGATOR_TOKENS"`
		JailSeconds            int    `json:"JAIL_SECONDS"`
		MaxBlockAdvances       int    `json:"MAX_BLOCK_ADVANCES"`
		MaxValidators          int    `json:"MAX_VALIDATORS"`
		NumValidators          int    `json:"NUM_VALIDATORS"`
		P                      string `json:"P"`
		TokenScalar            int    `json:"TOKEN_SCALAR"`
		TrustingSeconds        int    `json:"TRUSTING_SECONDS"`
		UnbondingSecondsC      int    `json:"UNBONDING_SECONDS_C"`
		UnbondingSecondsP      int    `json:"UNBONDING_SECONDS_P"`
		ZeroTimeoutHeight      int    `json:"ZERO_TIMEOUT_HEIGHT"`
	} `json:"constants"`
	Events []string `json:"events"`
	Meta   struct {
		Commit string `json:"commit"`
		Diff   string `json:"diff"`
	} `json:"meta"`
}
