package difftest

type Action struct {
	Amt              int      `json:"amt,omitempty"`
	Chain            string   `json:"chain,omitempty"`
	Chains           []string `json:"chains,omitempty"`
	Factor           float64  `json:"factor,omitempty"`
	InfractionHeight int      `json:"infractionHeight,omitempty"`
	IsDowntime       bool     `json:"isDowntime"`
	Kind             string   `json:"kind"`
	N                int      `json:"n,omitempty"`
	Power            int      `json:"power,omitempty"`
	SecondsPerBlock  int      `json:"secondsPerBlock,omitempty"`
	Val              int      `json:"val,omitempty"`
}

type Consequence struct {
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

type Trace struct {
	Events      []string `json:"events"`
	Transitions []struct {
		Action      `json:"action"`
		Consequence `json:"consequence"`
	} `json:"transitions"`
}
