package pbt

type Action struct {
	Amt             int      `json:"amt,omitempty"`
	Chain           string   `json:"chain,omitempty"`
	Chains          []string `json:"chains,omitempty"`
	Factor          float64  `json:"factor,omitempty"`
	Height          int      `json:"height,omitempty"`
	IsDowntime      bool     `json:"is_downtime"`
	Kind            string   `json:"kind"`
	N               int      `json:"n,omitempty"`
	Power           int      `json:"power,omitempty"`
	SecondsPerBlock int      `json:"seconds_per_block,omitempty"`
	Val             int      `json:"val,omitempty"`
}

type Trace struct {
	Actions []Action `json:"actions"`
	Blocks  struct {
		Consumer []struct {
			H        int `json:"h"`
			Snapshot struct {
				DelegatorTokens float64 `json:"delegator_tokens"`
				H               struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"h"`
				Jailed []*int `json:"jailed"`
				Power  []*int `json:"power"`
				T      struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"t"`
				Tokens        []int `json:"tokens"`
				UndelegationQ []struct {
					Balance        int  `json:"balance"`
					CompletionTime int  `json:"completion_time"`
					CreationHeight int  `json:"creation_height"`
					Expired        bool `json:"expired"`
					InitialBalance int  `json:"initial_balance"`
					OnHold         bool `json:"on_hold"`
					OpID           int  `json:"op_id"`
					Val            int  `json:"val"`
				} `json:"undelegationQ"`
			} `json:"snapshot"`
			T int `json:"t"`
		} `json:"consumer"`
		Provider []struct {
			H        int `json:"h"`
			Snapshot struct {
				DelegatorTokens float64 `json:"delegator_tokens"`
				H               struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"h"`
				Jailed []*int `json:"jailed"`
				Power  []*int `json:"power"`
				T      struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"t"`
				Tokens        []int `json:"tokens"`
				UndelegationQ []struct {
					Balance        int  `json:"balance"`
					CompletionTime int  `json:"completion_time"`
					CreationHeight int  `json:"creation_height"`
					Expired        bool `json:"expired"`
					InitialBalance int  `json:"initial_balance"`
					OnHold         bool `json:"on_hold"`
					OpID           int  `json:"op_id"`
					Val            int  `json:"val"`
				} `json:"undelegationQ"`
			} `json:"snapshot"`
			T int `json:"t"`
		} `json:"provider"`
	} `json:"blocks"`
	Consequences []struct {
		DelegatorTokens float64 `json:"delegator_tokens"`
		H               struct {
			Consumer int `json:"consumer"`
			Provider int `json:"provider"`
		} `json:"h"`
		Jailed []*int `json:"jailed"`
		Power  []*int `json:"power"`
		T      struct {
			Consumer int `json:"consumer"`
			Provider int `json:"provider"`
		} `json:"t"`
		Tokens        []int `json:"tokens"`
		UndelegationQ []struct {
			Balance        int  `json:"balance"`
			CompletionTime int  `json:"completion_time"`
			CreationHeight int  `json:"creation_height"`
			Expired        bool `json:"expired"`
			InitialBalance int  `json:"initial_balance"`
			OnHold         bool `json:"on_hold"`
			OpID           int  `json:"op_id"`
			Val            int  `json:"val"`
		} `json:"undelegationQ"`
	} `json:"consequences"`
	Events []string `json:"events"`
}
