package main

type T []struct {
	Actions []struct {
		Amt             int      `json:"amt,omitempty"`
		Chain           string   `json:"chain,omitempty"`
		Chains          []string `json:"chains,omitempty"`
		Kind            string   `json:"kind"`
		N               int      `json:"n,omitempty"`
		SecondsPerBlock int      `json:"seconds_per_block,omitempty"`
		Val             int      `json:"val,omitempty"`
	} `json:"actions"`
	Blocks struct {
		Consumer []struct {
			H        int `json:"h"`
			Snapshot struct {
				DelegatorTokens float64 `json:"delegator_tokens"`
				H               struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"h"`
				Jailed []interface{} `json:"jailed"`
				Power  []*int        `json:"power"`
				T      struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"t"`
				Tokens        []int         `json:"tokens"`
				UndelegationQ []interface{} `json:"undelegationQ"`
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
				Jailed []interface{} `json:"jailed"`
				Power  []*int        `json:"power"`
				T      struct {
					Consumer int `json:"consumer"`
					Provider int `json:"provider"`
				} `json:"t"`
				Tokens        []int         `json:"tokens"`
				UndelegationQ []interface{} `json:"undelegationQ"`
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
		Jailed []interface{} `json:"jailed"`
		Power  []*int        `json:"power"`
		T      struct {
			Consumer int `json:"consumer"`
			Provider int `json:"provider"`
		} `json:"t"`
		Tokens        []int         `json:"tokens"`
		UndelegationQ []interface{} `json:"undelegationQ"`
	} `json:"consequences"`
	Events []string `json:"events"`
}
