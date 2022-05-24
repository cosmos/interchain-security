package main

type T []struct {
	Actions []struct {
		Amt             int      `json:"amt,omitempty"`
		Chain           string   `json:"chain,omitempty"`
		Chains          []string `json:"chains,omitempty"`
		Factor          float64  `json:"factor,omitempty"`
		Height          int      `json:"height,omitempty"`
		IsDowntime      bool     `json:"is_downtime,omitempty"`
		Kind            string   `json:"kind"`
		N               int      `json:"n,omitempty"`
		Power           int      `json:"power,omitempty"`
		SecondsPerBlock int      `json:"seconds_per_block,omitempty"`
		Val             int      `json:"val,omitempty"`
	} `json:"actions"`
}
