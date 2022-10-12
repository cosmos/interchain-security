package types

import (
// this line is used by starport scaffolding # genesis/types/import
// this line is used by starport scaffolding # ibc/genesistype/import
	"strings"
	"fmt"
)

// DefaultIndex is the default capability global index
const DefaultIndex uint64 = 1

// DefaultGenesis returns the default Capability genesis state
func DefaultGenesis() *GenesisState {
	return &GenesisState{
		Admins: []string{},
	}
}

// Validate performs basic genesis state validation returning an error upon any
// failure.
func (gs GenesisState) Validate() error {
	for _, admin := range gs.Admins {
		if strings.TrimSpace(admin) == "" {
			return fmt.Errorf("admin cannot be blank: %s", admin)
		}
	}

	return nil
}
