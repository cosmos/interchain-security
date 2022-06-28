//go:build tools
// +build tools

package tools

import (
	_ "github.com/BurntSushi/toml/cmd/tomlv"
	_ "github.com/fzipp/gocyclo/cmd/gocyclo"
	_ "github.com/go-critic/go-critic/cmd/gocritic"
	_ "golang.org/x/tools/cmd/goimports"
)
