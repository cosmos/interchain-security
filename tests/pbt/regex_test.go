package pbt_test

import (
	"net"
	"testing"

	"pgregory.net/rapid"
)

func TestParseValidIPv4(t *testing.T) {
	const ipv4re = `(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9])` +
		`\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9])` +
		`\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9])` +
		`\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9])`

	rapid.Check(t, func(t *rapid.T) {
		addr := rapid.StringMatching(ipv4re).Draw(t, "addr")
		ip := net.ParseIP(addr)
		if ip == nil || ip.String() != addr {
			t.Fatalf("parsed %q into %v", addr, ip)
		}
	})
}
