package main

import (
	"strings"
	"testing"
)

func TestCombinedDockerImageName(t *testing.T) {
	tests := []struct {
		name     string
		provider string
		consumer string
		want     string
	}{
		{"local", "repo:v1", "repo:v2", "cosmos-ics-combined:v1_v2"},
		{"registry", "ghcr.io/org/repo:v1", "ghcr.io/org/repo:v2", "cosmos-ics-combined:v1_v2"},
		{"registry ports", "localhost:5000/org/repo:v1", "localhost:5001/org/repo:v2", "cosmos-ics-combined:v1_v2"},
		{"mixed sources", "localhost:5000/org/repo:v7.0.0", "cosmos-ics:local", "cosmos-ics-combined:v7.0.0_local"},
		{"local build tags", "cosmos-ics:ea20044", "cosmos-ics_gaia:local-v23.0.0", "cosmos-ics-combined:ea20044_local-v23.0.0"},
		{"IPv6 registry", "[::1]:5000/org/repo:v1", "repo:v2", "cosmos-ics-combined:v1_v2"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got, err := combinedDockerImageName(tt.provider, tt.consumer)
			if err != nil {
				t.Fatal(err)
			}
			if got != tt.want {
				t.Fatalf("got %q, want %q", got, tt.want)
			}
		})
	}
}

func TestCombinedDockerImageNameRejectsUnsupportedReferences(t *testing.T) {
	digest := "sha256:" + strings.Repeat("a", 64)
	for _, image := range []string{
		"", "repo", "localhost:5000/org/repo", "repo:", ":v1",
		"ghcr.io/org/repo", "repo@" + digest, "repo:v1@" + digest,
	} {
		t.Run(image, func(t *testing.T) {
			for _, pair := range [][2]string{{image, "repo:v2"}, {"repo:v1", image}} {
				got, err := combinedDockerImageName(pair[0], pair[1])
				if err == nil || got != "" {
					t.Fatalf("combinedDockerImageName(%q, %q) = %q, %v; want empty name and error", pair[0], pair[1], got, err)
				}
			}
		})
	}
}
