package main

// Get compatible provider versions for this consumer
//
// Note: This is a hardcoded list of tags which has to be updated manually
// and serves as base information of different versions to be tested
// against this consumer implementation
func GetCompatibleProviderVersions() []string {
	return []string{"v3.0.x"}
}

// Get compatible consumer versions for this provider
//
// Note: This is a hardcoded list of tags which has to be updated manually
// and serves as base information of different versions to be tested
// against this provider implementation
func GetCompatibleConsumerVersions() []string {
	// For now it's the same as for provider
	return GetCompatibleProviderVersions()
}
