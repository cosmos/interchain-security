package main

import (
	"fmt"
	"strings"
)

// combinedDockerImageName names a combined image using the explicit tags of the
// images returned by getDockerImage. Digest references are not supported.
func combinedDockerImageName(providerImage, consumerImage string) (string, error) {
	var tags [2]string
	for i, image := range []string{providerImage, consumerImage} {
		// A registry port precedes the last slash; a tag separator follows it.
		separator := strings.LastIndex(image, ":")
		if strings.Contains(image, "@") || separator <= strings.LastIndex(image, "/") ||
			separator == 0 || separator == len(image)-1 {
			return "", fmt.Errorf("cannot name combined docker image: expected an explicit tag without a digest in %q", image)
		}
		tags[i] = image[separator+1:]
	}
	return fmt.Sprintf("cosmos-ics-combined:%s_%s", tags[0], tags[1]), nil
}
