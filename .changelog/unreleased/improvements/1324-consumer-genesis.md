- Split out consumer genesis state to reduce shared data between provider and
  consumer. ([\#1324](https://github.com/cosmos/interchain-security/pull/1324))
  - Note: This breaks json format used by augmenting Genesis files of consumer 
  chains with consumer genesis content exported from provider chain. Consumer 
  Genesis content exported from a provider chain using major version 1, 2 or 3 
  of the provider module needs to be transformed with the transformation command 
  introduced by this PR:
    ```
    Transform the consumer genesis file from a provider version v1, v2 or v3 to a version supported by this consumer. Result is printed to STDOUT.

    Example:
    $ <appd> transform /path/to/ccv_consumer_genesis.json

    Usage:
      interchain-security-cd genesis transform [genesis-file] [flags]
    ```