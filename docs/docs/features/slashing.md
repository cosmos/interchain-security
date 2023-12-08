---
sidebar_position: 4
---

# Consumer Initiated Slashing
A consumer chain is essentially a regular Cosmos-SDK based chain that uses the Interchain Security module to achieve economic security by stake deposited on the provider chain, instead of its own chain.
In essence, provider chain and consumer chains are different networks (different infrastructures) that are bound together by the provider's validator set. By being bound to the provider's validator set, a consumer chain inherits the economic security guarantees of the provider chain (in terms of total stake).

To maintain the proof of stake model, the consumer chain is able to send evidence of infractions (double signing and downtime) to the provider chain so the offending validators can be penalized.
Any infraction committed on any of the consumer chains is reflected on the provider and all other consumer chains.

In the current implementation there are two important changes brought by the Interchain Security module.

## Downtime Infractions

Downtime infractions are reported by consumer chains and are acted upon on the provider as soon as the provider receives the infraction evidence.

Instead of slashing, the provider will only jail offending validator for the duration of time established by the chain parameters.

:::info
[Slash throttling](../adrs/adr-002-throttle.md) (sometimes called jail throttling) mechanism ensures that only a fraction of the validator set can be jailed at any one time to prevent malicious consumer chains from harming the provider.
:::

## Equivocation Infractions

Equivocation infractions are reported by external agents (e.g., relayers) that can submit to the provider evidence of light client or double signing attacks observed on a consumer chain. 
The evidence is submitted by sending `MsgSubmitConsumerMisbehaviour` or `MsgSubmitConsumerDoubleVoting` transactions to the provider. 
When valid evidence is received, the malicious validators are slashed, jailed, and tombstoned on the provider.
This is enabled through the _cryptographic verification of equivocation_ feature. 
For more details, see [ADR-005](../adrs/adr-005-cryptographic-equivocation-verification.md) and [ADR-013](../adrs/adr-013-equivocation-slashing.md).

### Report equivocation infractions through CLI

The ICS provider module offers two commands for submitting evidence of misbehavior originating from a consumer chain.
Below are two examples illustrating the process on Cosmos Hub. 

Use the following command to submit evidence of double signing attacks:
```bash
gaiad tx provider submit-consumer-double-voting [path/to/evidence.json] [path/to/infraction_header.json] --from node0 --home ../node0 --chain-id $CID 
```

<details>
  <summary>Example of `evidence.json`</summary>
  <div>
    <div>
    ```json
    {
        "vote_a": {
            "type": 1,
            "height": 25,
            "round": 0,
            "block_id": {
                "hash": "tBBWTqjECl31S/clZGoxLdDqs93kTvy3qhpPqET/laY=",
                "part_set_header": {
                    "total": 1,
                    "hash": "ai2qCLgVZAFph4FJ4Cqw5QW1GZKR4zjOv0bI/Um5AIc="
                }
            },
            "timestamp": "2023-11-20T12:57:54.565207Z",
            "validator_address": "aCG1hw85Zz7Ylgpsy263IJVJEMA=",
            "signature": "y9yILm9hmv45BZwAaaq9mS1FpH7QeAIJ5Jkcc3U2/k5uks9cuqr4NTIwaIrqMSMKwxVyqiR56xmCT59a6AngAA=="
        },
        "vote_b": {
            "type": 1,
            "height": 25,
            "round": 0,
            "block_id": {
                "hash": "3P06pszgPatuIdLTP5fDWiase4SYHIq9YXGSbRk9/50=",
                "part_set_header": {
                    "total": 1,
                    "hash": "S+SbOMxFRzfeNNpX9/jyFMz94VwBKk7Dpx6ZyvSYyNU="
                }
            },
            "timestamp": "2023-11-20T12:57:54.599273Z",
            "validator_address": "aCG1hw85Zz7Ylgpsy263IJVJEMA=",
            "validator_index": 0,
            "signature": "DGFcn4Um1t2kXW60+JhMk5cj7ZFdE5goKVOGiZkLwnNv43+6aGmOWjoq0SHYVzM4MwSwOwbhgZNbkWX+EHGUBw=="
        },
        "total_voting_power": 300,
        "validator_power": 100,
        "timestamp": "2023-11-20T12:57:51.267308Z"
    }
    ```
    </div>
  </div>
</details>

<details>
  <summary>Example of `infraction_header.json`</summary>
  <div>
    <div>
    ```json
    {
        "signed_header": {
            "header": {
                "version": {
                    "block": 11,
                    "app": 2
                },
                "chain_id": "consumer",
                "height": 22,
                "time": "2023-11-20T12:57:40.479686Z",
                "last_block_id": {
                    "hash": "L63hyLJ+y9+fpb7WYKdmmBhPHwbfEGQEuKmvGzyBPiY=",
                    "part_set_header": {
                        "total": 18,
                        "hash": "euzRQjN7MjGtM6skXM4B8wOgAldWGfZSJRA9JRlO42s="
                    }
                },
                "last_commit_hash": "qdDJwVziW3pPqmf8QDGZG+5HVd3OF7fCVh2Z8KQqNVU=",
                "data_hash": "47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU=",
                "validators_hash": "pVc+gSYkGesaP3OkK4ig3DBi4o9/GCdXGtO/PQ6i/Ik=",
                "next_validators_hash": "pVc+gSYkGesaP3OkK4ig3DBi4o9/GCdXGtO/PQ6i/Ik=",
                "consensus_hash": "BICRvH3cKD93v7+R1zxE2ljD34qcvIZ0Bdi389qtoi8=",
                "app_hash": "Yu3HX62w7orbbY/pm2QEK7yIwR+AlNdjSSqiK1kmuJM=",
                "last_results_hash": "Yu3HX62w7orbbY/pm2QEK7yIwR+AlNdjSSqiK1kmuJM=",
                "evidence_hash": "47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU=",
                "proposer_address": "aCG1hw85Zz7Ylgpsy263IJVJEMA="
            },
            "commit": {
                "height": 22,
                "round": 1,
                "block_id": {
                    "hash": "PKrS32IEZoFY2q2S3iQ68HQL751ieBhf5Eu/Y5Z/QPg=",
                    "part_set_header": {
                        "total": 1,
                        "hash": "8UuA7Oqw5AH/KOacpmHVSMOIDe4l2eC8VmdH2mzcpiM="
                    }
                },
                "signatures": [
                    {
                        "block_id_flag": 2,
                        "validator_address": "aCG1hw85Zz7Ylgpsy263IJVJEMA=",
                        "timestamp": "2023-11-20T12:57:44.076538Z",
                        "signature": "bSOH4+Vg2I37zeJphOguGOD0GK3JzM1ghSgJd0UlW/DHn1u9Hvv4EekHuCu6qwRLZcuS/ZxNlmr9qYNfxX3bDA=="
                    },
                    {
                        "block_id_flag": 2,
                        "validator_address": "i/A830FM7cfmA8yTn9n3xBg5XpU=",
                        "timestamp": "2020-01-02T00:07:00Z",
                        "signature": "7bXSDtlOwGK/gLEsFpTWOzm2TFoaARrWQUpbgWEwKtLlUs7iE06TOvJ3yPPfTfqqN/qYnvxxgjl0M0EhUWu5Bg=="
                    },
                    {
                        "block_id_flag": 2,
                        "validator_address": "lrQDkJ2fk7UAgNzRZfcwMKSYa2E=",
                        "timestamp": "2023-11-20T12:57:44.076519Z",
                        "signature": "Pb6G4bCg4wafmV89WNnzXxbSCknZUHnSQfSCE5QMFxPtSUIN4A7SK5m7yltqMJF5zkyenlFiEI4J3OZ4KCjCAw=="
                    },
                    {
                        "block_id_flag": 2,
                        "validator_address": "+R94nXSeM1Z49e/CXpyHT3M+h3k=",
                        "timestamp": "2023-11-20T12:57:44.057451Z",
                        "signature": "j3EasIHNYA6MxW/PiWyruzHsjVsBV9t11W6Qx800WMm/+P+CkfR+UZAp7MPTvKZEZFuh3GUsBtyfb/vA+jJWCw=="
                    }
                ]
            }
        },
        "validator_set": {
            "validators": [
                {
                    "address": "aCG1hw85Zz7Ylgpsy263IJVJEMA=",
                    "pub_key": {
                        "ed25519": "dtn+SfD+4QLo0+t0hAoP6Q2sGjh0XEI3LWVG+doh3u0="
                    },
                    "voting_power": 100,
                    "proposer_priority": -200
                },
                {
                    "address": "lrQDkJ2fk7UAgNzRZfcwMKSYa2E=",
                    "pub_key": {
                        "ed25519": "UgN2JsjPy2WLh7dzJRBkUQtdgNoT4/uGj7kbIVqqHT8="
                    },
                    "voting_power": 100,
                    "proposer_priority": 100
                },
                {
                    "address": "+R94nXSeM1Z49e/CXpyHT3M+h3k=",
                    "pub_key": {
                        "ed25519": "5svW8261x+cZosp2xIhqzgt2tyuawrSDyHlpbgS3BC4="
                    },
                    "voting_power": 100,
                    "proposer_priority": 100
                },
                {
                    "address": "aCG1hw85Zz7Ylgpsy263IJVJEMA=",
                    "pub_key": {
                        "ed25519": "dtn+SfD+4QLo0+t0hAoP6Q2sGjh0XEI3LWVG+doh3u0="
                    },
                    "voting_power": 100,
                    "proposer_priority": -200
                }
            ],
            "proposer": {
                "address": "VUz+QceJ8Nu7GbJuVItwsfVjybA=",
                "pub_key": {
                    "ed25519": "0s8KDTgEcwmOBrHWvV7mtBlItJ3upgM1FJsciwREdy4="
                },
                "voting_power": 1,
                "proposer_priority": -3
            }
        },
        "trusted_height": {
            "revision_height": 18
        },
        "trusted_validators": {
            "validators": [
                {
                    "address": "VUz+QceJ8Nu7GbJuVItwsfVjybA=",
                    "pub_key": {
                        "ed25519": "0s8KDTgEcwmOBrHWvV7mtBlItJ3upgM1FJsciwREdy4="
                    },
                    "voting_power": 1,
                    "proposer_priority": -3
                },
                {
                    "address": "i/A830FM7cfmA8yTn9n3xBg5XpU=",
                    "pub_key": {
                        "ed25519": "FCmIw7hSuiAoWk/2f4LuGQ+3zx5101xiqU8DoC5wGkg="
                    },
                    "voting_power": 1,
                    "proposer_priority": 1
                },
                {
                    "address": "2DrZF0roNnnvEy4NS2aY811ncKg=",
                    "pub_key": {
                        "ed25519": "MI9c6sphsWlx0RAHCYOjMRXMFkTUaEYwOiOKG/0tsMs="
                    },
                    "voting_power": 1,
                    "proposer_priority": 1
                },
                {
                    "address": "73aN0uOc5b/Zfq2Xcjl0kH2r+tw=",
                    "pub_key": {
                        "ed25519": "gWNcDup4mdnsuqET4QeFRzVb+FnSP4Vz3iNMj5wvWXk="
                    },
                    "voting_power": 1,
                    "proposer_priority": 1
                }
            ],
            "proposer": {
                "address": "VUz+QceJ8Nu7GbJuVItwsfVjybA=",
                "pub_key": {
                    "ed25519": "0s8KDTgEcwmOBrHWvV7mtBlItJ3upgM1FJsciwREdy4="
                },
                "voting_power": 1,
                "proposer_priority": -3
            }
        }
    }
    ```
    </div>
  </div>
</details>

Use the following command to submit evidence of light client attacks:
```bash
gaiad tx provider submit-consumer-misbehaviour [path/to/misbehaviour.json] --from node0 --home ../node0 --chain-id $CID
```

### Report equivocation infractions with Hermes

Ensure you have a well-configured Hermes `v1.7.3+` relayer effectively relaying packets between a consumer chain and a provider chain. 
The following command demonstrates how to run a Hermes instance in _evidence mode_ to detect misbehaviors on a consumer chain and automatically submit the evidence to the provider chain.
```bash
hermes evidence --chain <CONSUMER-CHAIN-ID>
```

:::tip
`hermes evidence` takes a `--check-past-blocks` option giving the possibility to look for older evidences (default is 100).
:::