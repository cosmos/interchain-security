- Introduce new CLI commands and gRPC endpoints to interact with the Permissionless ICS logic. All commands listed below assume the prefix `interchain-security-pd tx|q provider`.

  - **Transactions (TXs):**

    | Command                                | Description                                                   |   Message                                                                                                 | Replaces Proposal              |
    |----------------------------------------|---------------------------------------------------------------  |---------------------------------------------------------------------------------------------------------|--------------------------------|
    | `create-consumer [consumer-parameters]`| Create a new consumer chain.                                   | [MsgCreateConsumer](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L360) |   [ConsumerAdditionProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L31)            |
    | `update-consumer [consumer-parameters]`| Update an existing consumer chain (e.g., spawn time, allowlist)| [MsgUpdateConsumer](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L382) |   [ConsumerModificationProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L140)        |
    | `remove-consumer [consumer-id]`        | Remove a consumer chain.                                       | [MsgRemoveConsumer](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/tx.proto#L226) |   [ConsumerRemovalProposal](https://github.com/cosmos/interchain-security/blob/feat/permissionless/proto/interchain_security/ccv/provider/v1/provider.proto#L122)             |

    > These new TX commands should be used instead of their corresponding deprecated proposals. To update consumer chains owned by the governance module, a proposal containing a `MsgUpdateConsumer` message must be submitted.

  - **Queries:**

    | Command                                 | Description                                                      | gRPC   Endpoint                                         |
    |-----------------------------------------|------------------------------------------------------------------  |------------------------------------------------------|
    | `consumer-chain [consumer-id]`          | Retrieve details of a consumer chain associated with the consumer ID. | `/interchain_security/ccv/provider/consumer_chains`   |
    | `consumer-id-from-client-id [client-id]`| Get the consumer ID of a chain from a client ID.                  | `/interchain_security/ccv/provider/consumer_id/{client_id}` |
    | `blocks-until-next-epoch`               | Query the number of blocks remaining until the next epoch begins. | `/interchain_security/ccv/provider/blocks_until_next_epoch` |

- Improve the `list-consumer-chains` query to accept optional parameters `[phase]` and `[limit]`:
  - `[phase]`: Filters returned consumer chains by their phase.
  - `[limit]`: Limits the number of consumer chains returned.  

([\#2171](https://github.com/cosmos/interchain-security/pull/2171))
