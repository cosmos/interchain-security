
# PSS: reward distribution design proposal

## Provider states

### x/ccv/provider

- in-store: consumer chain Id -> opted-in validators mapping
- in-store: consumer chain Id -> module account (reward fee pool) mapping  
- code constant: consumer reward pools / module account name list
- in-store: last consumer module account index assigned

### x/banking

- consumer module account balances
- community fee pool balance (x/distr module account balance)

### x/auth

- consumer module accounts

### ABCI

- previous block validator votes used as an input to calculate the validators reward allocations (abci.CommitInfo)

### IBC packet

- handshake metadata storing the consumer reward fee pool, i.e. assigned module account on the provider

### Actions

- Provider app startup:

  - Module accounts are created from the consumer reward pool list

- Provider App runtime:

  - for each consumer addition proposal that passes, assign a reward pool to the associated consumer chain
  - when a consumer chain completes the CCV handshake, send the reward pool address of the consumer in the handshake ACK packet
  - In enblock:
    - for each consumer reward pool
      - filter fees using denoms whitelist
      - send to distribution module account
      - compute community and validators rewards
      - allocate tokens to community pool and tokens

- Consumer app runtime (unchanged):
  - After distribution period each block transfers fees collected to consumer reward pool



## Questions:

- Should the consumer module accounts rather be stored as a code constant or a states?

- Reward "pool" Naming conventions:

    - In the SDK, the  community pool refers to a FeePool type struct that tracks the validators rewards.
    The distribution module account holds the tokens and tracks the validator rewards using different states.
    - In PSS, the consumer reward are received through an IBC transfers. That entails that it's hard to define from which consumer sent the reward.
    - How can we determine for how long a validator opted in?
    - Ask SDK the security
