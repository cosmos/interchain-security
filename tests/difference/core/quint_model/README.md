This folder contains a Quint model for the core logic of Cross-Chain Validation (CCV).

### File structure
The files are as follows:
- ccv.qnt: Contains the type definitions, data structures, functional logic for CCV.
The core of the protocol.
- ccv_statemachine.qnt: Contains the state machine layer for CCV. Very roughly speaking, this could be seen as "e2e tests".
Also contains invariants.
- ccv_test.qnt: Contains unit tests for the functional layer of CCV.
- libraries/*: Libraries that don't belong to CCV, but are used by it.

### Model details

To see the data structures used in the model, see the `ProtocolState` type in ccv.qnt.

The "public" endpoints of the model are those functions that take as an input the protocol state, and return a `Result`.
Other functions are for utility.

The parameters of the protocol are defined as consts in [ccv.qnt](ccv.qnt).

### Tests

To run unit tests, run 
```
quint test ccv_test.qnt
```
and 
```
quint test ccv_statemachine.qnt
```

### Invariants

The invariants to check are in [ccv_statemachine.qnt](ccv_statemachine.qnt).
Check a single invariant by running
`quint run --invariant INVARIANT_NAME ccv_statemachine.qnt`,
or all invariants one after another with the help of the script `run_invariants.sh`.
Each invariant takes about a minute to run.

Invariants are as follows:
- [X] ValidatorUpdatesArePropagatedInv: When a validator power update is comitted on chain, a packet containing that change in voting power is sent to all running consumers.
- [X] ValidatorSetHasExistedInv: Every validator set on consumer chains is/was a validator set on the provider.
- [X] SameVscPacketsInv: Ensure that consumer chains receive the same VscPackets in the same order.
Because of nuances with starting/stopping consumers, this invariant is not as simple as it sounds. In detail:
For consumer chains c1, c2, if both c1 and c2 received a packet p1 sent at t1 and a packet p2 sent at t2,
then both have received ALL packets that were sent between t1 and t2 in the same order.
- [X] MatureOnTimeInv: For every ValidatorSetChangePacket received by a consumer chain at 
time t, a MaturedVscPacket is sent back to the provider in the first block 
with a timestamp >= t + UnbondingPeriod on that consumer.
- [X] EventuallyMatureOnProviderInv: If we send a VscPacket, this is eventually responded to by all consumers
that were running at the time the packet was sent (and are still running).

Invariants can also be model-checked by Apalache, using this command:
```
quint verify --invariant ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv \
 ccv_statemachine.qnt
```

### Sanity Checks

Sanity checks verify that certain patterns of behaviour can appear in the model.
In detail, they are invariant checks that we expect to fail.
They usually negate the appearance of some behaviour, i.e. `not(DesirableBehaviour)`.
Then, a counterexample for this is an example trace exhibiting the behaviour.

They are run like invariant checks, i.e. `quint run --invariant SANITY_CHECK_NAME ccv_statemachine.qnt`.
The available sanity checks are:
- CanRunConsumer
- CanStopConsumer
- CanTimeoutConsumer
- CanSendVscPackets
- CanSendVscMaturedPackets