This folder contains a Quint model for the core logic of Cross-Chain Validation (CCV).

### File structure
The files are as follows:
- ccv.qnt: Contains the type definitions, data structures, functional logic for CCV.
The core of the protocol.
- ccv_statemachine.qnt: Contains the state machine layer for CCV. Very roughly speaking, this could be seen as "e2e tests".
Also contains invariants.
- ccv_test.qnt: Contains unit tests for the functional layer of CCV.
- libararies/*: Libraries that don't belong to CCV, but are used by it.

### Model details

To see the data structures used in the model, see the ProtocolState type in ccv.qnt.

The "public" endpoints of the model are those functions that take as an input the protocol state, and return a Result.
Other functions are for utility.

The parameters of the protocol are defined as consts in ccv.qnt.

### Invariants

The invariants I am checking are in ccv_statemachine.qnt, and are as follows:
- ValidatorUpdatesArePropagated: When a validator power update is comitted on chain, a packet containing that change in voting power is sent to all running consumers. Check via `quint run --invariant ValidatorUpdatesArePropagated ccv_statemachine.qnt --main CCVDefaultStateMachine`