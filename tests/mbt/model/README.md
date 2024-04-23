This folder contains a Quint model for the core logic of Cross-Chain Validation (CCV).

## File structure
The files are as follows:
- ccv.qnt: Contains the type definitions, data structures, functional logic for CCV.
The core of the protocol.
- ccv_model.qnt: Contains the stateful part of the model for CCV. Very roughly speaking, this could be seen as "e2e tests".
Also contains invariants.
- ccv_sync.qnt: An extra layer on top of ccv_model.qnt which restricts the traces to only ones where the 
consumer chains and provider chain produce blocks in sync.
- ccv_boundeddrift.qnt: An extra layer on top of ccv_model.qnt which restricts traces to ones where
chains never drift too far apart in time.
- ccv_test.qnt: Contains unit tests for the functional layer of CCV.
- libraries/*: Libraries that don't belong to CCV, but are used by it.

## Model details

To see the data structures used in the model, see the `ProtocolState` type in ccv.qnt.

The "public" endpoints of the model are those functions that take as an input the protocol state, and return a `Result`.
Other functions are for utility.

The parameters of the protocol are defined as consts in [ccv.qnt](ccv.qnt).

### Actions

The model has these actions:
* `VotingPowerChange(validator: Node, changeAmount: int)`: On the provider chain, changes the voting power of the `validator` by `changeAmount`.
* `EndAndBeginBlockForProvider(timeAdvancement: Time, consumersToStart: Set[Chain], consumersToStop: Set[Chain])`: On the provider chain, ends the current block, and begins a new one. Starts the consumer chains in `consumersToStart`, and stops the consumer chains in `consumersToStop`.
All the logic in EndBlock/BeginBlock happens here, like updating the validator set, sending packets, etc.
* `EndAndBeginBlockForConsumer(chain: Chain, timeAdvancement: Time)`: On the consumer `chain`, ends the current block, and begins a new one. Again, all the logic in EndBlock/BeginBlock happens here, like validator set change maturations.
* `DeliverVscPacket(receiver: Chain)`: Delivers a pending VSCPacket from the provider to the consumer `receiver`.
* `DeliverPacketToProvider(sender: Chain)`: Delivers a pending packet from the consumer `sender` to the provider.
* `KeyAssignment(chain: Chain, validator: Node, consumerAddr: ConsumerAddr)` (only when running with `--step stepKeyAssignment`): Assigns the `consumerAddr` to the `validator` on the `chain`. Note that we use "key" and "consumerAddr" pretty much interchangeably, as the model makes no differentiation between private keys, public keys, addresses, etc, as it doesn't model the cryptography.

### State machines

There are 3 different "state machine layers" that can be put on top of the core logic.
Some layers include extra logic, need other invariants, ...

#### ccv_model.qnt
This is the most general state machine layer. It allows the most behaviour,
in particular it allows abitrary clock drift between chains, it allows starting and
stopping consumer chains during runtime, etc.
This layer is most useful for model checking, because it encompasses the most behaviour.
As an optional module, it can also include KeyAssignment.

##### KeyAssignment

To run with key assignment, specify the step flag: `--step stepKeyAssignment`.

KeyAssignment also needs some different invariants, see below.

#### Partial Set Security

To run with Partial Set Security, specify the step flag `--step stepBoundedDriftKeyAndPSS`.
This runs both PSS and Key Assignment.
It also requires running with `ccv_boundeddrift.qnt`, see below.

#### ccv_boundeddrift.qnt
This state machine layer is more restricted to generate more interesting traces:
* It never allows consumer chains to drift more than `MaxDrift` time apart from each other.
In practice, we set `MaxDrift` to be the maximal allowed clock drift/trusting period for light clients.
Then this state machine allows us to not worry about light client expirations, which is important
for generating traces we can run against the real system, because the model doesn't actually model
light client expirations, while in the real system, they can normally happen.
* It might stop consumers during runtime, but only with small probability.
Without this, it becomes very likely that consumer chains are stopped very frequently when generating
traces, which leads to less interesting traces.

##### ccv_sync.qnt
This state machine layer is even more restricted:
* It starts all consumer chains right at the start of the trace, and never stops them.
* It only allows chains to end and begin blocks together.

This is useful for generating happy path traces, but means these
traces are not very useful for testing.


## Tests

To run unit tests, run 
```
quint test ccv_test.qnt;
quint test ccv_pss_test.qnt;
quint test ccv_model.qnt
```

## Invariants

The invariants to check are in [ccv_model.qnt](ccv_model.qnt).
Check a single invariant by running
`quint run --invariant INVARIANT_NAME ccv_model.qnt`,
or all invariants one after another with the help of the script `run_invariants.sh`.
Each invariant takes about a minute to run.

Invariants are as follows:
- [X] ValidatorUpdatesArePropagatedInv: When a validator power update is committed on chain, a packet containing that change in voting power is sent to all running consumers.
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

Invariants only relevant when running with key assignment (`--step stepKeyAssignment`):
- [X] ValidatorSetHasExistedKeyAssignmentInv: Should replace ValidatorSetHasExistedInv when running with `--step stepKeyAssignment`. Validator sets are checked for equality under key assignment when checking whether they have existed.
- [X] SameVscPacketsKeyAssignmentInv: Should replace SameVscPacketsInv when running with `--step stepKeyAssignment`. VscPackets are checked for equality under key assignment when ensuring consumers receive the same ones.
- [X] KeyAssignmentRulesInv: Ensures the rules of key assignment are never violated. The two rules relevant for the model are: 1) validator A cannot assign consumer key K to consumer chain X if there is already a validator B (B!=A)
using K on the provider, and 2) validator A cannot assign consumer key K to consumer chain X if there is already a validator B using K on X


Invariants can also be model-checked by Apalache, using this command:
```
quint verify --invariant ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv \
 ccv_model.qnt
```

## Sanity Checks

Sanity checks verify that certain patterns of behaviour can appear in the model.
In detail, they are invariant checks that we expect to fail.
They usually negate the appearance of some behaviour, i.e. `not(DesirableBehaviour)`.
Then, a counterexample for this is an example trace exhibiting the behaviour.

They are run like invariant checks, i.e. `quint run --invariant SANITY_CHECK_NAME ccv_model.qnt`.
The available sanity checks are:
- CanRunConsumer
- CanStopConsumer
- CanTimeoutConsumer
- CanSendVscPackets
- CanSendVscMaturedPackets
- CanReceiveMaturations
- CanAssignConsumerKey (only with `--step stepKeyAssignment`)
- CanHaveConsumerAddresses (only with `--step stepKeyAssignment`)
- CanOptIn (only with `--step stepBoundedDriftKeyAndPSS` on `ccv_boundeddrift.qnt`)
- CanOptOut (only with `--step stepBoundedDriftKeyAndPSS` on `ccv_boundeddrift.qnt`)
- CanFailOptOut (only with `--step stepBoundedDriftKeyAndPSS` on `ccv_boundeddrift.qnt`)
- CanHaveOptIn (only with `--step stepBoundedDriftKeyAndPSS` on `ccv_boundeddrift.qnt`)
