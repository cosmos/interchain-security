# End-to-end testing

This folder contains end-to-end tests and related infrastructure.
The goal of end-to-end tests is to test our application completely.
End-to-end in this context means tests
where the whole app (including command line interfaces, interfaces to external components like
relayers, CometBFT, etc) is in scope for testing.

End-to-end tests should tyoically be used only to perform basic sanity checks that the provided
APIs and protocols work as expected.
For more detailed tests, like exhaustively testing edge cases,
utilize in-memory tests.
The reasoning behind this is that end-to-end tests
make it harder to actually locate errors, and are more brittle and might need to be changed extensively
when unrelated components change.
End-to-end tests can still be useful, and we need them,
but when possible, we should prefer more local tests.

At a high-level, every test case consists of the following steps.
* The test starts a docker container, see [the startup script](testnet-scripts/start-docker.sh)
* We run a defined sequence of actions and expected states, see as an example the steps for [testing the democracy module](steps_democracy.go)
    * Actions are any event that might meaningfully modify the system state, such as submitting transactions to a node, making nodes double-sign, starting a relayer, starting a new chain, etc.
    * Expected states define the state we expect after the action was taken.
    We might specify what we expect the balances of validators to be,
    which chains are running, etc.
    We don't have to specify a complete state after each step, but instead we only
    specify the parts of the state we care about.
    For example, after an action that sends tokens from one validator to another,
    we would usually just specify the expected, new validator balances,
    but not check what chains are currently running.
* After each action, the state of the system is queried and compared against the expected state.

## Running e2e tests

If you just want to run the end-to-end tests,
see the commands in the Makefile in the repo root.

If you want to run the tests with a bit more control, see the help by running 
```go run ./tests/e2e/... --help```
in the repo root to see how to do that.

## Defining a new test case

This section explains how to define a new test case. For now, let's assume that
all actions and state checks we want to perform already exist (see [actions.go](actions.go)
for possible actions and [state.go](state.go) for possible state checks).
Then what we need to do is the following:
* Create a new test config (or decide on an existing one to reuse), see [config.go](config.go).
The test config governs the config parameters of validators and chains that can be run in the test,
for example we can set the genesis parameters of a chain using `ChainConfig.GenesisChanges`.
* Define a sequence of actions and state checks to perform for our test case.
* Add the new test case to the main file [main.go](main.go).
    * ...in the stepChoices slice, where you need to put your step slice and the test config you want to run your steps on.
    * ...add your test config to the `testConfigs` map (which is used to specify configs when calling from the CLI)
    * ...if your test case should run by default (if you're not sure, it probably should), also add it to the predefined test cases in
    `getTestCases` (which governs which test cases will be run when no specific test case is specified on the CLI)

For example, a short sequence of actions and state checks could look like this:
```
steps := []Step{
    Action: delegateTokensAction{
        Chain:  ChainID("provi"),
        From:   ValidatorID("alice"),
        To:     ValidatorID("alice"),
        Amount: 11000000,
    },
    State: State{
        ChainID("provi"): ChainState{
            ValPowers: &map[ValidatorID]uint{
                ValidatorID("alice"): 511,
                ValidatorID("bob"):   500,
                ValidatorID("carol"): 500,
            },
        },
    },
    Action: delegateTokensAction{
        Chain:  ChainID("provi"),
        From:   ValidatorID("alice"),
        To:     ValidatorID("bob"),
        Amount: 99000000,
    },
    State: State{
        ChainID("provi"): ChainState{
            ValPowers: &map[ValidatorID]uint{
                ValidatorID("alice"): 511,
                ValidatorID("bob"):   599,
                ValidatorID("carol"): 500,
            },
        },
    },
},
```
In this sequence, we first use the `delegateTokensAction`
to delegate 11000000 tokens from alice to herself,
then check that alices voting power was set to 511 (note that 11000000 stake=11 voting power here),
then afterwards use the same action again, this time to delegate 99000000
tokens from alice to bob, and again check the voting powers, with the change that
bobs voting power should now be 599.

For most steps, we can reuse existing code, for example
the actions necessary to start a provider and multiple consumer chains
are already "packaged together" and available as
`stepsStartChains` in [steps_start_chains.go](steps_start_chains.go).

**Note:** The parts of the state that are *not* defined are just *not checked*. 
For example, if the balance of a validator is not listed in a state, it means we
do not care about the balance of that validator in this particular state.

### How to use relayers

For relayers, there are currently several actions defined.
There are some subtleties here.

* `addChainToRelayer` gives the relayer the config for the chain and should be called before the relayer is expected to interact with the chain for the first time.
* `createIbcClientsAction`, `addIbcConnectionAction` and `addIbcChannel` are used to create clients, connections and channels.
* `relayPackets` relays all *currently queued* packets and their acknowledgements.
* `startRelayer` starts the relayer, which means from now on, it will *automatically relay all packets*.
Before `startRelayer`, it's possible to let packets queue up and not clear them.
Afterwards, *all packets* will be relayed immediately, so it's no longer possible
to e.g. delay the relaying of a packet.


## Defining new actions

It is necessary to define new actions when we want to test something that does not yet have the corresponding actions defined.
For example, a new feature may introduce new transactions, and
there is likely no existing action to submit these transactions to the chain.

You can see the basic template for how to do this by looking at the actions in
[actions.go](actions.go).
The basic principle is to use `exec.Command` to execute a command inside the docker container.
The pattern for this looks something like this:
```
cmd := exec.Command("docker", "exec", 
    tr.containerConfig.InstanceName,
    tr.chainConfigs[action.Chain].BinaryName,
    "the command to execute, for example tx",
    "argument 1",
    "argument 2")
output, err := cmd.CombinedOutput()
if err != nil {
    log.Fatal(err, "\n", string(bz))
}

// potentially check something in the output, or log something, ...
```

Don't forget to wire your action into [main.go](main.go):runStep, where
the action structs and functions to run for each of them are wired together.

**Note:** Actions don't need to check that the state was modified correctly,
since we have the state checks for this.
Still, it's generally a good idea to do a basic check for errors,
since in case the action encounters an error,
we'd rather fail inside the action and immediately know something went wrong,
rather than just getting a non-matching state during the state check that happens after the action.

### Gas
When submitting transactions, generally either specify a large enough amount of gas manually,
or use `--gas=auto` with a large `--gas-adjustment` (1.5 seems pretty safe).
You should avoid situations where transactions non-deterministically sometimes
work and sometimes fail due to gas, as can happen with `--gas=auto` and no `--gas-adjustment` (or gas adjustment too close to 1).
Essentially, sometimes the gas estimation will underestimate gas, but not always -
it seems to be non-deterministic, and probably depends on subtle things like
block times, or heights, which are not finely controlled in the end-to-end tests
and do not perfectly match each time. 
To be sure we don't introduce nondeterminism like this,
we need to use a sufficient adjustment to make sure there is enough gas for transactions to pass.

### Waiting for blocks/time

To wait for blocks to be produced or for time to pass,
you should avoid writing your own logic, and reuse the existing
utility functions `testConfig.waitBlocks` and `testConfig.WaitTime`.
These already take care of subtleties, like `WaitTime` working with
[CometMock](https://github.com/informalsystems/CometMock) to
advance the time instead of sleeping.

## Defining new state checks

When we want to check a part of the state that was never accessed before, it
might be necessary to define a new state check.
This is done by adding new fields to `ChainState` in [state.go](state.go).

We also need to populate the newly added fields by querying the actual system state,
which is done in `getChainState`.
Typically, this is ultimately done, like actions, by issuing commands to the chain binary
inside the docker container. See how this is done e.g. for `getBalance`.

## Traces

It is possible to dump the test cases (in the form of actions+state checks)
to files and read them from files, instead of just having them defined inside of Go code.
The reasoning behind this is that
with this, it becomes possible to generate test traces e.g. outside of
the Go code via other tools.
You should not need to write these json files by hand.
If you want to just write an end-to-end test, write it inside the
Go files, as outlined above.

### Updating the trace format and tests when adjusting the framework

Some things in the test framework should stay consistent, in particular with respect to the trace format.
When adding or modifying actions, please follow these guidelines:
* Add a case for your action to `main.go`
* Add a case for your action to `json_utils.go/UnmarshalMapToActionType`
* Add a generator for your action to `action_rapid_test.go` and add the generator to `GetActionGen`

If the chain state from `state.go` is modified, the `ChainStateWithProposalTypes` in `json_utils.go/MarshalJSON` should be updated.

When adding a new proposal type:
* add a case for your proposal type to `json_utils.go/UnmarshalProposalWithType`
* add a generator for your proposal type in `state_rapid_test.go` and add it to the `GetProposalGen` function

### Regenerating Traces

The traces in `tracehandler_testdata` are generated by the test `trace_handlers_test.go/TestWriteExamples`.

You can regenerate them by running `make e2e-traces` in the root of the repo.

### Running against traces

To run a test trace in the e2e tests, run `go run . --test-file $TRACEFILE::$TESTCONFIG`.
See `--help` for more details.

## Debugging and using the e2e infrastructure to set up a testnet

When something in the tests goes wrong, a nice thing about the tests is that the
docker container doesn't get killed.
You can sh into the docker container via e.g. `docker exec -it "testinstance" sh` and manually look around.
Useful pointers are:
* Look at logs in the nodes' home folder, i.e., `/$CHAIN_ID/validator$VAL_ID`
* Query/Run txs on the running apps (find out the relevant addresses and node homes to use e.g. by running `htop "binaryname"`)

To debug an action,
you can temporarily add a very long `time.Sleep` inside the action you are interested in, then sh into the docker container
and e.g. try running the commands from the action yourself to see what happens.