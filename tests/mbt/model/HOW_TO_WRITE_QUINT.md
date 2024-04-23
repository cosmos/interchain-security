# How to Quint well

This document is supposed to summarize my experience with writing Quint.
It's meant to be high-level.
If one wants to modify the Quint model here, it is probably a good idea to read this document, to
a) understand why the model is currently structured as is; and
b) understand how to efficiently make changes

This assumes you have a good understanding of the syntax of Quint.
E.g., you know what a "step" action is.

### Functional layer and state machine layer separation

The most important thing I have learned about writing Quint models so far:
*Split the functional layer and the state machine layer*

The basic pattern looks like this:

Basic functional layer (here, ccv.qnt)
```
// functional layer defines all the state of your protocol
type State = {...}

// Very useful to have a way to define an empty, default state object
pure def EmptyState(): State = {...}

// Functional layer defines a result object,
// which is returned by the "API layer" inside the functional layer.
type Result = {error: string, resultState: State}

// The API of the functional layer looks like this:
// Pure (=stateless) functions that take a current state and some parameters as arguments,
// the returns a result (=either error, or the new state if no error)
pure def DoFoo(currentState: State, a: Param1, b: Param2, c: Param3): Result {
    if(badThing) {
        {error: "something bad happened", resultState: emptyState}
    }
}
```
So the main ingredient of the functional layer are stateless functions that take a current state as input,
then return a result, which is either a new state, or an error explaining why that function can't be applied in the given state.

Basic state-machine layer (here, ccv_model.qnt):
```
// an action that calls Foo and applies the result to the state.
// the action is stateful, it actually accesses the current state, and will set the next state.
action Foo(
    a: Param1,
    b: Param2,
    c: Param3,
) = 
val result = DoFoo(currentState, a, b, c)
all {
    result.hasError() = false, // action will only be executed if there is no error
    currentState' = result.resultState // set the next state
}

// sometimes this layer is useful: does Foo, but resolves the parameters according
// to some nondeterministic choice
action NondetFoo() =
// choose a and b nondeterministically from some sets
nondet a = oneOf(PossibleParam1Values)
nondet b = oneOf(PossibleParam2Values)
// as an example, maybe c is derived deterministically by some function from a and b
val c = ComputeC(a, b)
Foo(a, b, c)

// ... many other actions

// step chooses any of the Nondet actions
action step = any {
    NondetFoo,
    NondetBar,
    ...
}
```

The important thing about the state-machine layer is that it involves nondeterministic choices,
and wraps around the functional layer in a nice way that keeps the two as separated as possible.
The functional layer should contain *no* im-pure (i.e. stateful) definitions.

All impure definitions should be in the the state machine layer.
(Of course, it doesn't need to exclusively contain impure definitions, the state machine layer indeed
sometimes benefits from having utility functions, but all actual protocol logic should be in the functional layer).

#### Benefit

The separation makes it easy to reason about the functional layer:
it's pure functional programming,
the thing you need to care about is how the single function you are writing transforms the current state into the next state,
no need to think about side effects, etc.

### Making traces usable for testing

To make traces usable for testing, it is important to keep all information needed to replay traces.
For starters, there needs to be a way to log what actions were taken.

In the CCV model, in particularly we have:
* a `trace`, which is a list of all actions taken
* an `action` record, which contains the kind of an action (just a string), and also all possible arguments that an action could have.
This is the best way to do this in Quint imo, you just set the parts of the object that are relevant for the action you are taking, all others stay empty.
* a `params` record, which stores all the parameters that are needed to replay the trace, i.e. the set of consumer chains, unbonding periods, etc.

These things "pollute" the state machine layer a bit, since they need to be touched in every action.
A nice separation between state machine and functional layer makes this less annoying.

The `trace` record is also sometimes useful for defining invariants of the form
"if action A is ever taken, then it cannot be taken again", etc,
simply by checking the past trace.

### Abstracting from the implementations

For the Quint model to be maximally useful, it should prioritize readability a lot.
One of the things that I learned (the hard way) was to
construct sets and maps in advance, not incrementally, whenever possible.
This wasn't done consistently throughout the spec, but probably should be.
As an example, for key assignment, in reality only validators with a key assignment would be entered in some data structure,
and other validators implicitly don't have a key assigned.
In the model, it's better to have a map from all validators to their key assignments, and the default
assignment is just the validator assigns their own key to themselves.

We shouldn't care about performance of the model too much, and this is exactly one of the ways in which we can
prioritize readability over performance.

So in general, I'd recommend using idealized data structures that wouldn't be efficient on chain, but are readable and understandable in the model.
In particular, partial maps seem too detailed in general, and should be avoided in favor of full maps that are built
early with default values.

See a nice blog post by Igor Konnov on the topic:
https://konnov.github.io/protocols-made-fun/quint/2024/01/14/maps.html

The takeaway: Especially when modelling something where there is already source code, resist the temptation to
stay too close to the source code in terms of data structures.

### Concrete Style Guide

Some concrete stylistic decisions, where we know things are up-to-debate:

#### .with vs {...old, field1:val1}

There are two possibilities for updating a record in Quint:
```
val newRecord = {...oldRecord, field1: val1, field2: val2}
```
or
```
val newRecord = oldRecord.with("field1", val1).with("field2", val2)
```

We should make a decision. I think the first one is less verbose,
but Marius liked the second one more.

Decision: ???

#### Getters/Setters

In the Quint model, we have a lot of records that are just data structures,
and often we need values from very deep in some record, e.g.
```
currentState.consumerStates.get(sender).outstandingPacketsToProvider
```

This is verbose, and hard to update if we ever change the data structures significantly, e.g.
by adding a new layer of nesting.

It might be better to have getters and setters for most fields,
e.g. 
```
packets = currentState.getOutstandingPacketsToProvider(consumer)
```
and 
```
newState = currentState.setOutstandingPacketsToProvider(consumer, newPackets)
```

However, this could also have problems, e.g. making things less immediately obvious and more abstract, potentially for little benefit.

Decision: ???

### Testing

To test Quint specifications, there are two main ways:
1) Use invariants and the simulator.
2) Write test cases.

My usual way is to write a one or more test cases, then try to formulate invariants and run the simulator.
Typically, I will get some faults that are hard to understand, and I will transform the failures into test cases
in order to understand them better.

### Modularity in Step functions

Sometimes, you might have many different actions,
e.g.
```
votingPowerChange,
optIn,
optOut,
assignKey,
endBlock
```
but essentially, some of these actions are modular.
E.g. it might make sense to have a run where optIn and optOut are not allowed,
or one where assignKey is not allowed, etc.

In this case, it might make sense to have one "step function" per module, e.g.:
```
action stepCommon = any {
    votingPowerChange,
    endBlock
}

action stepOptInOptOut = any {
    optIn,
    optOut
}

action stepAssignKey = any {
    assignKey
}
```

When invoking `quint run`, the `--step` argument can take Quint code.
So for example, we can only enable the common and assignKey modules by running:
```
quint run --step "any{stepCommon, stepAssignKey}"
```

The requirement on these "module steps" is that they should
not need any inputs, e.g. they resolve all nondeterminism inside them.
Otherwise, the `--step` argument would need to be more complicated.

## Nondeterministic Choice from Sets

Sometimes, you want to finely control nondeterminism, e.g. to have different probability distributions.
For example:

```
action goUp(element: E) = {...}

action goDown(element: E) = {...}

action step =
    mySet.map(
        element =>
        nondet x = oneOf(1.to(100))
        if(x < 50) {
            goUp
        } else {
            goDown
        }
    )
```

This is ok, but let's step back one meta-layer.
What if you want to have different step functions with different probability distributions, while reusing as much code
as possible from step?

You might be tempted to pass in a function that generates numbers nondeterministically,
and to have different functions for different probability distributions.
E.g. one could imagine to do this:

```
action step(oracle: () => int) =
    mySet.map(
        element =>
        val x = oracle()
        if(x < 50) {
            element.goUp()
        } else {
            element.goDown()
        }
    )

def mostlyUpOracle(): int = oneOf(1.to(60))

def mostlyDownOracle(): int = oneOf(40.to(100))
```

This is not possible, because of technicalities with nondeterminism.

The basic rule-of-thumb is:
*Nondeterminism can only happen directly in actions*

We are violating this commandment here, because the nondeterminism would happen in the oracle functions.

The solution is to use sets instead of functions.
The idea is that we leave the nondeterministic choice inside the step function, but we do oneOf from a set that is passed in.
E.g.:

```
action step(oracleDomain: Set[int]) =
    nondet x = oneOf(oracleDomain)
    if(x < 50) {
        goUp
    } else {
        goDown
    }

val mostlyUpOracleDomain = 1.to(60)
val mostlyDownOracleDomain = 40.to(100)
```

We could get more complicated distributions by applying a function to x.