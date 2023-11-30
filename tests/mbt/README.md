# Model-based testing for the Cross-Chain Validation protocol

This folder contains the model-based testing (MBT) framework that we use to test the Cross-Chain Validation (CCV) protocol.

The basic idea is that it is hard to test that protocols make sense and fulfill desired properties just by
looking at them hard. Typically, we give these requirements as
*invariants* should hold for the protocol. For example, a property of the CCV protocol is
that the validator set on the consumer chains should always be or have been a validator set on the provider chain.
This is a property that we can express as an invariant.
However, it is pretty hard to check that this invariant holds just by looking at the protocol.

 This is where languages like Quint come in:
Quint is amenable to *model-checking*, which means that when we write a specification (equivalently called model)
in Quint, we can use tools like Apalache to automatically check whether invariants hold in *all*
possible traces (up to a certain length).

This is different from property-based testing: there, we generate random traces and check that the invariants hold
for these traces. Property-based testing is a good way to find bugs, but it is not a good way to prove that a protocol is correct -
because the state space of the protocol is extremely large, we can't hope to cover it all with random traces.
Model-checking is great at this, because it provides a systematic way to check all possible traces,
and it can even help when there are infinitely many possible traces (that is the power of formal logic!).

So now let's assume we have modelled the CCV protocol in Quint, we have written some invariants, and model-checking
gave us confidence that the protocol is correct. Unfortunately, the model we have just checked is *not* the actual implementation.
Thus, the missing step is to check that the actual implementation behaves like the model.
We do this by randomly generating traces in the model, and then running the same traces against the actual implementation,
while checking that the actual system behaves like the model.

The way we gain confidence is then:
* We model-check the Quint model to ensure it satisfies desirable properties...
* ...and we run the model against the actual implementation to ensure the actual implementation behaves like the model...
* ...so the actual implementation also satisfies the desirable properties.

## Limitations

#### Models are more abstract than implementations

Despite the fact that we can gain confidence in the actual implementation by running it against the model,
the model *is not* the same as the implementation.
In part, this is on purpose - we want to model the protocol, not the implementation.
This means we typically model protocols at a higher level of abstraction than the implementation.
For example, in the model, we don't model the whole of IBC, but we instead make some
assumptions about how IBC works, and we model the protocol on top of these assumptions.

This limitation means that MBT cannot replace diligent unit and end-to-end testing, but it can add value to them.

#### Model-checking has limits

Model-checking is a powerful tool, but it suffers from the state-space explosion problem.
We typically parameterize models, e.g. the number of consumer chains is a parameter of the CCV model.
It is typically not possible to check protocols for large instantiations of such parameters (say, with 100 consumer chains) 
because the state space gets too large.
Similarly, we can typically not model-check the protocol for very long traces.
Throwing more computational power at the problem can push the boundary forward, but
it does not solve the underlying problem that model-checking is inherently a computationally hard problem.

The counterpoint to these concerns is that for most real protocols,
invariant violations appear even with short traces and small parameter values, because we
indeed check *all* short traces.

However, the limitations inherent to model-checking are still real, and we need to be aware of them.

## File structure

* `model` contains the Quint model
* `driver` contains the driver, which is the instrumentation code that runs and checks the model against the actual implementation.

See the readmes in the specific folders for more information.