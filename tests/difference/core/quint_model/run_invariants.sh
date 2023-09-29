quint run --invariant ValidatorUpdatesArePropagated ccv_statemachine.qnt --main CCVDefaultStateMachine
quint run --invariant ValidatorSetHasExistedInv ccv_statemachine.qnt --main CCVDefaultStateMachine
quint run --invariant SameVSCPacketsInv ccv_statemachine.qnt --main CCVDefaultStateMachine
quint run --invariant MatureOnTimeInv ccv_statemachine.qnt --main CCVDefaultStateMachine
quint run --invariant EventuallyMatureOnProviderInv ccv_statemachine.qnt --main CCVDefaultStateMachine