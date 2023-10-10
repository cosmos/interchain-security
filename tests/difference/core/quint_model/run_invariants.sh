#! /bin/sh

quint test ccv_statemachine.qnt --main CCVDefaultStateMachine
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_statemachine.qnt --main CCVDefaultStateMachine --max-steps 500 --max-samples 200