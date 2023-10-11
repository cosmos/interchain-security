#! /bin/sh

quint test ccv_statemachine.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_statemachine.qnt --max-steps 500 --max-samples 200