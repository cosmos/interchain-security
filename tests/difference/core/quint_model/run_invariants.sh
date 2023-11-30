#! /bin/sh

quint test ccv_model.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 500 --max-samples 200