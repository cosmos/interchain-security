#!/bin/bash

quint test ccv_model.qnt
quint test ccv_test.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 200 --max-samples 200