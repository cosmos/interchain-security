#!/bin/bash

quint test ccv_model.qnt
quint test ccv_test.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 200 --max-samples 200
quint run --invariant "all{ValidatorUpdatesArePropagatedKeyAssignmentInv,ValidatorSetHasExistedKeyAssignmentInv,SameVscPacketsKeyAssignmentInv,MatureOnTimeInv,EventuallyMatureOnProviderInv,KeyAssignmentRulesInv}" ccv_model.qnt --step stepKeyAssignment --max-steps 200 --max-samples 200
