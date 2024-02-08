#!/bin/bash

<<<<<<< HEAD
# to stop on any errors
set -e

quint test ccv_model.qnt
quint test ccv_test.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 200 --max-samples 200
quint run --invariant "all{ValidatorUpdatesArePropagatedKeyAssignmentInv,ValidatorSetHasExistedKeyAssignmentInv,SameVscPacketsKeyAssignmentInv,MatureOnTimeInv,EventuallyMatureOnProviderInv,KeyAssignmentRulesInv}" ccv_model.qnt --step stepKeyAssignment --max-steps 200 --max-samples 200


# do not stop on errors anymore, so we can give better output if we error
set +e

run_invariant() {
  local invariant=$1
  local step=$2
  local match=$3

  if [[ -z "$step" ]]; then
    quint run --invariant $invariant ccv_model.qnt | grep -q $match
  else
    quint run --invariant $invariant --step $step ccv_model.qnt | grep -q $match
  fi

  if [[ $? -eq 0 ]]; then
    echo "sanity check $invariant ok"
  else
    echo "sanity check $invariant not ok"
    exit 1
  fi
}

run_invariant "CanRunConsumer" "" '[violation]'
run_invariant "CanStopConsumer" "" '[violation]'
run_invariant "CanTimeoutConsumer" "" '[violation]'
run_invariant "CanSendVscPackets" "" '[violation]'
run_invariant "CanSendVscMaturedPackets" "" '[violation]'
run_invariant "CanAssignConsumerKey" "stepKeyAssignment" '[violation]'
run_invariant "CanHaveConsumerAddresses" "stepKeyAssignment" '[violation]'
run_invariant "CanReceiveMaturations" "stepKeyAssignment" '[violation]'
=======
quint test ccv_model.qnt
quint test ccv_test.qnt
quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 200 --max-samples 200
quint run --invariant "all{ValidatorUpdatesArePropagatedKeyAssignmentInv,ValidatorSetHasExistedKeyAssignmentInv,SameVscPacketsKeyAssignmentInv,MatureOnTimeInv,EventuallyMatureOnProviderInv,KeyAssignmentRulesInv}" ccv_model.qnt --step stepKeyAssignment --max-steps 200 --max-samples 200
>>>>>>> 6e075652 (test: MBT: Add partial set security to model (feature branch version) (#1627))
