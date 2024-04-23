#!/bin/bash

# Check if a seed is provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <seed>"
    exit 1
fi

# The seed provided as the first argument
seed="$1"

# The command from which to extract invariants and the model file (paste your command inside the single quotes)
command='quint run --invariant "all{ValidatorUpdatesArePropagatedInv,ValidatorSetHasExistedInv,SameVscPacketsInv,MatureOnTimeInv,EventuallyMatureOnProviderInv}" ccv_model.qnt --max-steps 200 --max-samples 200'

# Extract the invariants part of the command
invariants_string=$(echo $command | awk -F'--invariant "' '{print $2}' | awk -F'" ' '{print $1}')
# Extract the model file from the command
model_file=$(echo $command | awk '{for(i=1;i<=NF;i++) if ($i ~ /\.qnt$/) print $(i)}')

# Extract max-steps, max-samples, and --step values if they exist
max_steps=$(echo $command | grep -oP '(?<=--max-steps )[^ ]*' || echo "")
max_samples=$(echo $command | grep -oP '(?<=--max-samples )[^ ]*' || echo "")
step_value=$(echo $command | grep -oP '(?<=--step )[^ ]*' || echo "")

# Construct optional arguments
optional_args=""
if [ -n "$max_steps" ]; then
  optional_args+="--max-steps $max_steps "
fi
if [ -n "$max_samples" ]; then
  optional_args+="--max-samples $max_samples "
fi
if [ -n "$step_value" ]; then
  optional_args+="--step $step_value "
fi

# Remove "all{" and "}" from the string, then split by ","
invariants=$(echo $invariants_string | sed 's/all{//g' | sed 's/}//g' | tr ',' '\n')

# Store the results
violated_invariants=()
nonviolated_invariants=()

# Loop over each invariant
while read -r invariant; do
  if [ -z "$invariant" ]; then
    continue
  fi
  
  echo "Checking invariant: $invariant with model file: $model_file"

  # Run the Quint command with the current invariant, model file, and optional arguments
  quint_cmd="quint run --invariant \"$invariant\" $model_file $optional_args--seed=$seed"
  echo "Executing $quint_cmd"
  result=$(eval $quint_cmd)

  # Check if the invariant was violated
  if [[ $result == *"[violation]"* ]]; then
    echo "Invariant violated: $invariant"
    violated_invariants+=("$invariant")
  else
    echo "Invariant not violated: $invariant"
    nonviolated_invariants+=("$invariant")
  fi
done <<< "$invariants"

# Summarize the results
echo "Summary:"
echo "Violated invariants:"
for invariant in "${violated_invariants[@]}"; do
  echo "- $invariant"
done

echo "Non-violated invariants:"
for invariant in "${nonviolated_invariants[@]}"; do
  echo "- $invariant"
done
