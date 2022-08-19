# Differential testing for Interchain Security 'core' protocol

This directory contains model and trace generation code for the differential approach to testing Interchain Security. In particular, this work is used to test 'core' features of the protocol.

## Scope

### Tested (Unchecked means that work is in progress. Checked means the work is complete.)

The following aspects of the system are tested

- [x] Sending VSC packets from provider to one consumer
- [x] Sending VSC maturities from one consumer to provider
- [x] The bond-based-consumer-voting-power property
- [x] Slashing logic (not including actual token burning)
- [x] Validator power change
- [x] Validators leaving or joining the active validor set
- [x] Consumer initiated slashing
- [x] Delegation operations
- [x] Undelegation operations
- [x] Validator unbonding
- [x] Valiator jailing
- [x] Validator tombstoning
- [x] Packet acknowledgements
- [ ] Redelegation operations
- [ ] Unjailing operations

### NOT Tested

The following aspects of the system are not tested by this work.

- Completing the IBC handshakes
- Repairing an expired IBC channel through governance
- Slashing with non-zero slash factors
- Submitting proposals
- Executing proposals
- Adding a new consumer chain
- Removing a consumer chain for any reason
- Distribution of rewards
- Provider Governance
- Consumer Governance/Democracy
- Anything to do with cosmwasm
- Client timeouts or expiry
- Restarting any chain from exported state
- Any logic that deals with having _more than one consumer chain_

## Usage

### Overview

This typescript project contains code for

- Modelling the aspects of the system listed under TESTED above
- Generating and executing actions against a model system based on those aspects, in order to explore various behaviors. The actions are generated using heuristics and randomness.
- Recording traces of executions to file
- Choosing a set of traces in a manner convenient for testing the SUT.
- Replaying a given existing trace against a new model instance, for debugging purposes.

### Usage prerequisities

```bash
# nodejs version 16 is required.
node --version
# yarn package manager is required
yarn --version
# setup the project
yarn install
```

### Commands

There are several top level yarn project scripts which can be run via

```bash
yarn <script_name>
```

as per the `scripts` entry in [package.json](./package.json). The most important of these are

```bash
# install the project
yarn install;
# build in watch mode. Repeatedly build the project when the src changes
# recommended to run in background process
yarn build:watch
# start main.ts - the entry point to the program
yarn start <args>
# test - run the tests in __tests__
yarn test
```

The actual functionality has entrypoint in [src/main.ts](./src/main.ts). Please see the file for details. The available functionalities are

```bash
# generate traces
yarn start gen <num minutes>
# create a subset of traces
yarn start subset <output file abs path> <num event instances (optional)>
# replay a trace from a file (for debugging)
yarn start replay <filename> <trace index> <num actions>
```

### Workflow

A workflow of updating the model and generating new traces for testing against the SUT might look like

```bash
# Generate traces for 2 minutes
yarn start gen 2
# Collect and compact a subset of these traces
yarn start subset <abs path to x/ccv/difftest/traces.json> 20
```

### Extending the model

All of the semantic logic of the model that relates to how the system is supposed to work is contained in [src/model.ts](./src/model.ts). All of the logic for generating actions (and thus traces) against the model is contained in [src/main.ts](./src/main.ts). The remaining files are less important.

### Ensuring a consistent Trace format

The golang test driver must be able to parse the traces output by this Typescript project. Several tools exist to generate golang type definitions from json files. I strongly suggest using [gojsonstruct](https://github.com/twpayne/go-jsonstruct) to generate a new golang definition whenever the json trace format changes. The steps to do this are

```bash
# Pass the content of traces.json to gojsonstruct binary which will output a golang type definition
gojsonstruct < <traces.json> > trace.go
```

The `trace.go` file output from the above command should be reconciled with the content in `difftest/trace.go`.
