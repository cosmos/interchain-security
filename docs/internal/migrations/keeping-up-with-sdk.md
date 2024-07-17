# Keeping up with CosmosSDK releases

Our general approach for minor version cosmos-sdk upgrades (e.g. v0.47.x -> v0.50.x):
Cosmos-sdk and IBC are updated at the same lockstep. This is done because every ibc-go version has a corresponding cosmos-sdk version.

Our process starts with a "spike" phase that is capped at 2 weeks. During this "spike" we attempt the upgrade by bumping the deps and checking if the upgrade is smooth. This phase can be extended, depending on the complexity of the upgrade.

This allows us to detect any unforeseen issues and triage them before committing to a release date.

Upon the completion of the "spike", most of our custom application logic (modules) is already upgraded and functioning and that leaves us in a state where we have to modify the testing frameworks, app boilerplate and various other auxiliary systems (CI pipelines etc.).

This phase as involves a lot of manual work and rewrites. One significant time drain is due to the need to update most of the test files to reflect API changes. Sometimes the tests need to be rewritten to be updated because of the amount of breaking changes.

## Methodology

We found it most efficient to always have a development branch that includes the latest cometbft/cosmos-sdk/ibc-go changes. This branch is continually updated and part of CI integrations.

This does not come without issues, becasue the branch needs to be kept in sync with the main branch. Essentially, this forces you to backport features into the development branch so it is ready to be marked as `main` at all times.

## Affected dependencies
* cosmos-sdk
* cometbft
* ibc-go
* cosmwasm

## Areas of work

### Application libraries

Major deps upgrades cause breaking changes in the chain's custom application logic. These changes often require need manual attention (code changes) and corresponding migrations

### 

In case of deps upgrades, it is sometimes required to write custom migration code. Some changes are outlined in the cosmos-sdk/ibc-go upgrade documentation, but oftentimes this is left up to the chain's developers.


### Managing forks
In case of deps upgrades, it is sometimes required to write custom migration code on your forks.
We recommend frequent syncs with the released mainline version.


## Updating app boilerplate
This is usually the least time-consuming phase. Extra attention should be paid to IBC transfer stacks, order of execution in BeginBlock and EndBlock and similar. Linting tools are very helful in automating this process.
