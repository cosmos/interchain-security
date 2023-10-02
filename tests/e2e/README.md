## Updating the trace format and tests when adjusting the framework

Some things in the test framework should stay consistent, in particular with respect to the trace format.
When adding or modifying actions, please follow these guidelines:
* Add a case for your action to `main.go`
* Add a case for your action to `json_utils.go/UnmarshalMapToActionType`
* Add a generator for your action to `action_rapid_test.go` and add the generator to `GetActionGen`

If the chain state from `state.go` is modified, the `ChainStateWithProposalTypes` in `json_utils.go/MarshalJSON` should be updated.

When adding a new proposal type:
* add a case for your proposal type to `json_utils.go/UnmarshalProposalWithType`
* add a generator for your proposal type in `state_rapid_test.go` and add it to the `GetProposalGen` function 