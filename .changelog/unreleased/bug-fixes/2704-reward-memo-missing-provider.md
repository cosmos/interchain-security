- `[x/types]` Return an error from `GetRewardMemoFromTransferMemo` when the
  transfer memo has no `provider` field, so the provider IBC middleware falls
  back to identifying the consumer from the packet instead of using an empty
  reward memo.
  ([\#2704](https://github.com/cosmos/interchain-security/pull/2704))
