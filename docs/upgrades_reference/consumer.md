# consumer app
```go
func (k Keeper) UpdateSlashingSigningInfo(ctx sdk.Context)
```
* GetValidatorSigningInfo has extra panics that were not there before

In `app/consumer/app.go` the configuration options were updated to allow using a different consumer chain address prefix:
```go
func init() {
	...
	cfg := sdk.GetConfig()
	cfg.SetBech32PrefixForAccount(Bech32MainPrefix, Bech32MainPrefix+"pub")
	cfg.SetBech32PrefixForValidator(Bech32MainPrefix+"valoper", Bech32MainPrefix+"valoperpub")
	cfg.SetBech32PrefixForConsensusNode(Bech32MainPrefix+"valcons", Bech32MainPrefix+"valconspub")
	cfg.Seal()
}
```