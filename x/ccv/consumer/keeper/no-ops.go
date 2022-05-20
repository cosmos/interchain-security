package keeper

// import (
// 	"time"

// 	sdk "github.com/cosmos/cosmos-sdk/types"
// 	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
// 	"github.com/cosmos/cosmos-sdk/x/staking/types"
// 	abci "github.com/tendermint/tendermint/abci/types"
// )

// // fulfills all the no-ops of staking keeper

// // Load the last total validator power.
// func (k *Keeper) GetLastTotalPower(ctx sdk.Context) sdk.Int {
// 	return sdk.Int{}
// }

// // TODO: confirm OK to stub
// // Set the last total validator power.
// func (k *Keeper) SetLastTotalPower(ctx sdk.Context, power sdk.Int) {}

// // TODO: this is only used as part of IBC test framework, ok to stub?
// // Delegate performs a delegation, set/update everything necessary within the store.
// // tokenSrc indicates the bond status of the incoming funds.
// func (k Keeper) Delegate(
// 	ctx sdk.Context, delAddr sdk.AccAddress, bondAmt sdk.Int, tokenSrc types.BondStatus,
// 	validator types.Validator, subtractAccount bool,
// ) (newShares sdk.Dec, err error) {
// 	return sdk.Dec{}, nil
// }

// // TODO: this is only used as part of IBC test framework, ok to stub?
// // return a given amount of all the validators
// func (k Keeper) GetValidators(ctx sdk.Context, maxRetrieve uint32) (validators []types.Validator) {
// 	return nil
// }
// func (k Keeper) IterateBondedValidatorsByPower(ctx sdk.Context, fn func(index int64, validator types.ValidatorI) (stop bool)) {
// }
// func (k Keeper) IterateLastValidators(ctx sdk.Context, fn func(index int64, validator types.ValidatorI) (stop bool)) {
// }
// func (k Keeper) GetValidatorSet() types.ValidatorSet {
// 	return nil
// }
// func (k Keeper) IterateDelegations(ctx sdk.Context, delAddr sdk.AccAddress,
// 	fn func(index int64, del types.DelegationI) (stop bool)) {
// }
// func (k Keeper) GetAllSDKDelegations(ctx sdk.Context) (delegations []types.Delegation) {
// 	return nil
// }

// // delegation.go
// func (k Keeper) GetDelegation(ctx sdk.Context,
// 	delAddr sdk.AccAddress, valAddr sdk.ValAddress) (delegation types.Delegation, found bool) {
// 	return types.Delegation{}, false
// }
// func (k Keeper) IterateAllDelegations(ctx sdk.Context, cb func(delegation types.Delegation) (stop bool)) {
// }
// func (k Keeper) GetAllDelegations(ctx sdk.Context) (delegations []types.Delegation) {
// 	return nil
// }
// func (k Keeper) GetValidatorDelegations(ctx sdk.Context, valAddr sdk.ValAddress) (delegations []types.Delegation) { //nolint:interfacer
// 	return nil
// }
// func (k Keeper) GetDelegatorDelegations(ctx sdk.Context, delegator sdk.AccAddress,
// 	maxRetrieve uint16) (delegations []types.Delegation) {
// 	return nil
// }
// func (k Keeper) SetDelegation(ctx sdk.Context, delegation types.Delegation) {
// }
// func (k Keeper) RemoveDelegation(ctx sdk.Context, delegation types.Delegation) {
// }
// func (k Keeper) GetUnbondingDelegations(ctx sdk.Context, delegator sdk.AccAddress,
// 	maxRetrieve uint16) (unbondingDelegations []types.UnbondingDelegation) {
// 	return nil
// }
// func (k Keeper) GetUnbondingDelegation(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress,
// ) (ubd types.UnbondingDelegation, found bool) {
// 	return types.UnbondingDelegation{}, false
// }
// func (k Keeper) GetUnbondingDelegationsFromValidator(ctx sdk.Context, valAddr sdk.ValAddress) (ubds []types.UnbondingDelegation) {
// 	return nil
// }
// func (k Keeper) IterateUnbondingDelegations(ctx sdk.Context, fn func(index int64, ubd types.UnbondingDelegation) (stop bool)) {
// }
// func (k Keeper) HasMaxUnbondingDelegationEntries(ctx sdk.Context,
// 	delegatorAddr sdk.AccAddress, validatorAddr sdk.ValAddress) bool {
// 	return false
// }
// func (k Keeper) SetUnbondingDelegation(ctx sdk.Context, ubd types.UnbondingDelegation) {
// }
// func (k Keeper) RemoveUnbondingDelegation(ctx sdk.Context, ubd types.UnbondingDelegation) {
// }
// func (k Keeper) SetUnbondingDelegationEntry(
// 	ctx sdk.Context, delegatorAddr sdk.AccAddress, validatorAddr sdk.ValAddress,
// 	creationHeight int64, minTime time.Time, balance sdk.Int,
// ) types.UnbondingDelegation {
// 	return types.UnbondingDelegation{}
// }
// func (k Keeper) GetUBDQueueTimeSlice(ctx sdk.Context, timestamp time.Time) (dvPairs []types.DVPair) {
// 	return nil
// }
// func (k Keeper) SetUBDQueueTimeSlice(ctx sdk.Context, timestamp time.Time, keys []types.DVPair) {
// }
// func (k Keeper) InsertUBDQueue(ctx sdk.Context, ubd types.UnbondingDelegation,
// 	completionTime time.Time) {
// }
// func (k Keeper) UBDQueueIterator(ctx sdk.Context, endTime time.Time) sdk.Iterator {
// 	return nil
// }
// func (k Keeper) DequeueAllMatureUBDQueue(ctx sdk.Context, currTime time.Time) (matureUnbonds []types.DVPair) {
// 	return nil
// }
// func (k Keeper) GetRedelegations(ctx sdk.Context, delegator sdk.AccAddress,
// 	maxRetrieve uint16) (redelegations []types.Redelegation) {
// 	return nil
// }
// func (k Keeper) GetRedelegation(ctx sdk.Context,
// 	delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress) (red types.Redelegation, found bool) {
// 	return types.Redelegation{}, false
// }
// func (k Keeper) GetRedelegationsFromSrcValidator(ctx sdk.Context, valAddr sdk.ValAddress) (reds []types.Redelegation) {
// 	return nil
// }
// func (k Keeper) HasReceivingRedelegation(ctx sdk.Context,
// 	delAddr sdk.AccAddress, valDstAddr sdk.ValAddress) bool {
// 	return false
// }
// func (k Keeper) HasMaxRedelegationEntries(ctx sdk.Context,
// 	delegatorAddr sdk.AccAddress, validatorSrcAddr,
// 	validatorDstAddr sdk.ValAddress) bool {
// 	return false
// }
// func (k Keeper) SetRedelegation(ctx sdk.Context, red types.Redelegation) {
// }
// func (k Keeper) SetRedelegationEntry(ctx sdk.Context,
// 	delegatorAddr sdk.AccAddress, validatorSrcAddr,
// 	validatorDstAddr sdk.ValAddress, creationHeight int64,
// 	minTime time.Time, balance sdk.Int,
// 	sharesSrc, sharesDst sdk.Dec) types.Redelegation {
// 	return types.Redelegation{}
// }
// func (k Keeper) IterateRedelegations(ctx sdk.Context, fn func(index int64, red types.Redelegation) (stop bool)) {
// }
// func (k Keeper) RemoveRedelegation(ctx sdk.Context, red types.Redelegation) {
// }
// func (k Keeper) GetRedelegationQueueTimeSlice(ctx sdk.Context, timestamp time.Time) (dvvTriplets []types.DVVTriplet) {
// 	return nil
// }
// func (k Keeper) SetRedelegationQueueTimeSlice(ctx sdk.Context, timestamp time.Time, keys []types.DVVTriplet) {
// }
// func (k Keeper) InsertRedelegationQueue(ctx sdk.Context, red types.Redelegation,
// 	completionTime time.Time) {
// }
// func (k Keeper) RedelegationQueueIterator(ctx sdk.Context, endTime time.Time) sdk.Iterator {
// 	return nil
// }
// func (k Keeper) DequeueAllMatureRedelegationQueue(ctx sdk.Context, currTime time.Time) (matureRedelegations []types.DVVTriplet) {
// 	return nil
// }
// func (k Keeper) Unbond(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, shares sdk.Dec,
// ) (amount sdk.Int, err error) {
// 	return sdk.Int{}, nil
// }
// func (k Keeper) getBeginInfo(
// 	ctx sdk.Context, valSrcAddr sdk.ValAddress,
// ) (completionTime time.Time, height int64, completeNow bool) {
// 	return time.Time{}, 0, false
// }
// func (k Keeper) Undelegate(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, sharesAmount sdk.Dec,
// ) (time.Time, error) {
// 	return time.Time{}, nil
// }
// func (k Keeper) CompleteUnbonding(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) (sdk.Coins, error) {
// 	return nil, nil
// }
// func (k Keeper) BeginRedelegation(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress, sharesAmount sdk.Dec,
// ) (completionTime time.Time, err error) {
// 	return time.Time{}, nil
// }
// func (k Keeper) CompleteRedelegation(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valSrcAddr, valDstAddr sdk.ValAddress,
// ) (sdk.Coins, error) {
// 	return nil, nil
// }
// func (k Keeper) ValidateUnbondAmount(
// 	ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress, amt sdk.Int,
// ) (shares sdk.Dec, err error) {
// 	return sdk.Dec{}, nil
// }

// // historical_info.go
// func (k Keeper) IterateHistoricalInfo(ctx sdk.Context, cb func(types.HistoricalInfo) bool) {
// }
// func (k Keeper) GetAllHistoricalInfo(ctx sdk.Context) []types.HistoricalInfo {
// 	return nil
// }

// // hooks.go
// func (k Keeper) AfterValidatorCreated(ctx sdk.Context, valAddr sdk.ValAddress) {
// }
// func (k Keeper) BeforeValidatorModified(ctx sdk.Context, valAddr sdk.ValAddress) {
// }
// func (k Keeper) AfterValidatorRemoved(ctx sdk.Context, consAddr sdk.ConsAddress, valAddr sdk.ValAddress) {
// }

// // func (k Keeper) AfterValidatorBonded(ctx sdk.Context, consAddr sdk.ConsAddress, valAddr sdk.ValAddress) {
// // }
// func (k Keeper) AfterValidatorBeginUnbonding(ctx sdk.Context, consAddr sdk.ConsAddress, valAddr sdk.ValAddress) {
// }
// func (k Keeper) BeforeDelegationCreated(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
// }
// func (k Keeper) BeforeDelegationSharesModified(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
// }
// func (k Keeper) BeforeDelegationRemoved(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
// }
// func (k Keeper) AfterDelegationModified(ctx sdk.Context, delAddr sdk.AccAddress, valAddr sdk.ValAddress) {
// }
// func (k Keeper) BeforeValidatorSlashed(ctx sdk.Context, valAddr sdk.ValAddress, fraction sdk.Dec) {
// }
// func (k Keeper) AfterUnbondingInitiated(ctx sdk.Context, id uint64) {
// }

// // keeper.go
// // func (k Keeper) Logger(ctx sdk.Context) log.Logger {
// // }
// // func (k *Keeper) SetHooks(sh types.StakingHooks) *Keeper {
// // }
// // func (k Keeper) GetLastTotalPower(ctx sdk.Context) sdk.Int {
// // }
// // func (k Keeper) SetLastTotalPower(ctx sdk.Context, power sdk.Int) {
// // }
// func (k Keeper) GetValidatorUpdate(ctx sdk.Context, consAddr sdk.ConsAddress) (abci.ValidatorUpdate, bool) {
// 	return abci.ValidatorUpdate{}, false
// }
// func (k Keeper) HasValidatorUpdate(ctx sdk.Context, consAddr sdk.ConsAddress) bool {
// 	return false
// }
// func (k Keeper) SetValidatorUpdate(ctx sdk.Context, consAddr sdk.ConsAddress, valUpdate abci.ValidatorUpdate) {
// }
// func (k Keeper) GetValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
// 	return nil
// }

// // params.go
// // func (k Keeper) UnbondingTime(ctx sdk.Context) (res time.Duration) {
// // }
// // func (k Keeper) MaxValidators(ctx sdk.Context) (res uint32) {
// // }
// func (k Keeper) MaxEntries(ctx sdk.Context) (res uint32) {
// 	return 0
// }
// func (k Keeper) HistoricalEntries(ctx sdk.Context) (res uint32) {
// 	return 0
// }
// func (k Keeper) BondDenom(ctx sdk.Context) (res string) {
// 	return ""
// }
// func (k Keeper) PowerReduction(ctx sdk.Context) sdk.Int {
// 	return sdk.Int{}
// }

// // func (k Keeper) GetParams(ctx sdk.Context) types.Params {
// // }
// // func (k Keeper) SetParams(ctx sdk.Context, params types.Params) {
// // }

// // pool.go
// func (k Keeper) GetBondedPool(ctx sdk.Context) (bondedPool authtypes.ModuleAccountI) {
// 	return nil
// }
// func (k Keeper) GetNotBondedPool(ctx sdk.Context) (notBondedPool authtypes.ModuleAccountI) {
// 	return nil
// }
// func (k Keeper) bondedTokensToNotBonded(ctx sdk.Context, tokens sdk.Int) {
// }
// func (k Keeper) notBondedTokensToBonded(ctx sdk.Context, tokens sdk.Int) {
// }
// func (k Keeper) burnBondedTokens(ctx sdk.Context, amt sdk.Int) error {
// 	return nil
// }
// func (k Keeper) burnNotBondedTokens(ctx sdk.Context, amt sdk.Int) error {
// 	return nil
// }
// func (k Keeper) TotalBondedTokens(ctx sdk.Context) sdk.Int {
// 	return sdk.Int{}
// }
// func (k Keeper) StakingTokenSupply(ctx sdk.Context) sdk.Int {
// 	return sdk.Int{}
// }
// func (k Keeper) BondedRatio(ctx sdk.Context) sdk.Dec {
// 	return sdk.Dec{}
// }

// // power_reduction.go
// func (k Keeper) TokensToConsensusPower(ctx sdk.Context, tokens sdk.Int) int64 {
// 	return 0
// }
// func (k Keeper) TokensFromConsensusPower(ctx sdk.Context, power int64) sdk.Int {
// 	return sdk.Int{}
// }

// // slash.go
// // func (k Keeper) Slash(ctx sdk.Context, consAddr sdk.ConsAddress, infractionHeight int64, power int64, slashFactor sdk.Dec, _ types.InfractionType) {
// // }
// // func (k Keeper) Jail(ctx sdk.Context, consAddr sdk.ConsAddress) {
// // }
// // func (k Keeper) Unjail(ctx sdk.Context, consAddr sdk.ConsAddress) {
// // }
// func (k Keeper) SlashUnbondingDelegation(ctx sdk.Context, unbondingDelegation types.UnbondingDelegation,
// 	infractionHeight int64, slashFactor sdk.Dec) (totalSlashAmount sdk.Int) {
// 	return sdk.Int{}
// }
// func (k Keeper) SlashRedelegation(ctx sdk.Context, srcValidator types.Validator, redelegation types.Redelegation,
// 	infractionHeight int64, slashFactor sdk.Dec) (totalSlashAmount sdk.Int) {
// 	return sdk.Int{}
// }

// // unbonding.go
// func (k Keeper) IncrementUnbondingId(ctx sdk.Context) (unbondingDelegationEntryId uint64) {
// 	return 0
// }
// func (k Keeper) DeleteUnbondingIndex(ctx sdk.Context, id uint64) {
// }
// func (k Keeper) GetUnbondingDelegationByUnbondingId(
// 	ctx sdk.Context, id uint64,
// ) (ubd types.UnbondingDelegation, found bool) {
// 	return types.UnbondingDelegation{}, false
// }
// func (k Keeper) GetRedelegationByUnbondingId(
// 	ctx sdk.Context, id uint64,
// ) (red types.Redelegation, found bool) {
// 	return types.Redelegation{}, false
// }
// func (k Keeper) GetValidatorByUnbondingId(
// 	ctx sdk.Context, id uint64,
// ) (val types.Validator, found bool) {
// 	return types.Validator{}, false
// }
// func (k Keeper) SetUnbondingDelegationByUnbondingIndex(ctx sdk.Context, ubd types.UnbondingDelegation, id uint64) {
// }
// func (k Keeper) SetRedelegationByUnbondingIndex(ctx sdk.Context, red types.Redelegation, id uint64) {
// }
// func (k Keeper) SetValidatorByUnbondingIndex(ctx sdk.Context, val types.Validator, id uint64) {
// }
// func unbondingDelegationEntryArrayIndex(ubd types.UnbondingDelegation, id uint64) (index int, found bool) {
// 	return 0, false
// }
// func redelegationEntryArrayIndex(red types.Redelegation, id uint64) (index int, found bool) {
// 	return 0, false
// }
// func (k Keeper) UnbondingCanComplete(ctx sdk.Context, id uint64) error {
// 	return nil
// }
// func (k Keeper) unbondingDelegationEntryCanComplete(ctx sdk.Context, id uint64) (found bool, err error) {
// 	return false, nil
// }
// func (k Keeper) redelegationEntryCanComplete(ctx sdk.Context, id uint64) (found bool, err error) {
// 	return false, nil
// }
// func (k Keeper) validatorUnbondingCanComplete(ctx sdk.Context, id uint64) (found bool, err error) {
// 	return false, nil
// }
// func (k Keeper) PutUnbondingOnHold(ctx sdk.Context, id uint64) error {
// 	return nil
// }
// func (k Keeper) putUnbondingDelegationEntryOnHold(ctx sdk.Context, id uint64) (found bool) {
// 	return false
// }
// func (k Keeper) putRedelegationEntryOnHold(ctx sdk.Context, id uint64) (found bool) {
// 	return false
// }
// func (k Keeper) putValidatorOnHold(ctx sdk.Context, id uint64) (found bool) {
// 	return false
// }

// // val_state_change.go
// func (k Keeper) BlockValidatorUpdates(ctx sdk.Context) []abci.ValidatorUpdate {
// 	return nil
// }

// // func (k Keeper) ApplyAndReturnValidatorSetUpdates(ctx sdk.Context) (updates []abci.ValidatorUpdate, err error) {
// // }
// func (k Keeper) bondedToUnbonding(ctx sdk.Context, validator types.Validator) (types.Validator, error) {
// 	return types.Validator{}, nil
// }
// func (k Keeper) unbondingToBonded(ctx sdk.Context, validator types.Validator) (types.Validator, error) {
// 	return types.Validator{}, nil
// }
// func (k Keeper) unbondedToBonded(ctx sdk.Context, validator types.Validator) (types.Validator, error) {
// 	return types.Validator{}, nil
// }
// func (k Keeper) UnbondingToUnbonded(ctx sdk.Context, validator types.Validator) types.Validator {
// 	return types.Validator{}
// }
// func (k Keeper) jailValidator(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) unjailValidator(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) bondValidator(ctx sdk.Context, validator types.Validator) (types.Validator, error) {
// 	return types.Validator{}, nil
// }
// func (k Keeper) BeginUnbondingValidator(ctx sdk.Context, validator types.Validator) (types.Validator, error) {
// 	return types.Validator{}, nil
// }
// func (k Keeper) CompleteUnbondingValidator(ctx sdk.Context, validator types.Validator) types.Validator {
// 	return types.Validator{}
// }

// type validatorsByAddr map[string][]byte

// func (k Keeper) getLastValidatorsByAddr(ctx sdk.Context) (validatorsByAddr, error) {
// 	return nil, nil
// }
// func sortNoLongerBonded(last validatorsByAddr) ([][]byte, error) {
// 	return nil, nil
// }

// // validator.go
// func (k Keeper) GetValidator(ctx sdk.Context, addr sdk.ValAddress) (validator types.Validator, found bool) {
// 	return types.Validator{}, false
// }
// func (k Keeper) mustGetValidator(ctx sdk.Context, addr sdk.ValAddress) types.Validator {
// 	return types.Validator{}
// }
// func (k Keeper) GetValidatorByConsAddr(ctx sdk.Context, consAddr sdk.ConsAddress) (validator types.Validator, found bool) {
// 	return types.Validator{}, false
// }
// func (k Keeper) mustGetValidatorByConsAddr(ctx sdk.Context, consAddr sdk.ConsAddress) types.Validator {
// 	return types.Validator{}
// }
// func (k Keeper) SetValidator(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) SetValidatorByConsAddr(ctx sdk.Context, validator types.Validator) error {
// 	return nil
// }
// func (k Keeper) SetValidatorByPowerIndex(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) DeleteValidatorByPowerIndex(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) SetNewValidatorByPowerIndex(ctx sdk.Context, validator types.Validator) {
// }
// func (k Keeper) AddValidatorTokensAndShares(ctx sdk.Context, validator types.Validator,
// 	tokensToAdd sdk.Int) (valOut types.Validator, addedShares sdk.Dec) {
// 	return types.Validator{}, sdk.Dec{}
// }
// func (k Keeper) RemoveValidatorTokensAndShares(ctx sdk.Context, validator types.Validator,
// 	sharesToRemove sdk.Dec) (valOut types.Validator, removedTokens sdk.Int) {
// 	return types.Validator{}, sdk.Int{}
// }
// func (k Keeper) RemoveValidatorTokens(ctx sdk.Context,
// 	validator types.Validator, tokensToRemove sdk.Int) types.Validator {
// 	return types.Validator{}
// }
// func (k Keeper) UpdateValidatorCommission(ctx sdk.Context,
// 	validator types.Validator, newRate sdk.Dec) (types.Commission, error) {
// 	return types.Commission{}, nil
// }
// func (k Keeper) RemoveValidator(ctx sdk.Context, address sdk.ValAddress) {
// }

// // func (k Keeper) GetAllValidators(ctx sdk.Context) (validators []types.Validator) {
// // }
// // func (k Keeper) GetValidators(ctx sdk.Context, maxRetrieve uint32) (validators []types.Validator) {
// // }
// func (k Keeper) GetBondedValidatorsByPower(ctx sdk.Context) []types.Validator {
// 	return nil
// }
// func (k Keeper) ValidatorsPowerStoreIterator(ctx sdk.Context) sdk.Iterator {
// 	return nil
// }
// func (k Keeper) GetLastValidatorPower(ctx sdk.Context, operator sdk.ValAddress) (power int64) {
// 	return 0
// }
// func (k Keeper) SetLastValidatorPower(ctx sdk.Context, operator sdk.ValAddress, power int64) {
// }
// func (k Keeper) DeleteLastValidatorPower(ctx sdk.Context, operator sdk.ValAddress) {
// }
// func (k Keeper) LastValidatorsIterator(ctx sdk.Context) (iterator sdk.Iterator) {
// 	return nil
// }
// func (k Keeper) IterateLastValidatorPowers(ctx sdk.Context, handler func(operator sdk.ValAddress, power int64) (stop bool)) {
// }
// func (k Keeper) GetLastValidators(ctx sdk.Context) (validators []types.Validator) {
// 	return nil
// }
// func (k Keeper) GetUnbondingValidators(ctx sdk.Context, endTime time.Time, endHeight int64) []string {
// 	return nil
// }
// func (k Keeper) SetUnbondingValidatorsQueue(ctx sdk.Context, endTime time.Time, endHeight int64, addrs []string) {
// }
// func (k Keeper) InsertUnbondingValidatorQueue(ctx sdk.Context, val types.Validator) {
// }
// func (k Keeper) DeleteValidatorQueueTimeSlice(ctx sdk.Context, endTime time.Time, endHeight int64) {
// }
// func (k Keeper) DeleteValidatorQueue(ctx sdk.Context, val types.Validator) {
// }
// func (k Keeper) ValidatorQueueIterator(ctx sdk.Context, endTime time.Time, endHeight int64) sdk.Iterator {
// 	return nil
// }
// func (k Keeper) UnbondAllMatureValidators(ctx sdk.Context) {
// }

// // func (k Keeper) IsValidatorJailed(ctx sdk.Context, addr sdk.ConsAddress) bool {
// // }
