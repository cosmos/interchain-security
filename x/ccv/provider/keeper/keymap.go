package keeper

/*
TODO: I think roughly, what I need to do, to drive this thing to completion is

- [ ] more unit tests
- [ ] integration with SendValidatorUpdates
- [ ] integration with Consumer Initiated Slashing (receive request)
- [ ] integration with Consumer Initiated Slashing (send acks)
- [ ] integration with Validator add / delete
- [ ] integration with RPC queries
- [ ] integration with msg server
- [ ] integration with pending changes
- [ ] include in diff test driver?
- [ ] include in any existing tests?

- Whenever a consumer chain is added or removed a new Keymap instance needs to be created
with a store interface which handles all of its reading and writing.
	- Need to figure out exactly where/when to add/delete consumer chain instance
	- Need to figure out exactly where/when to add/remove validator instance (with default?)


*/

func (k Keeper) getPkToCk() map[PK]CK {
	_ = k
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) getCkToPk() map[CK]PK {
	_ = k
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) getCkToMemo() map[CK]memo {
	_ = k
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) setPkToCk(e map[PK]CK) {
	_ = k
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) setCkToPk(e map[CK]PK) {
	_ = k
	// TODO: implement
	panic("not implemented")
}

func (k Keeper) setCkToMemo(e map[CK]memo) {
	_ = k
	// TODO: implement
	panic("not implemented")
}
