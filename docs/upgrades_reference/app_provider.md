# provider/app.go
* use ibc-go/modules/capability
* interfaces registration
```go
interfaceRegistry, _ := types.NewInterfaceRegistryWithOptions(types.InterfaceRegistryOptions{
	ProtoFiles: proto.HybridResolver,
	SigningOptions: signing.Options{
		AddressCodec: address.Bech32Codec{
			Bech32Prefix: sdk.GetConfig().GetBech32AccountAddrPrefix(),
		},
		ValidatorAddressCodec: address.Bech32Codec{
			Bech32Prefix: sdk.GetConfig().GetBech32ValidatorAddrPrefix(),
		},
	},
})
appCodec := codec.NewProtoCodec(interfaceRegistry)
legacyAmino := codec.NewLegacyAmino()
txConfig := authtx.NewTxConfig(appCodec, authtx.DefaultSignModes)

std.RegisterLegacyAminoCodec(legacyAmino)
std.RegisterInterfaces(interfaceRegistry)
// ABCI++, v50
voteExtOp := func(bApp *baseapp.BaseApp) {
	voteExtHandler := NewVoteExtensionHandler()
	voteExtHandler.SetHandlers(bApp)
}
baseAppOptions = append(baseAppOptions, voteExtOp)

bApp := baseapp.NewBaseApp(AppName, logger, db, txConfig.TxDecoder(), baseAppOptions...)
```

* register streaming services so ibc-testing can listen for packets
```go
// register streaming services
if err := bApp.RegisterStreamingServices(appOpts, keys); err != nil {
	panic(err)
}

```

* function additions
```go

func (app *App) PreBlocker(ctx sdk.Context, _ *abci.RequestFinalizeBlock) (*sdk.ResponsePreBlock, error) {
	return app.MM.PreBlock(ctx)
}

// Configurator returns the configurator for the app
func (app *App) Configurator() module.Configurator {
	return app.configurator
}

func (app *App) setPostHandler() {
	postHandler, err := posthandler.NewPostHandler(
		posthandler.HandlerOptions{},
	)
	if err != nil {
		panic(err)
	}

	app.SetPostHandler(postHandler)
}

// AutoCliOpts returns the autocli options for the app.
func (app *App) AutoCliOpts() autocli.AppOptions {
	modules := make(map[string]appmodule.AppModule, 0)
	for _, m := range app.MM.Modules {
		if moduleWithName, ok := m.(module.HasName); ok {
			moduleName := moduleWithName.Name()
			if appModule, ok := moduleWithName.(appmodule.AppModule); ok {
				modules[moduleName] = appModule
			}
		}
	}

	return autocli.AppOptions{
		Modules:               modules,
		ModuleOptions:         runtimeservices.ExtractAutoCLIOptions(app.MM.Modules),
		AddressCodec:          authcodec.NewBech32Codec(sdk.GetConfig().GetBech32AccountAddrPrefix()),
		ValidatorAddressCodec: authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ValidatorAddrPrefix()),
		ConsensusAddressCodec: authcodec.NewBech32Codec(sdk.GetConfig().GetBech32ConsensusAddrPrefix()),
	}
}

```

* function updates
```go
func (app *App) BeginBlocker(ctx sdk.Context) (sdk.BeginBlock, error) {
	return app.MM.BeginBlock(ctx)
}

func (app *App) EndBlocker(ctx sdk.Context) (sdk.EndBlock, error) {
	return app.MM.EndBlock(ctx)
}

func (app *App) InitChainer(ctx sdk.Context, req *abci.RequestInitChain) (*abci.ResponseInitChain, error) {...}

func (app *App) RegisterNodeService(clientCtx client.Context, cfg config.Config) {
	nodeservice.RegisterNodeService(clientCtx, app.GRPCQueryRouter(), cfg)
}
```

* `cmd/nterchain-security-p/root.go was wired to autoCLI
