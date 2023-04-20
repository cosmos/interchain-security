package testutil

import (
	"context"

	"github.com/stretchr/testify/mock"
	"github.com/tendermint/tendermint/libs/bytes"
	"github.com/tendermint/tendermint/libs/log"
	rpcClient "github.com/tendermint/tendermint/rpc/client"
	ctypes "github.com/tendermint/tendermint/rpc/core/types"
	"github.com/tendermint/tendermint/types"
)

// A mock client to be used in tests that want to mock out calls to the CometBFT CLI.
// The client implements the interface "github.com/tendermint/tendermint/rpc/client".Client
// Example Usage:
//
//	mockClient := new(testutil.MockCometBFTRPCClient)
//	clientCtx := client.Context{}.WithClient(mockClient)
//	mockClient.On("ConsensusParams", mock.Anything, mock.Anything).Return(&resConsensParams, nil)
//	{code using clientCtx}
type MockCometBFTRPCClient struct {
	mock.Mock
}

// IsRunning implements client.Client
func (m MockCometBFTRPCClient) IsRunning() bool {
	args := m.Called()
	return args.Bool(0)
}

// OnReset implements client.Client
func (m MockCometBFTRPCClient) OnReset() error {
	args := m.Called()
	return args.Error(0)
}

// OnStart implements client.Client
func (m MockCometBFTRPCClient) OnStart() error {
	args := m.Called()
	return args.Error(0)
}

// OnStop implements client.Client
func (m MockCometBFTRPCClient) OnStop() {
	m.Called()
}

// Quit implements client.Client
func (m MockCometBFTRPCClient) Quit() <-chan struct{} {
	args := m.Called()
	return args.Get(0).(<-chan struct{})
}

// Reset implements client.Client
func (m MockCometBFTRPCClient) Reset() error {
	args := m.Called()
	return args.Error(0)
}

// SetLogger implements client.Client
func (m MockCometBFTRPCClient) SetLogger(logger log.Logger) {
	m.Called(logger)
}

// Start implements client.Client
func (m MockCometBFTRPCClient) Start() error {
	args := m.Called()
	return args.Error(0)
}

// Stop implements client.Client
func (m MockCometBFTRPCClient) Stop() error {
	args := m.Called()
	return args.Error(0)
}

// ABCIInfo implements client.Client
func (m MockCometBFTRPCClient) ABCIInfo(ctx context.Context) (*ctypes.ResultABCIInfo, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultABCIInfo), args.Error(1)
}

// ABCIQuery implements client.Client
func (m MockCometBFTRPCClient) ABCIQuery(ctx context.Context, path string, data bytes.HexBytes) (*ctypes.ResultABCIQuery, error) {
	args := m.Called(ctx, path, data)
	return args.Get(0).(*ctypes.ResultABCIQuery), args.Error(1)
}

// ABCIQueryWithOptions implements client.Client
func (m MockCometBFTRPCClient) ABCIQueryWithOptions(ctx context.Context, path string, data bytes.HexBytes, opts rpcClient.ABCIQueryOptions) (*ctypes.ResultABCIQuery, error) {
	args := m.Called(ctx, path, data, opts)
	return args.Get(0).(*ctypes.ResultABCIQuery), args.Error(1)
}

// BroadcastTxAsync implements client.Client
func (m MockCometBFTRPCClient) BroadcastTxAsync(ctx context.Context, tx types.Tx) (*ctypes.ResultBroadcastTx, error) {
	args := m.Called(ctx, tx)
	return args.Get(0).(*ctypes.ResultBroadcastTx), args.Error(1)
}

// BroadcastTxCommit implements client.Client
func (m MockCometBFTRPCClient) BroadcastTxCommit(ctx context.Context, tx types.Tx) (*ctypes.ResultBroadcastTxCommit, error) {
	args := m.Called(ctx, tx)
	return args.Get(0).(*ctypes.ResultBroadcastTxCommit), args.Error(1)
}

// BroadcastTxSync implements client.Client
func (m MockCometBFTRPCClient) BroadcastTxSync(ctx context.Context, tx types.Tx) (*ctypes.ResultBroadcastTx, error) {
	args := m.Called(ctx, tx)
	return args.Get(0).(*ctypes.ResultBroadcastTx), args.Error(1)
}

// Subscribe implements client.Client
func (m MockCometBFTRPCClient) Subscribe(ctx context.Context, subscriber string, query string, outCapacity ...int) (<-chan ctypes.ResultEvent, error) {
	args := m.Called(ctx, subscriber, query, outCapacity)
	return args.Get(0).(<-chan ctypes.ResultEvent), args.Error(1)
}

// Unsubscribe implements client.Client
func (m *MockCometBFTRPCClient) Unsubscribe(ctx context.Context, subscriber string, query string) error {
	args := m.Called(ctx, subscriber, query)
	return args.Error(0)
}

// UnsubscribeAll implements client.Client
func (m *MockCometBFTRPCClient) UnsubscribeAll(ctx context.Context, subscriber string) error {
	args := m.Called(ctx, subscriber)
	return args.Error(0)
}

// BlockchainInfo implements client.Client
func (m *MockCometBFTRPCClient) BlockchainInfo(ctx context.Context, minHeight int64, maxHeight int64) (*ctypes.ResultBlockchainInfo, error) {
	args := m.Called(ctx, minHeight, maxHeight)
	return args.Get(0).(*ctypes.ResultBlockchainInfo), args.Error(1)
}

// Genesis implements client.Client
func (m *MockCometBFTRPCClient) Genesis(ctx context.Context) (*ctypes.ResultGenesis, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultGenesis), args.Error(1)
}

// GenesisChunked implements client.Client
func (m *MockCometBFTRPCClient) GenesisChunked(ctx context.Context, chunkSize uint) (*ctypes.ResultGenesisChunk, error) {
	args := m.Called(ctx, chunkSize)
	return args.Get(0).(*ctypes.ResultGenesisChunk), args.Error(1)
}

// ConsensusParams implements client.Client
func (m *MockCometBFTRPCClient) ConsensusParams(ctx context.Context, height *int64) (*ctypes.ResultConsensusParams, error) {
	args := m.Called(ctx, height)
	return args.Get(0).(*ctypes.ResultConsensusParams), args.Error(1)
}

// ConsensusState implements client.Client
func (m MockCometBFTRPCClient) ConsensusState(ctx context.Context) (*ctypes.ResultConsensusState, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultConsensusState), args.Error(1)
}

// DumpConsensusState implements client.Client
func (m MockCometBFTRPCClient) DumpConsensusState(ctx context.Context) (*ctypes.ResultDumpConsensusState, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultDumpConsensusState), args.Error(1)
}

// Health implements client.Client
func (m MockCometBFTRPCClient) Health(ctx context.Context) (*ctypes.ResultHealth, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultHealth), args.Error(1)
}

// NetInfo implements client.Client
func (m MockCometBFTRPCClient) NetInfo(ctx context.Context) (*ctypes.ResultNetInfo, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultNetInfo), args.Error(1)
}

// Block implements client.Client
func (m MockCometBFTRPCClient) Block(ctx context.Context, height *int64) (*ctypes.ResultBlock, error) {
	args := m.Called(ctx, height)
	return args.Get(0).(*ctypes.ResultBlock), args.Error(1)
}

// BlockByHash implements client.Client
func (m MockCometBFTRPCClient) BlockByHash(ctx context.Context, hash []byte) (*ctypes.ResultBlock, error) {
	args := m.Called(ctx, hash)
	return args.Get(0).(*ctypes.ResultBlock), args.Error(1)
}

// BlockResults implements client.Client
func (m MockCometBFTRPCClient) BlockResults(ctx context.Context, height *int64) (*ctypes.ResultBlockResults, error) {
	args := m.Called(ctx, height)
	return args.Get(0).(*ctypes.ResultBlockResults), args.Error(1)
}

// BlockSearch implements client.Client
func (m MockCometBFTRPCClient) BlockSearch(ctx context.Context, query string, page *int, perPage *int, orderBy string) (*ctypes.ResultBlockSearch, error) {
	args := m.Called(ctx, query, page, perPage, orderBy)
	return args.Get(0).(*ctypes.ResultBlockSearch), args.Error(1)
}

// Commit implements client.Client
func (m MockCometBFTRPCClient) Commit(ctx context.Context, height *int64) (*ctypes.ResultCommit, error) {
	args := m.Called(ctx, height)
	return args.Get(0).(*ctypes.ResultCommit), args.Error(1)
}

// Tx implements client.Client
func (m MockCometBFTRPCClient) Tx(ctx context.Context, hash []byte, prove bool) (*ctypes.ResultTx, error) {
	args := m.Called(ctx, hash, prove)
	return args.Get(0).(*ctypes.ResultTx), args.Error(1)
}

// TxSearch implements client.Client
func (m MockCometBFTRPCClient) TxSearch(ctx context.Context, query string, prove bool, page *int, perPage *int, orderBy string) (*ctypes.ResultTxSearch, error) {
	args := m.Called(ctx, query, prove, page, perPage, orderBy)
	return args.Get(0).(*ctypes.ResultTxSearch), args.Error(1)
}

// Validators implements client.Client
func (m MockCometBFTRPCClient) Validators(ctx context.Context, height *int64, page *int, perPage *int) (*ctypes.ResultValidators, error) {
	args := m.Called(ctx, height, page, perPage)
	return args.Get(0).(*ctypes.ResultValidators), args.Error(1)
}

// Status implements client.Client
func (m *MockCometBFTRPCClient) Status(ctx context.Context) (*ctypes.ResultStatus, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultStatus), args.Error(1)
}

// BroadcastEvidence implements client.Client
func (m *MockCometBFTRPCClient) BroadcastEvidence(ctx context.Context, ev types.Evidence) (*ctypes.ResultBroadcastEvidence, error) {
	args := m.Called(ctx, ev)
	return args.Get(0).(*ctypes.ResultBroadcastEvidence), args.Error(1)
}

// CheckTx implements client.Client
func (m *MockCometBFTRPCClient) CheckTx(ctx context.Context, tx types.Tx) (*ctypes.ResultCheckTx, error) {
	args := m.Called(ctx, tx)
	return args.Get(0).(*ctypes.ResultCheckTx), args.Error(1)
}

// NumUnconfirmedTxs implements client.Client
func (m *MockCometBFTRPCClient) NumUnconfirmedTxs(ctx context.Context) (*ctypes.ResultUnconfirmedTxs, error) {
	args := m.Called(ctx)
	return args.Get(0).(*ctypes.ResultUnconfirmedTxs), args.Error(1)
}

// UnconfirmedTxs implements client.Client
func (m *MockCometBFTRPCClient) UnconfirmedTxs(ctx context.Context, limit *int) (*ctypes.ResultUnconfirmedTxs, error) {
	args := m.Called(ctx, limit)
	return args.Get(0).(*ctypes.ResultUnconfirmedTxs), args.Error(1)
}
