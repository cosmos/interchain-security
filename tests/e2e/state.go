package main

import (
	"fmt"
	"log"
	"regexp"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v9/modules/core/02-client/types"

	e2e "github.com/cosmos/interchain-security/v6/tests/e2e/testlib"
)

// type aliases
type (
	ChainState                   = e2e.ChainState
	ConsumerAdditionProposal     = e2e.ConsumerAdditionProposal
	ConsumerRemovalProposal      = e2e.ConsumerRemovalProposal
	ConsumerModificationProposal = e2e.ConsumerModificationProposal
	IBCTransferParams            = e2e.IBCTransferParams
	IBCTransferParamsProposal    = e2e.IBCTransferParamsProposal
	Param                        = e2e.Param
	ParamsProposal               = e2e.ParamsProposal
	Proposal                     = e2e.Proposal
	Rewards                      = e2e.Rewards
	TargetDriver                 = e2e.TargetDriver
	TextProposal                 = e2e.TextProposal
	TxResponse                   = e2e.TxResponse
	UpgradeProposal              = e2e.UpgradeProposal
)

type State map[ChainID]ChainState

type Chain struct {
	target     TargetDriver
	testConfig *TestConfig
}

// waitForTx waits until a transaction is seen in a block or panics if a timeout occurs
func (tr Chain) waitForTx(chain ChainID, txResponse []byte, timeout time.Duration) TxResponse {
	// remove any gas estimate as when command is run with gas=auto the output contains gas estimation mixed with json output
	re, err := regexp.Compile("gas estimate: [0-9]+")
	if err != nil {
		panic(fmt.Sprintf("error compiling regexp: %s", err.Error()))
	}
	txResponse = re.ReplaceAll(txResponse, []byte{})

	// check transaction
	response := e2e.GetTxResponse(txResponse)
	if response.Code != 0 {
		log.Fatalf("sending transaction failed with error code %d, Log:'%s'", response.Code, response.RawLog)
	}

	// wait for the transaction
	start := time.Now()
	for {
		res, err := tr.target.QueryTransaction(chain, response.TxHash)
		if err == nil {
			return e2e.GetTxResponse(res)
		}
		if time.Since(start) > timeout {
			log.Printf("query transaction failed with err=%s, resp=%s", err.Error(), res)
			panic(fmt.Sprintf("\n\nwaitForTx on chain '%s' has timed out after: %s\n\n", chain, timeout))
		}
		time.Sleep(1 * time.Second)
	}
}

func (tr Chain) waitBlocks(chain ChainID, blocks uint, timeout time.Duration) {
	if tr.testConfig.UseCometmock {
		// call advance_blocks method on cometmock
		// curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"advance_blocks","params":{"num_blocks": "36000000"},"id":1}' 127.0.0.1:22331
		tcpAddress := tr.target.GetQueryNodeRPCAddress(chain)
		method := "advance_blocks"
		params := fmt.Sprintf(`{"num_blocks": "%d"}`, blocks)

		tr.curlJsonRPCRequest(method, params, tcpAddress)
		return
	}
	startBlock := tr.target.GetBlockHeight(chain)

	tr.waitUntilBlock(chain, startBlock+blocks, timeout)
}

func (tr Chain) waitUntilBlock(chain ChainID, block uint, timeout time.Duration) {
	start := time.Now()
	for {
		thisBlock := tr.target.GetBlockHeight(chain)
		if thisBlock >= block {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(500 * time.Millisecond)
	}
}

func (tr Chain) GetBalances(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.target.GetBalance(chain, k)
	}

	return actualState
}

func (tr Chain) GetClientFrozenHeight(chain ChainID, clientID string) clienttypes.Height {
	revNumber, revHeight := tr.target.GetClientFrozenHeight(chain, clientID)
	return clienttypes.Height{RevisionHeight: revHeight, RevisionNumber: revNumber}
}

func (tr Chain) GetProposedConsumerChains(chain ChainID) []string {
	tr.waitBlocks(chain, 1, 10*time.Second)
	return tr.target.GetProposedConsumerChains(chain)
}

func (tr Chain) GetProposals(chain ChainID, modelState map[uint]Proposal) map[uint]Proposal {
	actualState := map[uint]Proposal{}
	for k := range modelState {
		actualState[k] = tr.target.GetProposal(chain, k)
	}

	return actualState
}

func (tr Chain) GetValPowers(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	validatorConfigs := tr.testConfig.ValidatorConfigs
	for k := range modelState {
		valAddresses := map[string]bool{}
		if chain == ChainID("provi") {
			// use binary with Bech32Prefix set to ProviderAccountPrefix
			valAddresses[validatorConfigs[k].ValconsAddress] = true
		} else {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			valAddresses[validatorConfigs[k].ValconsAddressOnConsumer] = true
			valAddresses[validatorConfigs[k].ConsumerValconsAddress] = true
		}
		actualState[k] = tr.target.GetValPower(chain, k)
	}

	return actualState
}

func (tr Chain) GetStakedTokens(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for validator := range modelState {
		validatorConfigs := tr.testConfig.ValidatorConfigs
		valoperAddress := validatorConfigs[validator].ValoperAddress
		if chain != ChainID("provi") {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			if validatorConfigs[validator].UseConsumerKey {
				valoperAddress = validatorConfigs[validator].ConsumerValoperAddress
			} else {
				// use the same address as on the provider but with different prefix
				valoperAddress = validatorConfigs[validator].ValoperAddressOnConsumer
			}
		}

		actualState[validator] = tr.target.GetValStakedTokens(chain, valoperAddress)
	}

	return actualState
}

func (tr Chain) GetRewards(chain ChainID, modelState Rewards) Rewards {
	receivedRewards := map[ValidatorID]bool{}

	currentBlock := tr.target.GetBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)
	nextBlock := tr.target.GetBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)

	if !modelState.IsIncrementalReward {
		currentBlock = 1
	}
	for k := range modelState.IsRewarded {
		receivedRewards[k] = tr.target.GetReward(chain, k, nextBlock, modelState.Denom) > tr.target.GetReward(chain, k, currentBlock, modelState.Denom)
	}

	return Rewards{IsRewarded: receivedRewards, IsIncrementalReward: modelState.IsIncrementalReward, Denom: modelState.Denom}
}

func (tr Chain) GetConsumerAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.target.GetConsumerAddress(chain, k)
	}

	return actualState
}

func (tr Chain) GetProviderAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.target.GetProviderAddressFromConsumer(chain, k)
	}

	return actualState
}

func (tr Chain) getValidatorNode(chain ChainID, validator ValidatorID) string {
	// for CometMock, validatorNodes are all the same address as the query node (which is CometMocks address)
	if tr.testConfig.UseCometmock {
		return tr.target.GetQueryNode(chain)
	}

	return "tcp://" + tr.getValidatorIP(chain, validator) + ":26658"
}

func (tr Chain) getValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.testConfig.ChainConfigs[chain].IpPrefix + "." + tr.testConfig.ValidatorConfigs[validator].IpSuffix
}

func (tr Chain) getValidatorHome(chain ChainID, validator ValidatorID) string {
	return `/` + string(chain) + `/validator` + fmt.Sprint(validator)
}

func (tr Chain) curlJsonRPCRequest(method, params, address string) {
	cmd_template := `curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"%s","params":%s,"id":1}' %s`

	cmd := tr.target.ExecCommand("bash", "-c", fmt.Sprintf(cmd_template, method, params, address))

	verbosity := false
	e2e.ExecuteCommand(cmd, "curlJsonRPCRequest", verbosity)
}

func (tr Chain) GetConsumerCommissionRates(chain ChainID, modelState map[ValidatorID]float64) map[ValidatorID]float64 {
	actualState := map[ValidatorID]float64{}
	for k := range modelState {
		actualState[k] = tr.target.GetConsumerCommissionRate(chain, k)
	}

	return actualState
}

func uintPtr(i uint) *uint {
	return &i
}

func intPtr(i int) *int {
	return &i
}
