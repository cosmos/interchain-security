- Remove support for legacy-proposal to add/modify/remove consumer proposals and change reward denoms
  ([\#2130](https://github.com/cosmos/interchain-security/pull/2130))
  To submit a proposal to add/modify/remove a consumer use the following command
  ```shell
  interchain-security-pd tx gov submit-proposal [proposal-file]
  ```

  Run `interchain-security-pd tx gov draft-proposal` command and select in `other` one of the following
  message types to generate a draft proposal json file:
  - `/interchain_security.ccv.provider.v1.MsgConsumerAddition`

  - `/interchain_security.ccv.provider.v1.MsgConsumerModification`

  - `/interchain_security.ccv.provider.v1.MsgConsumerRemoval`

  - `/interchain_security.ccv.provider.v1.MsgChangeRewardDenoms`

  This replaces the following command which are not supported anymore:

  ```shell
  interchain-security-pd tx gov submit-legacy-proposal consumer-addition [proposal-file]
  interchain-security-pd tx gov submit-legacy-proposal consumer-modification [proposal-file]
  interchain-security-pd tx gov submit-legacy-proposal consumer-removal [proposal-file]
  interchain-security-pd tx gov submit-legacy-proposal change-reward-denoms [proposal-file]
  ```