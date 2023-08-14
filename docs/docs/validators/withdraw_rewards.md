---
sidebar_position: 3
---

# Withdrawing consumer chain validator rewards

Here are example steps for withdrawing rewards from consumer chains in the provider chain

:::info
The examples used are from `rs-testnet`, the replicated security persistent testnet.

Validator operator address: `cosmosvaloper1e5yfpc8l6g4808fclmlyd38tjgxuwshnmjkrq6`
Self-delegation address: `cosmos1e5yfpc8l6g4808fclmlyd38tjgxuwshn7xzkvf`
:::

Prior to withdrawing rewards, query balances for self-delegation address:

```bash
gaiad q bank balances cosmos1e5yfpc8l6g4808fclmlyd38tjgxuwshn7xzkvf

balances:
- amount: "1000000000000"
  denom: uatom
pagination:
  next_key: null
  total: "0"
```

## Querying validator rewards
Query rewards for the validator address:

```bash
gaiad q distribution rewards cosmos1e5yfpc8l6g4808fclmlyd38tjgxuwshn7xzkvf cosmosvaloper1e5yfpc8l6g4808fclmlyd38tjgxuwshnmjkrq6

rewards:
- amount: "158.069895000000000000"
  denom: ibc/2CB0E87E2A742166FEC0A18D6FBF0F6AD4AA1ADE694792C1BD6F5E99088D67FD
- amount: "841842390516.072526500000000000"
  denom: uatom
```

The `ibc/2CB0E87E2A742166FEC0A18D6FBF0F6AD4AA1ADE694792C1BD6F5E99088D67FD` denom represents rewards from a consumer chain.


## Withdrawing rewards and commission

### 1. Withdraw rewards
```bash
gaiad tx distribution withdraw-rewards cosmosvaloper1e5yfpc8l6g4808fclmlyd38tjgxuwshnmjkrq6 --from cosmos1e5yfpc8l6g4808fclmlyd38tjgxuwshn7xzkvf --commission --chain-id provider --gas auto --fees 500uatom -b block -y

txhash: A7E384FB1958211B43B7C06527FC7D4471FB6B491EE56FDEA9C5634D76FF1B9A
```

### 2. Confirm withdrawal
After withdrawing rewards self-delegation address balance to confirm rewards were withdrawn:

```bash
gaiad q bank balances cosmos1e5yfpc8l6g4808fclmlyd38tjgxuwshn7xzkvf

balances:
- amount: "216"
  denom: ibc/2CB0E87E2A742166FEC0A18D6FBF0F6AD4AA1ADE694792C1BD6F5E99088D67FD
- amount: "2233766225342"
  denom: uatom
pagination:
  next_key: null
  total: "0"
```
