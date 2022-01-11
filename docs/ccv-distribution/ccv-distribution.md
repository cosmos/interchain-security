# CCV Distribution

Tokens distributed                                                           
                                                                             
                                                                             
```                                                                          
               ┌─for each block─────────────────────────────────────────┐    
          ┌─   │┌─────────────────┐                  ┌────────────────┐ │    
          │    ││child-chain      │                  │protocol        │ │          Child-Chain 
          │    ││mints or collects├────sends-to─────▶│holding address │ │           Distribution Params 
          │    ││reward tokens    │                  └───────┬────────┘ │           - RewardPeriodBlocks
          │    │└─────────────────┘                          │          │           - 
          │    │                                             ▼          │    
  consumer│    │┌────────────────────┐          ┌─next abci.BeginBlock┐ │                                    
  chain  ─┤    ││child-chain         │          │distributes to       │ │    
          │    ││collects votes and  │          │holding-pool         │ │                      
          │    ││associated power and├─────────▶│containing validator │ │                                     
          │    ││who the proposer was│          │operator &           │ │    
          │    ││for each block      │          │associated tokens    │ │    
               │└────────────────────┘          │for previous block   │ │    
          │    │                                └─────────────────────┘ │    
          │    └──────────┬─────────────────────────────────────────────┘                
                          │
          │     Wait RewardPeriodBlocks
          │               │                      
          │               ▼                     
          │     ┌──────────────────────────────┐
          │     │Construct & transmit IBC      │
          │     │message containing accumulated│
          │     │holding pool                  │
          │     └──────────────────────────────┘
          │                                    
          │               │             
          │      transmit IBC message                                    
          │      to provider chain                                                 
          └─              │                                               
                          │          ┌───────────────────────────────────────────────────────┐
                          ├─────────▶│ set total_reward_fraction = total-incoming-ccv-rewards│
                          ▼          └───────────────────────────────────────────────────────┘
                ┌ for each validator in the holding pool received ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  ┐
                              ┌─────────────────────┐                            
  provider                    │is validator operator│                           │
  chain         ◀────yes──────┤still operating?     │                            
                              └──────────────┬──────┘                           │
                                             │
                                                                no                                   
                                                                │                                    
                │                                               ▼                                  │
                   ├─────────────────┐       ┌─────────────────────────────────────────────────┐    
                   │added to array   │       │validator forfeights reward tokens allocated     │ 
                │  │of validators    │       │to disqualified rewards pool                     │ 
                   │receiving rewards│       │disqualified_rewards_pool += disqualified_rewards│
                   └─────────────────┘       │total_reward_fraction -= disqualified_rewards    │                                  
                └ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  └─────────────────────────────────────────────────┘  ─┴    

                for each validator receiving rewards not disqualified:
                calculate rewards as: holding_pool_allocated_tokens +
                                        disqualified_rewards * (holding_pool_allocated_tokens/total_reward_fraction)



                final distribution to delegators through keeper.AllocateTokensToValidator function 


                                                                                                
```
