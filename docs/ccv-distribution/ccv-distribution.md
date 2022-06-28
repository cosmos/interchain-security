# CCV Distribution

This diagram describes an more correct ccv distribution mechanism. Note that
this is not the simple distribution mechanism. 
                                                                             
```                                                                          
              ┌─for each block────────────────────────────────────┐     
          ┌─  │┌─────────────────┐             ┌───────────────┐  │ -- Params -- 
          │   ││consumer-chain   │             │fee-collector  │  │  [P1] BlocksPerDistributionTransmission                  
          │   ││mints & collects ├──sends-to──▶│holding address│  │                                                         
          │   ││reward tokens    │             └───────┬───────┘  │ -- Keys --                                        
          │   │└─────────────────┘                     │          │  [K1] LastDistributionTransmission
          │   │                                        │          │  [K2] DistributionValidatorHoldingPool
          │   │                                        ▼          └──────────┐
  Consumer│   │                        ┌──AllocateTokens───────────────────┐ │
  Chain  ─┤   │ tendermint votes,      │distribute funds from fee-collector│ │
          │   │ power, & proposer ────▶│to per-validator holding pool      │ │
          │   │                        │using AllocateTokens-              │ │
          │   │                        │ToProviderValidatorHoldingPool     │ │
          │   │                        │(pools held with key prefix: [K2]) │ │                          
          │   │                        └───────────────────────────────────┘ │
          │   └─────────────────┬────────────────────────────────────────────┘
          │                     │                                  ▲ 
          │     wait [P1] blocks from last distribution [K1]       │ 
          │                     │                                  │               
          │                     ▼                                  │               
          │   ┌──────────────────────────────────────────┐         │            
          │   │combine all rewards held in all per-      │         │            
          │   │validator holding pools into a single pool│  send back remainder
          │   │(ProviderPoolTokens) while recording      │  to fee-collector for
          │   │the fraction of this pool owed to each    │  use in next block
          │   │validate into a ProviderPoolWeights object│         │            
          │   └───────────┬───────────┬──────────────────┘         │            
          │               │           │    ┌───────────────────────┴─────┐    
          │     ┌─────────┴─────────┐ └────┤truncate ProviderPoolTokens  │ 
          │     │ProviderPoolWeights│      │converting: DecCoins -> Coins│
          │     └─────────┬─────────┘      └─────────────┬───────────────┘  
          │               │                              │                
          └─              ▼                              ▼  
          ┌─    transmit to provider            transmit to provider                            
  Relayer─┤     chain on CCV ordered            chain on unordered                                      
          └─    IBC channel                     IBC channel (ICS-20)                                     
          ┌─              │                              │                                            
          │               │                   ┌──────────┘                                           
  Provider│               │                   │                                                       
  Chain  ─┤    wait for enough tokens to be received      
          │    to fulfill ProviderPoolWeights.TotalTokens
          │               │                                    -- Diagram Aliases --                         
          │    ┌─initialize──────────────────┐                 TW   = ProviderPoolWeights.TotalWeight     
          │    │PPTE          = PPT + Excess │◀════════════╗   PPT  = ProviderPoolTokens                 
          │    │PoolRemaining = PPTE         │             ║   PPTE = ProviderPoolTokensWithExcess       
          │    └──────────┬──────────────────┘             ║   W[i] = ProviderPoolWeights[i]             
          │               │                                ║                                                 
          │               ▼                                ║                                                 
          │    ┌─for each validator[i] in ProviderPool─┐   ║                                        
          │    │┌──────────────────────────────────┐   │   ║                                                           
          │    ││calculate rewards:                │   │   ║                                        
          │    ││  ValRewards     = PPT * W[i]/TW  │   │   ║                                                      
          │    ││  PoolRemaining -= ValRewards     │   │  ┌╨┐                                                     
          │    │└──────┬───────────────────────────┘   │  │+│◀═══════════════╗                      
          │    │       │                               │  └╥┘                ║                   
          │    │       ▼                               │   ║                 ║                   
          │    │┌──────────────┐                       │   ║                 ║                     
          │    ││does validator│                       └───╫─────────────┐   ║                    
          │    ││still exist?  │    ┌──────────────────────╨──────────┐  │   ║
          │    │└──┬───┬───────┘    │validator forfeits rewards,      │  │   ║     
          │    │   │   │            │added to excess for next block:  │  │   ║     
          │    │   │   └──no───────▶│  Excess += ValRewards           │  │   ║
          │    │   │    (edge-case) └─────────────────────────────────┘  │   ║
          │    │   │                ┌─────────────────────────────────┐  │   ║
          │    │   │                │final distribution of ValRewards │  │   ║
          │    │   └──────yes──────▶│with AllocateTokensToValidator:  │  │   ║
          │    │                    │  -> delegator rewards           │  │   ║
          │    │                    │  -> validator commission        │  │   ║
          │    │                    └─────────────────────────────────┘  │   ║                     
          │    └──────────┬──────────────────────────────────────────────┘   ║    
          │               │                                                  ║   
          │               ▼                                                  ║    
          │    ┌─────────────────────────────────────────────────────────┐   ║                                                     
          │    │any rounding error added to excess for next block:       │   ║                                                     
          │    │  Excess += PoolRemaining                                ╞═══╝        
          │    └─────────────────────────────────────────────────────────┘                     
          └─                                                                                   
```        
           
           
           
           
           
           
           
           
