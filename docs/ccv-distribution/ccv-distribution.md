# CCV Distribution
                                                                             
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
          ┌─             │                               │                                            
          │              │                    ┌──────────┘                                           
          │              │                    │                                                       
          │     wait for both packets to be received                                                          
          │              │                                                                                    
  Provider│    ┌─initialize────────────────┐             -- Diagram Aliases --                                
  Chain  ─┤    │QualifiedTotalWeight := TW │             TW  = ProviderPoolWeights.TotalWeight        
          │    │DisqualifiedPool     := 0  │             PPT = ProviderPoolTokens                        
          │    └─────────┬─────────────────┘             W[i]= ProviderPoolWeights[i]                    
          │              │                                                                                
          │              ▼                                                                                   
          │    ┌─for each validator[i] in ProviderPool───────────────────────┐
          │    │┌──────────────┐    ┌──────────────────────────────────────┐ │
          │    ││does validator│    │validator forfeits rewards:           │ │
          │    ││still exist?  │    │                                      │ │
          │    │└──┬───┬───────┘    │DisqualifiedPool     += PPT * W[i]/TW │ │     
          │    │   │   └──no───────▶│QualifiedTotalWeight -= W[i]          │ │     
          │    │   │                └──────────────────────────────────────┘ │
          │    │   │                ┌───────────────────────┐                │
          │    │   └──────yes──────▶│added to array         │                │
          │    │                    │of qualified validators│                │
          │    │                    └───────────────────────┘                │
          │    └─────────┬───────────────────────────────────────────────────┘
          │              ├───▶if no qualified validators send DisqualifiedPool
          │              │    to provider community pool (edge case)       
          │              ▼                                                                         
          │    ┌─for each qualified validator[i]─────────────────────────────────┐ 
          │    │┌──────────────────────────────────┐┌───────────────────────────┐│ 
          │    ││calculate rewards:                ││final distribution using   ││ 
          │    ││ValRewards =                      ││AllocateTokensToValidator: ││ 
          │    ││       PPT * W[i]/TW              ││ -> delegator rewards      ││ 
          │    ││       + DisqualifiedPool         ││ -> validator commission   ││ 
          │    ││       * W[i]/QualifiedTotalWeight││                           ││ 
          │    │└──────────────────────────────────┘└───────────────────────────┘│ 
          └─   └─────────────────────────────────────────────────────────────────┘ 
                                                                                               
```        
           
           
           
           
           
           
           
           
