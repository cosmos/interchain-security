"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[2110],{9075:(e,n,a)=>{a.r(n),a.d(n,{assets:()=>c,contentTitle:()=>s,default:()=>l,frontMatter:()=>o,metadata:()=>r,toc:()=>h});var i=a(5893),t=a(1151);const o={sidebar_position:8,title:"Frequently Asked Questions",slug:"/faq"},s=void 0,r={id:"frequently-asked-questions",title:"Frequently Asked Questions",description:"General",source:"@site/docs/frequently-asked-questions.md",sourceDirName:".",slug:"/faq",permalink:"/interchain-security/faq",draft:!1,unlisted:!1,tags:[],version:"current",sidebarPosition:8,frontMatter:{sidebar_position:8,title:"Frequently Asked Questions",slug:"/faq"},sidebar:"tutorialSidebar",previous:{title:"Fault Resolutions",permalink:"/interchain-security/adrs/adr-022-fault-resolutions"}},c={},h=[{value:"General",id:"general",level:2},{value:"What is Interchain Security (ICS)?",id:"what-is-interchain-security-ics",level:3},{value:"What is the difference between ICS and Partial Set Security (PSS)?",id:"what-is-the-difference-between-ics-and-partial-set-security-pss",level:3},{value:"Consumer Chains",id:"consumer-chains",level:2},{value:"What are consumer chains?",id:"what-are-consumer-chains",level:3},{value:"How to become a consumer chain?",id:"how-to-become-a-consumer-chain",level:3},{value:"What happens to consumers if the provider is down?",id:"what-happens-to-consumers-if-the-provider-is-down",level:3},{value:"What happens to provider if any of the consumers are down?",id:"what-happens-to-provider-if-any-of-the-consumers-are-down",level:3},{value:"Can consumer chains have their own token?",id:"can-consumer-chains-have-their-own-token",level:3},{value:"Can consumer chains have their own governance?",id:"can-consumer-chains-have-their-own-governance",level:3},{value:"Can a consumer chain modify its power shaping parameters?",id:"can-a-consumer-chain-modify-its-power-shaping-parameters",level:3},{value:"Can a Top N consumer chain become Opt-In or vice versa?",id:"can-a-top-n-consumer-chain-become-opt-in-or-vice-versa",level:3},{value:"Validators",id:"validators",level:2},{value:"How can validators opt in to validate a consumer chain?",id:"how-can-validators-opt-in-to-validate-a-consumer-chain",level:3},{value:"Can validators opt in to an Opt-in chain after the spawn time if nobody else opted in?",id:"can-validators-opt-in-to-an-opt-in-chain-after-the-spawn-time-if-nobody-else-opted-in",level:3},{value:"How does a validator know which consumers chains it has to validate?",id:"how-does-a-validator-know-which-consumers-chains-it-has-to-validate",level:3},{value:"How many chains can a validator opt in to?",id:"how-many-chains-can-a-validator-opt-in-to",level:3},{value:"How can validators assign consumer keys?",id:"how-can-validators-assign-consumer-keys",level:3},{value:"What are the benefits for validators running consumer chains?",id:"what-are-the-benefits-for-validators-running-consumer-chains",level:3},{value:"Can validators set per consumer chain commission rates?",id:"can-validators-set-per-consumer-chain-commission-rates",level:3},{value:"What are the risks for validators running consumer chains?",id:"what-are-the-risks-for-validators-running-consumer-chains",level:3},{value:"Can validators run the provider and consumer chains on the same machine?",id:"can-validators-run-the-provider-and-consumer-chains-on-the-same-machine",level:3},{value:"Can validators opt out of validating a consumer chain?",id:"can-validators-opt-out-of-validating-a-consumer-chain",level:3},{value:"Can all validators opt out of an Opt-in chain?",id:"can-all-validators-opt-out-of-an-opt-in-chain",level:3},{value:"How to connect to the testnets?",id:"how-to-connect-to-the-testnets",level:3},{value:"Integrators",id:"integrators",level:2},{value:"Which relayers are supported?",id:"which-relayers-are-supported",level:3},{value:"How to check when the next validator update will be sent to the consumer chains?",id:"how-to-check-when-the-next-validator-update-will-be-sent-to-the-consumer-chains",level:3}];function d(e){const n={a:"a",code:"code",em:"em",h2:"h2",h3:"h3",li:"li",p:"p",pre:"pre",strong:"strong",ul:"ul",...(0,t.a)(),...e.components};return(0,i.jsxs)(i.Fragment,{children:[(0,i.jsx)(n.h2,{id:"general",children:"General"}),"\n",(0,i.jsx)(n.h3,{id:"what-is-interchain-security-ics",children:"What is Interchain Security (ICS)?"}),"\n",(0,i.jsxs)(n.p,{children:["ICS is an IBC protocol that enables a provider chain (e.g., the Cosmos Hub) to provide security to multiple ",(0,i.jsx)(n.a,{href:"#what-are-consumer-chains",children:"consumer chains"}),".\nThis means that consumer chains will leverage the stake locked on the provider chain for block production (i.e., a cross-chain proof-of-stake system).\nICS allows anyone to launch a consumer chain using a subset, or even the entire, validator set from the provider chain.\nNote that validators need to run separate infrastructure for the provider and consumer chains, resulting in different networks that only share (a subset of) the validator set."]}),"\n",(0,i.jsx)(n.h3,{id:"what-is-the-difference-between-ics-and-partial-set-security-pss",children:"What is the difference between ICS and Partial Set Security (PSS)?"}),"\n",(0,i.jsxs)(n.p,{children:[(0,i.jsx)(n.a,{href:"#what-is-interchain-security-ics",children:"ICS is a protocol"}),".\nPSS is a feature of ICS that allows a provider chain to share only a subset of its validator set with a consumer chain.\nPSS differentiates between TopN and Opt-In consumer chains.\nFor TopN chains, the validator subset is determined by the top N% provider validators by voting power.\nFor Opt-In chains, the validator subset is determined by validators opting in to validate the consumer chains.\nPSS allows for flexible tradeoffs between security, decentralization, and the budget a consumer chain spends on rewards to validators."]}),"\n",(0,i.jsxs)(n.p,{children:["For more details, see the ",(0,i.jsx)(n.a,{href:"/interchain-security/features/partial-set-security",children:"PSS feature"}),"."]}),"\n",(0,i.jsx)(n.h2,{id:"consumer-chains",children:"Consumer Chains"}),"\n",(0,i.jsx)(n.h3,{id:"what-are-consumer-chains",children:"What are consumer chains?"}),"\n",(0,i.jsx)(n.p,{children:"Consumer chains are blockchains operated by (a subset of) the validators of the provider chain.\nThe ICS protocol ensures that consumer chains get information about which validators should validate on them.\nThis information consists of the opted in validators and their power on the consumer chains.\nNote that the validators' power on the consumer chains is a function of their stake locked on the provider chain."}),"\n",(0,i.jsx)(n.p,{children:"Consumer chains are run on infrastructure (virtual or physical machines) distinct from the provider chain, have their own configurations and operating requirements."}),"\n",(0,i.jsx)(n.p,{children:"Consumer chains are free to choose how they wish to operate and which modules to include.\nFor example, they can choose to use CosmWasm either in a permissioned or a permissionless way.\nAlso, consumer chains are free to perform software upgrades at any time without impacting the provider chain."}),"\n",(0,i.jsx)(n.h3,{id:"how-to-become-a-consumer-chain",children:"How to become a consumer chain?"}),"\n",(0,i.jsxs)(n.p,{children:["To become a consumer chain use this ",(0,i.jsx)(n.a,{href:"/interchain-security/consumer-development/onboarding",children:"checklist"})," and check the ",(0,i.jsx)(n.a,{href:"/interchain-security/consumer-development/app-integration",children:"App integration section"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"what-happens-to-consumers-if-the-provider-is-down",children:"What happens to consumers if the provider is down?"}),"\n",(0,i.jsxs)(n.p,{children:["In case the provider chain halts or experiences difficulties, the consumer chains will keep operating - the provider chain and consumer chains represent different networks that only share (a subset of) the validator set.\nAs the validators run separate infrastructure on these networks, ",(0,i.jsx)(n.strong,{children:(0,i.jsx)(n.em,{children:"the provider chain liveness does not impact the liveness of consumer chains"})}),"."]}),"\n",(0,i.jsxs)(n.p,{children:["Every consumer chain communicates with the provider chain via a CCV channel -- an IBC ordered channel.\nIf any of the packets sent over the CCV channel timeout (see the ",(0,i.jsx)(n.a,{href:"/interchain-security/build/modules/consumer#ccvtimeoutperiod",children:"CCVTimeoutPeriod param"}),"), then the channel is closed and, consequently, the consumer chain transitions to a Proof of Authority (PoA) chain.\nThis means that the validator set on the consumer will no longer be updated with information from the provider."]}),"\n",(0,i.jsx)(n.h3,{id:"what-happens-to-provider-if-any-of-the-consumers-are-down",children:"What happens to provider if any of the consumers are down?"}),"\n",(0,i.jsxs)(n.p,{children:[(0,i.jsx)(n.strong,{children:(0,i.jsx)(n.em,{children:"Consumer chains do not impact the livness of the provider chain."})}),"\nThe ICS protocol is concerned only with validator set management, and the only communication that the provider requires from the consumer is information about validator activity (essentially keeping the provider informed about slash events)."]}),"\n",(0,i.jsx)(n.h3,{id:"can-consumer-chains-have-their-own-token",children:"Can consumer chains have their own token?"}),"\n",(0,i.jsxs)(n.p,{children:["As any other Cosmos SDK chains, ",(0,i.jsx)(n.strong,{children:(0,i.jsx)(n.em,{children:"consumer chains can issue their own token"})})," and manage inflation parameters.\nNote that the ICS protocol does not impact the transaction fee system on the consumer chains.\nThis means consumer chains can use any token (including their own token) to pay gas fees.\nFor more details, see the ",(0,i.jsx)(n.a,{href:"/interchain-security/build/modules/democracy#tokenomics",children:"democracy modules"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"can-consumer-chains-have-their-own-governance",children:"Can consumer chains have their own governance?"}),"\n",(0,i.jsxs)(n.p,{children:["Yes. ICS allows consumer chains to ",(0,i.jsx)(n.strong,{children:(0,i.jsx)(n.em,{children:"separate governance from block production"})}),".\nValidator operators (with their stake locked on the provider) are responsible for block production, while ",(0,i.jsx)(n.em,{children:"representatives"})," (aka governators, governors) are responsible for on-chain governance.\nFor more details, see the ",(0,i.jsx)(n.a,{href:"/interchain-security/build/modules/democracy",children:"democracy modules"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"can-a-consumer-chain-modify-its-power-shaping-parameters",children:"Can a consumer chain modify its power shaping parameters?"}),"\n",(0,i.jsxs)(n.p,{children:["Yes, by issuing a ",(0,i.jsx)(n.code,{children:"MsgUpdateConsumer"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"can-a-top-n-consumer-chain-become-opt-in-or-vice-versa",children:"Can a Top N consumer chain become Opt-In or vice versa?"}),"\n",(0,i.jsxs)(n.p,{children:["Yes, by issuing a ",(0,i.jsx)(n.code,{children:"MsgUpdateConsumer"})," (see ",(0,i.jsx)(n.a,{href:"/interchain-security/features/permissionless#transform-an-opt-in-chain-to-top-n-and-vice-versa",children:"Permissionless ICS"}),")"]}),"\n",(0,i.jsx)(n.h2,{id:"validators",children:"Validators"}),"\n",(0,i.jsx)(n.h3,{id:"how-can-validators-opt-in-to-validate-a-consumer-chain",children:"How can validators opt in to validate a consumer chain?"}),"\n",(0,i.jsxs)(n.p,{children:["Check the ",(0,i.jsx)(n.a,{href:"/interchain-security/validators/partial-set-security-for-validators#how-to-opt-in-to-a-consumer-chain",children:"validator guide to Partial Set Security"}),"."]}),"\n",(0,i.jsx)(n.p,{children:"An important note is that validator the top N% of the provider chain validator set are automatically opted in on Top N consumer chains."}),"\n",(0,i.jsx)(n.h3,{id:"can-validators-opt-in-to-an-opt-in-chain-after-the-spawn-time-if-nobody-else-opted-in",children:"Can validators opt in to an Opt-in chain after the spawn time if nobody else opted in?"}),"\n",(0,i.jsx)(n.p,{children:"No, the consumer chain does not launch if nobody opted in by the spawn time. At least one validator, regardless of its voting power, must opt in before the spawn time in order for the chain can start."}),"\n",(0,i.jsx)(n.h3,{id:"how-does-a-validator-know-which-consumers-chains-it-has-to-validate",children:"How does a validator know which consumers chains it has to validate?"}),"\n",(0,i.jsxs)(n.p,{children:["In order for a validator to keep track of all the chains it has to validate, the validator can use the\n",(0,i.jsxs)(n.a,{href:"/interchain-security/validators/partial-set-security-for-validators#which-chains-does-a-validator-have-to-validate",children:[(0,i.jsx)(n.code,{children:"has-to-validate"})," query"]}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"how-many-chains-can-a-validator-opt-in-to",children:"How many chains can a validator opt in to?"}),"\n",(0,i.jsxs)(n.p,{children:["There is ",(0,i.jsx)(n.strong,{children:"no"})," limit in the number of consumers chains a validator can choose to opt in to."]}),"\n",(0,i.jsx)(n.h3,{id:"how-can-validators-assign-consumer-keys",children:"How can validators assign consumer keys?"}),"\n",(0,i.jsxs)(n.p,{children:["Check the ",(0,i.jsx)(n.a,{href:"/interchain-security/features/key-assignment",children:"Key Assignment guide"})," for specific instructions."]}),"\n",(0,i.jsxs)(n.p,{children:["Validators are strongly recommended to assign a separate key for each consumer chain and ",(0,i.jsx)(n.strong,{children:"not"})," reuse the provider key across consumer chains for security reasons."]}),"\n",(0,i.jsx)(n.p,{children:"Also note that validators can assign consensus keys before a consumer chain is launched (e.g., during the voting period for Top N consumer chains)."}),"\n",(0,i.jsx)(n.h3,{id:"what-are-the-benefits-for-validators-running-consumer-chains",children:"What are the benefits for validators running consumer chains?"}),"\n",(0,i.jsxs)(n.p,{children:["The consumer chains sends a portion of its block rewards (e.g., transaction fees and inflation) to the provider chain as defined by the ",(0,i.jsx)(n.a,{href:"/interchain-security/build/modules/consumer#consumerredistributionfraction",children:"ConsumerRedistributionFraction param"}),".\nThese rewards are sent periodically to the provider (via IBC transfers), where they are distributed ",(0,i.jsx)(n.strong,{children:"ONLY"})," to the ",(0,i.jsx)(n.em,{children:"opted in"})," validators and their delegators. For more details, see the ",(0,i.jsx)(n.a,{href:"/interchain-security/features/reward-distribution",children:"Reward Distribution feature"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"can-validators-set-per-consumer-chain-commission-rates",children:"Can validators set per consumer chain commission rates?"}),"\n",(0,i.jsxs)(n.p,{children:["Yes. See the ",(0,i.jsx)(n.a,{href:"/interchain-security/validators/partial-set-security-for-validators#how-to-set-specific-per-consumer-chain-commission-rate",children:"validator guide to Partial Set Security"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"what-are-the-risks-for-validators-running-consumer-chains",children:"What are the risks for validators running consumer chains?"}),"\n",(0,i.jsx)(n.p,{children:"Validators that perform an equivocation or a light-client attack on a consumer chain are slashed on the provider chain. This is done by submitting a proof of the equivocation or the light-client attack to the provider chain."}),"\n",(0,i.jsxs)(n.p,{children:["In addition, consumer chains send IBC packets via the CCV channels informing the provider when opted in validators should be jailed for downtime.\nIt is important to notice that ",(0,i.jsx)(n.em,{children:"validators are not slashed for downtime on consumer chains"}),".\nThe downtime logic is custom to the consumer chain.\nFor example, Cosmos SDK chains can use the ",(0,i.jsx)(n.a,{href:"https://docs.cosmos.network/v0.50/build/modules/slashing",children:"slashing module"})," to configure the downtime window."]}),"\n",(0,i.jsxs)(n.p,{children:["For more details, see the ",(0,i.jsx)(n.a,{href:"/interchain-security/features/slashing",children:"slashing feature"}),"."]}),"\n",(0,i.jsx)(n.h3,{id:"can-validators-run-the-provider-and-consumer-chains-on-the-same-machine",children:"Can validators run the provider and consumer chains on the same machine?"}),"\n",(0,i.jsx)(n.p,{children:"In theory yes.\nIn practice, we recommend validators to run the provider and consumer chains in separate environments for fault containment, i.e., failures of one machine do not impact the entire system."}),"\n",(0,i.jsx)(n.h3,{id:"can-validators-opt-out-of-validating-a-consumer-chain",children:"Can validators opt out of validating a consumer chain?"}),"\n",(0,i.jsx)(n.p,{children:"Validators can always opt out from an Opt-In consumer chain.\nValidators can only opt out from a TopN chain if they do not belong to the top N% validators."}),"\n",(0,i.jsx)(n.h3,{id:"can-all-validators-opt-out-of-an-opt-in-chain",children:"Can all validators opt out of an Opt-in chain?"}),"\n",(0,i.jsxs)(n.p,{children:["Note that if all validators opt out of an Opt-In consumer chain, then the chain will halt with a consensus failure upon receiving the ",(0,i.jsx)(n.code,{children:"VSCPacket"})," with an empty validator set."]}),"\n",(0,i.jsx)(n.h3,{id:"how-to-connect-to-the-testnets",children:"How to connect to the testnets?"}),"\n",(0,i.jsxs)(n.p,{children:["Check out the ",(0,i.jsx)(n.a,{href:"/interchain-security/validators/joining-testnet",children:"Joining Interchain Security testnet"})," section."]}),"\n",(0,i.jsx)(n.h2,{id:"integrators",children:"Integrators"}),"\n",(0,i.jsx)(n.h3,{id:"which-relayers-are-supported",children:"Which relayers are supported?"}),"\n",(0,i.jsx)(n.p,{children:"Currently supported versions:"}),"\n",(0,i.jsxs)(n.ul,{children:["\n",(0,i.jsxs)(n.li,{children:["Hermes ",(0,i.jsx)(n.code,{children:"v1.8.0+"})]}),"\n"]}),"\n",(0,i.jsx)(n.h3,{id:"how-to-check-when-the-next-validator-update-will-be-sent-to-the-consumer-chains",children:"How to check when the next validator update will be sent to the consumer chains?"}),"\n",(0,i.jsxs)(n.p,{children:["Validator updates are sent to consumer chains every ",(0,i.jsx)(n.code,{children:"BlocksPerEpoch"})," blocks.\nDepending on the status of relayers between the Hub and the consumer chains,\nit might take a while for the validator updates to be processed and applied on the consumer chains."]}),"\n",(0,i.jsx)(n.p,{children:"To query how many blocks are left until the next epoch starts,\nrun the following command:"}),"\n",(0,i.jsx)(n.pre,{children:(0,i.jsx)(n.code,{className:"language-bash",children:"interchain-security-pd query provider blocks-until-next-epoch\n"})})]})}function l(e={}){const{wrapper:n}={...(0,t.a)(),...e.components};return n?(0,i.jsx)(n,{...e,children:(0,i.jsx)(d,{...e})}):d(e)}},1151:(e,n,a)=>{a.d(n,{Z:()=>r,a:()=>s});var i=a(7294);const t={},o=i.createContext(t);function s(e){const n=i.useContext(o);return i.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function r(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(t):e.components||t:s(e.components),i.createElement(o.Provider,{value:n},e.children)}}}]);