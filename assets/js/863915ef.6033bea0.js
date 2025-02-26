"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[1751],{3054:(e,n,t)=>{t.r(n),t.d(n,{assets:()=>c,contentTitle:()=>s,default:()=>d,frontMatter:()=>o,metadata:()=>r,toc:()=>l});var i=t(5893),a=t(1151);const o={sidebar_position:3,title:"Onboarding Checklist"},s="Consumer Onboarding Checklist",r={id:"consumer-development/onboarding",title:"Onboarding Checklist",description:"The following checklists will aid in onboarding a new consumer chain to interchain security.",source:"@site/versioned_docs/version-v6.1.0/consumer-development/onboarding.md",sourceDirName:"consumer-development",slug:"/consumer-development/onboarding",permalink:"/interchain-security/v6.1.0/consumer-development/onboarding",draft:!1,unlisted:!1,tags:[],version:"v6.1.0",sidebarPosition:3,frontMatter:{sidebar_position:3,title:"Onboarding Checklist"},sidebar:"tutorialSidebar",previous:{title:"Consumer Chain Governance",permalink:"/interchain-security/v6.1.0/consumer-development/consumer-chain-governance"},next:{title:"Offboarding Checklist",permalink:"/interchain-security/v6.1.0/consumer-development/offboarding"}},c={},l=[{value:"1. Complete testing &amp; integration",id:"1-complete-testing--integration",level:2},{value:"2. Create an Onboarding Repository",id:"2-create-an-onboarding-repository",level:2},{value:"3. Submit a Governance Proposal",id:"3-submit-a-governance-proposal",level:2},{value:"4. Launch",id:"4-launch",level:2}];function h(e){const n={a:"a",code:"code",em:"em",h1:"h1",h2:"h2",input:"input",li:"li",p:"p",pre:"pre",ul:"ul",...(0,a.a)(),...e.components};return(0,i.jsxs)(i.Fragment,{children:[(0,i.jsx)(n.h1,{id:"consumer-onboarding-checklist",children:"Consumer Onboarding Checklist"}),"\n",(0,i.jsx)(n.p,{children:"The following checklists will aid in onboarding a new consumer chain to interchain security."}),"\n",(0,i.jsxs)(n.p,{children:["Additionally, you can check the ",(0,i.jsx)(n.a,{href:"https://github.com/cosmos/testnets/blob/master/interchain-security/CONSUMER_LAUNCH_GUIDE.md",children:"testnet repo"})," for a comprehensive guide on preparing and launching consumer chains."]}),"\n",(0,i.jsx)(n.h2,{id:"1-complete-testing--integration",children:"1. Complete testing & integration"}),"\n",(0,i.jsxs)(n.ul,{className:"contains-task-list",children:["\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","test integration with gaia"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","test your protocol with supported relayer versions (minimum hermes 1.4.1)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","reach out to the ICS team if you are facing issues"]}),"\n"]}),"\n",(0,i.jsx)(n.h2,{id:"2-create-an-onboarding-repository",children:"2. Create an Onboarding Repository"}),"\n",(0,i.jsx)(n.p,{children:"To help validators and other node runners onboard onto your chain, please prepare a repository with information on how to run your chain."}),"\n",(0,i.jsx)(n.p,{children:"This should include (at minimum):"}),"\n",(0,i.jsxs)(n.ul,{className:"contains-task-list",children:["\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","genesis.json without CCV data (before the proposal passes)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","genesis.json with CCV data (after spawn time passes). Check if CCV data needs to be transformed (see ",(0,i.jsx)(n.a,{href:"/interchain-security/v6.1.0/consumer-development/consumer-genesis-transformation",children:"Transform Consumer Genesis"}),")"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","information about relevant seed/peer nodes you are running"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","relayer information (compatible versions)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","copy of your governance proposal (as JSON)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","a script showing how to start your chain and connect to peers (optional)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","take feedback from other developers, validators and community regarding your onboarding repo and make improvements where applicable"]}),"\n"]}),"\n",(0,i.jsxs)(n.p,{children:["Example of such a repository can be found ",(0,i.jsx)(n.a,{href:"https://github.com/hyphacoop/ics-testnets/tree/main/game-of-chains-2022/sputnik",children:"here"}),"."]}),"\n",(0,i.jsx)(n.h2,{id:"3-submit-a-governance-proposal",children:"3. Submit a Governance Proposal"}),"\n",(0,i.jsxs)(n.p,{children:["Before you submit a ",(0,i.jsx)(n.code,{children:"ConsumerChainAddition"})," proposal, please consider allowing at least a day between your proposal passing and the chain spawn time. This will allow the validators, other node operators and the community to prepare for the chain launch.\nIf possible, please set your spawn time so people from different parts of the globe can be available in case of emergencies. Ideally, you should set your spawn time to be between 12:00 UTC and 20:00 UTC so most validator operators are available and ready to respond to any issues."]}),"\n",(0,i.jsxs)(n.p,{children:["Additionally, reach out to the community via the ",(0,i.jsx)(n.a,{href:"https://forum.cosmos.network/",children:"forum"})," to formalize your intention to become an ICS consumer, gather community support and accept feedback from the community, validators and developers."]}),"\n",(0,i.jsxs)(n.ul,{className:"contains-task-list",children:["\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","determine your chain's spawn time"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","determine consumer chain parameters to be put in the proposal"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","take note to include a link to your onboarding repository"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","describe the purpose and benefits of running your chain"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","determine whether your chain should be an Opt-In chain or a Top N chain (see ",(0,i.jsx)(n.a,{href:"/interchain-security/v6.1.0/features/partial-set-security",children:"Partial Set Security"}),")"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","if desired, decide on power-shaping parameters (see ",(0,i.jsx)(n.a,{href:"/interchain-security/v6.1.0/features/power-shaping",children:"Power Shaping"}),")"]}),"\n"]}),"\n",(0,i.jsx)(n.p,{children:"Example of a consumer chain addition proposal."}),"\n",(0,i.jsx)(n.pre,{children:(0,i.jsx)(n.code,{className:"language-js",children:'// ConsumerAdditionProposal is a governance proposal on the provider chain to spawn a new consumer chain.\n// If it passes, if the top_N parameter is not equal to 0, the top N% of validators by voting power on the provider chain are expected to validate the consumer chain at spawn time.\n// Otherwise, only validators that opted in during the proposal period are expected to validate the consumer chain at spawn time.\n// It is recommended that spawn time occurs after the proposal end time.\n{\n    // Title of the proposal\n    "title": "Add consumer chain",\n    // Description of the proposal\n    // format the text as a .md file and include the file in your onboarding repository\n    "description": ".md description of your chain and all other relevant information",\n    // Proposed chain-id of the new consumer chain.\n    // Must be unique from all other consumer chain ids of the executing provider chain.\n    "chain_id": "newchain-1",\n    // Initial height of new consumer chain.\n    // For a completely new chain, this will be {0,1}.\n    "initial_height" : {\n        "revision_height": 0,\n        "revision_number": 1,\n    },\n    // Hash of the consumer chain genesis state without the consumer CCV module genesis params.\n    // It is used for off-chain confirmation of genesis.json validity by validators and other parties.\n    "genesis_hash": "d86d756e10118e66e6805e9cc476949da2e750098fcc7634fd0cc77f57a0b2b0",\n    // Hash of the consumer chain binary that should be run by validators on chain initialization.\n    // It is used for off-chain confirmation of binary validity by validators and other parties.\n    "binary_hash": "376cdbd3a222a3d5c730c9637454cd4dd925e2f9e2e0d0f3702fc922928583f1",\n    // Time on the provider chain at which the consumer chain genesis is finalized and validators\n    // will be responsible for starting their consumer chain validator node.\n    "spawn_time": "2023-02-28T20:40:00.000000Z",\n    // Unbonding period for the consumer chain.\n    // It should be smaller than that of the provider.\n    "unbonding_period": 86400000000000,\n    // Timeout period for CCV related IBC packets.\n    // Packets are considered timed-out after this interval elapses.\n    "ccv_timeout_period": 259200000000000,\n    // IBC transfer packets will timeout after this interval elapses.\n    "transfer_timeout_period": 1800000000000,\n    // The fraction of tokens allocated to the consumer redistribution address during distribution events.\n    // The fraction is a string representing a decimal number. For example "0.75" would represent 75%.\n    // The reward amount distributed to the provider is calculated as: 1 - consumer_redistribution_fraction.\n    "consumer_redistribution_fraction": "0.75",\n    // BlocksPerDistributionTransmission is the number of blocks between IBC token transfers from the consumer chain to the provider chain.\n    // eg. send rewards to the provider every 1000 blocks\n    "blocks_per_distribution_transmission": 1000,\n    // The number of historical info entries to persist in store.\n    // This param is a part of the cosmos sdk staking module. In the case of\n    // a ccv enabled consumer chain, the ccv module acts as the staking module.\n    "historical_entries": 10000,\n    // The ID of a token transfer channel used for the Reward Distribution\n\t// sub-protocol. If DistributionTransmissionChannel == "", a new transfer\n\t// channel is created on top of the same connection as the CCV channel.\n\t// Note that transfer_channel_id is the ID of the channel end on the consumer chain.\n    // it is most relevant for chains performing a standalone to consumer changeover\n    // in order to maintain the existing ibc transfer channel\n    "distribution_transmission_channel": "channel-123",\n    // Corresponds to the percentage of validators that have to validate the chain under the Top N case.\n    // For example, 53 corresponds to a Top 53% chain, meaning that the top 53% provider validators by voting power\n    // have to validate the proposed consumer chain. top_N can either be 0 or any value in [50, 100].\n    // A chain can join with top_N == 0 as an Opt In chain, or with top_N \u2208 [50, 100] as a Top N chain.\n    "top_N": 95,\n    // Corresponds to the maximum power (percentage-wise) a validator can have on the consumer chain. For instance, if\n    // `validators_power_cap` is set to 32, it means that no validator can have more than 32% of the voting power on the\n    // consumer chain. Note that this might not be feasible. For example, think of a consumer chain with only\n    // 5 validators and with `validators_power_cap` set to 10%. In such a scenario, at least one validator would need\n    // to have more than 20% of the total voting power. Therefore, `validators_power_cap` operates on a best-effort basis.\n    "validators_power_cap": 0,\n    // Corresponds to the maximum number of validators that can validate a consumer chain.\n    // Only applicable to Opt In chains. Setting `validator_set_cap` on a Top N chain is a no-op.\n    "validator_set_cap": 0,\n    // Corresponds to a list of provider consensus addresses of validators that are the ONLY ones that can validate\n    // the consumer chain.\n    "allowlist": [],\n    // Corresponds to a list of provider consensus addresses of validators that CANNOT validate the consumer chain.\n    "denylist": [],\n    // Corresponds to the minimal amount of (provider chain) stake required to validate on the consumer chain.\n    "min_stake": 0,\n    // Corresponds to whether inactive validators are allowed to validate the consumer chain.\n    "allow_inactive_vals": false\n}\n'})}),"\n",(0,i.jsx)(n.h2,{id:"4-launch",children:"4. Launch"}),"\n",(0,i.jsxs)(n.p,{children:["The consumer chain starts after at least 66.67% of its voting power comes online.\nNote that this means 66.67% of the voting power in the ",(0,i.jsx)(n.em,{children:"consumer"})," validator set, which will be comprised of all validators that either opted in to the chain or are part of the top N% of the provider chain (and are thus automatically opted in).\nThe consumer chain is considered interchain secured once the appropriate CCV channels are established and the first validator set update is propagated from the provider to the consumer"]}),"\n",(0,i.jsxs)(n.ul,{className:"contains-task-list",children:["\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","provide a repo with onboarding instructions for validators (it should already be listed in the proposal)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","genesis.json with ccv data populated (MUST contain the initial validator set)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","maintenance & emergency contact info (relevant discord, telegram, slack or other communication channels)"]}),"\n",(0,i.jsxs)(n.li,{className:"task-list-item",children:[(0,i.jsx)(n.input,{type:"checkbox",disabled:!0})," ","have a block explorer in place to track chain activity & health"]}),"\n"]})]})}function d(e={}){const{wrapper:n}={...(0,a.a)(),...e.components};return n?(0,i.jsx)(n,{...e,children:(0,i.jsx)(h,{...e})}):h(e)}},1151:(e,n,t)=>{t.d(n,{Z:()=>r,a:()=>s});var i=t(7294);const a={},o=i.createContext(a);function s(e){const n=i.useContext(o);return i.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function r(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(a):e.components||a:s(e.components),i.createElement(o.Provider,{value:n},e.children)}}}]);