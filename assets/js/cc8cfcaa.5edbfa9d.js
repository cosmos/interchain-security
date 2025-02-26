"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[6772],{4094:(e,n,t)=>{t.r(n),t.d(n,{assets:()=>c,contentTitle:()=>r,default:()=>m,frontMatter:()=>s,metadata:()=>i,toc:()=>h});var o=t(5893),a=t(1151);const s={sidebar_position:2},r="Consumer Chain Governance",i={id:"consumer-development/consumer-chain-governance",title:"Consumer Chain Governance",description:'Different consumer chains can do governance in different ways. However, no matter what the governance method is, there are a few settings specifically related to consensus that consumer chain governance cannot change. We\'ll cover what these are in the "Whitelist" section below.',source:"@site/versioned_docs/version-v6.3.0/consumer-development/consumer-chain-governance.md",sourceDirName:"consumer-development",slug:"/consumer-development/consumer-chain-governance",permalink:"/interchain-security/v6.3.0/consumer-development/consumer-chain-governance",draft:!1,unlisted:!1,tags:[],version:"v6.3.0",sidebarPosition:2,frontMatter:{sidebar_position:2},sidebar:"tutorialSidebar",previous:{title:"Developing an ICS consumer chain",permalink:"/interchain-security/v6.3.0/consumer-development/app-integration"},next:{title:"Onboarding Checklist",permalink:"/interchain-security/v6.3.0/consumer-development/onboarding"}},c={},h=[{value:"Democracy module",id:"democracy-module",level:2},{value:"CosmWasm",id:"cosmwasm",level:2},{value:"The Whitelist",id:"the-whitelist",level:2}];function l(e){const n={a:"a",h1:"h1",h2:"h2",p:"p",...(0,a.a)(),...e.components};return(0,o.jsxs)(o.Fragment,{children:[(0,o.jsx)(n.h1,{id:"consumer-chain-governance",children:"Consumer Chain Governance"}),"\n",(0,o.jsx)(n.p,{children:'Different consumer chains can do governance in different ways. However, no matter what the governance method is, there are a few settings specifically related to consensus that consumer chain governance cannot change. We\'ll cover what these are in the "Whitelist" section below.'}),"\n",(0,o.jsx)(n.h2,{id:"democracy-module",children:"Democracy module"}),"\n",(0,o.jsx)(n.p,{children:"The democracy module provides a governance experience identical to what exists on a standalone Cosmos chain, with one small but important difference. On a standalone Cosmos chain validators can act as representatives for their delegators by voting with their stake, but only if the delegator themselves does not vote. This is a lightweight form of liquid democracy."}),"\n",(0,o.jsx)(n.p,{children:"Using the democracy module on a consumer chain is the exact same experience, except for the fact that it is not the actual validator set of the chain (since it is a consumer chain, these are the Cosmos Hub validators) acting as representatives. Instead, there is a separate representative role who token holders can delegate to and who can perform the functions that validators do in Cosmos governance, without participating in proof of stake consensus."}),"\n",(0,o.jsxs)(n.p,{children:["For an example, see the ",(0,o.jsx)(n.a,{href:"https://github.com/cosmos/interchain-security/tree/main/app/consumer-democracy",children:"Democracy Consumer"})]}),"\n",(0,o.jsx)(n.h2,{id:"cosmwasm",children:"CosmWasm"}),"\n",(0,o.jsx)(n.p,{children:"There are several great DAO and governance frameworks written as CosmWasm contracts. These can be used as the main governance system for a consumer chain. Actions triggered by the CosmWasm governance contracts are able to affect parameters and trigger actions on the consumer chain."}),"\n",(0,o.jsxs)(n.p,{children:["For an example, see ",(0,o.jsx)(n.a,{href:"https://github.com/neutron-org/neutron/",children:"Neutron"}),"."]}),"\n",(0,o.jsx)(n.h2,{id:"the-whitelist",children:"The Whitelist"}),"\n",(0,o.jsxs)(n.p,{children:["Not everything on a consumer chain can be changed by the consumer's governance. Some settings having to do with consensus etc. can only be changed by the provider chain. Consumer chains include a whitelist of parameters that are allowed to be changed by the consumer chain governance. For an example, see ",(0,o.jsx)(n.a,{href:"https://github.com/neutron-org/neutron/blob/main/app/proposals_allowlisting.go",children:"Neutron's"})," whitelist."]})]})}function m(e={}){const{wrapper:n}={...(0,a.a)(),...e.components};return n?(0,o.jsx)(n,{...e,children:(0,o.jsx)(l,{...e})}):l(e)}},1151:(e,n,t)=>{t.d(n,{Z:()=>i,a:()=>r});var o=t(7294);const a={},s=o.createContext(a);function r(e){const n=o.useContext(s);return o.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function i(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(a):e.components||a:r(e.components),o.createElement(s.Provider,{value:n},e.children)}}}]);