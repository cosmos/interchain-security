"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[4436],{4050:(e,i,t)=>{t.r(i),t.d(i,{assets:()=>c,contentTitle:()=>s,default:()=>d,frontMatter:()=>a,metadata:()=>o,toc:()=>l});var n=t(5893),r=t(1151);const a={sidebar_position:2},s="Terminology",o={id:"introduction/terminology",title:"Terminology",description:"You may have heard of one or multiple buzzwords thrown around in the cosmos and wider crypto ecosystem such shared security, interchain security and replicated security.",source:"@site/versioned_docs/version-v6.4.0/introduction/terminology.md",sourceDirName:"introduction",slug:"/introduction/terminology",permalink:"/interchain-security/v6.4.0/introduction/terminology",draft:!1,unlisted:!1,tags:[],version:"v6.4.0",sidebarPosition:2,frontMatter:{sidebar_position:2},sidebar:"tutorialSidebar",previous:{title:"Overview",permalink:"/interchain-security/v6.4.0/introduction/overview"},next:{title:"Key Assignment",permalink:"/interchain-security/v6.4.0/features/key-assignment"}},c={},l=[{value:"Shared Security",id:"shared-security",level:2},{value:"Interchain Security (ICS)",id:"interchain-security-ics",level:2},{value:"Consumer Chain",id:"consumer-chain",level:2},{value:"Replicated Security",id:"replicated-security",level:2},{value:"Partial Set Security (PSS)",id:"partial-set-security-pss",level:2},{value:"Permissionless ICS",id:"permissionless-ics",level:2},{value:"Standalone Chain",id:"standalone-chain",level:2},{value:"Changeover Procedure",id:"changeover-procedure",level:2},{value:"Mesh Security",id:"mesh-security",level:2}];function h(e){const i={a:"a",h1:"h1",h2:"h2",p:"p",strong:"strong",...(0,r.a)(),...e.components};return(0,n.jsxs)(n.Fragment,{children:[(0,n.jsx)(i.h1,{id:"terminology",children:"Terminology"}),"\n",(0,n.jsx)(i.p,{children:"You may have heard of one or multiple buzzwords thrown around in the cosmos and wider crypto ecosystem such shared security, interchain security and replicated security.\nThese and other terms are clarified below."}),"\n",(0,n.jsx)(i.h2,{id:"shared-security",children:"Shared Security"}),"\n",(0,n.jsx)(i.p,{children:"Shared Security is a family of technologies that include optimistic rollups, zk-rollups, sharding and Interchain Security.\nBasically, any protocol or technology that can allow one blockchain to lend/share its proof-of-stake security with another blockchain or off-chain process."}),"\n",(0,n.jsx)(i.h2,{id:"interchain-security-ics",children:"Interchain Security (ICS)"}),"\n",(0,n.jsx)(i.p,{children:"Interchain Security is the Cosmos-specific category of Shared Security that uses IBC (Inter-Blockchain Communication)."}),"\n",(0,n.jsx)(i.h2,{id:"consumer-chain",children:"Consumer Chain"}),"\n",(0,n.jsx)(i.p,{children:"Chain that is secured by the validator set of the provider, instead of its own.\nInterchain Security allows a subset of the provider chain's validator set to validate blocks on the consumer chain."}),"\n",(0,n.jsx)(i.h2,{id:"replicated-security",children:"Replicated Security"}),"\n",(0,n.jsxs)(i.p,{children:['A particular protocol/implementation of Interchain Security that fully replicates the security and decentralization of a validator set across multiple blockchains.\nReplicated security has also been referred to as "Interchain Security V1", a legacy term for the same protocol.\nThat is, a "provider chain" such as the Cosmos Hub can share its exact validator set with multiple consumer chains by communicating changes in its validator set over IBC.\nNote that since the introduction of ',(0,n.jsx)(i.a,{href:"#partial-set-security-pss",children:"Partial Set Security"}),", a TopN consumer chain with N 100% fully replicates the security and decentralization of the provider chain."]}),"\n",(0,n.jsx)(i.h2,{id:"partial-set-security-pss",children:"Partial Set Security (PSS)"}),"\n",(0,n.jsx)(i.p,{children:'A major feature of Interchain Security (also referred to as "Interchain Security V2") that allows a provider chain to share only a subset of its validator set with a consumer chain.\nThis subset can be determined by the top N% validators by voting power, or by validators opting in to validate the consumer chain.\nPSS allows for more flexible security tradeoffs than Replicated Security.'}),"\n",(0,n.jsx)(i.h2,{id:"permissionless-ics",children:"Permissionless ICS"}),"\n",(0,n.jsxs)(i.p,{children:[(0,n.jsx)(i.a,{href:"/interchain-security/v6.4.0/features/permissionless",children:"Permissionless ICS"})," is the latest version of ICS that allows to launch Opt In chains in\na permissionless way (i.e., without requiring a governance proposal)."]}),"\n",(0,n.jsx)(i.h2,{id:"standalone-chain",children:"Standalone Chain"}),"\n",(0,n.jsx)(i.p,{children:"Chain that is secured by its own validator set. This chain does not participate in Interchain Security."}),"\n",(0,n.jsx)(i.h2,{id:"changeover-procedure",children:"Changeover Procedure"}),"\n",(0,n.jsxs)(i.p,{children:["Chains that were not initially launched as consumers of Interchain Security can still participate in the protocol and leverage the economic security of the provider chain.\nThe process where a standalone chain transitions to being a replicated consumer chain is called the ",(0,n.jsx)(i.strong,{children:"changeover procedure"})," and is part of the ICS protocol.\nAfter the changeover, the new consumer chain will retain all existing state, including the IBC clients, connections and channels already established by the chain."]}),"\n",(0,n.jsx)(i.h2,{id:"mesh-security",children:"Mesh Security"}),"\n",(0,n.jsxs)(i.p,{children:["A protocol built on IBC that allows delegators on a Cosmos chain to re-delegate their stake to validators in another chain's own validator set, using the original chain's token (which remains bonded on the original chain). For a deeper exploration of Mesh Security, see ",(0,n.jsx)(i.a,{href:"https://informal.systems/blog/replicated-vs-mesh-security",children:"Replicated vs. Mesh Security on the Informal Blog"}),"."]})]})}function d(e={}){const{wrapper:i}={...(0,r.a)(),...e.components};return i?(0,n.jsx)(i,{...e,children:(0,n.jsx)(h,{...e})}):h(e)}},1151:(e,i,t)=>{t.d(i,{Z:()=>o,a:()=>s});var n=t(7294);const r={},a=n.createContext(r);function s(e){const i=n.useContext(a);return n.useMemo((function(){return"function"==typeof e?e(i):{...i,...e}}),[i,e])}function o(e){let i;return i=e.disableParentContext?"function"==typeof e.components?e.components(r):e.components||r:s(e.components),n.createElement(a.Provider,{value:i},e.children)}}}]);