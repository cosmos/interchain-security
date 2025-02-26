"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[6494],{326:(e,n,i)=>{i.r(n),i.d(n,{assets:()=>a,contentTitle:()=>o,default:()=>l,frontMatter:()=>r,metadata:()=>h,toc:()=>d});var t=i(5893),s=i(1151);const r={sidebar_position:22,title:"Consumer Chain Clients"},o="ADR 021: Consumer Chain Clients",h={id:"adrs/adr-021-consumer-chain-clients",title:"Consumer Chain Clients",description:"Changelog",source:"@site/docs/adrs/adr-021-consumer-chain-clients.md",sourceDirName:"adrs",slug:"/adrs/adr-021-consumer-chain-clients",permalink:"/interchain-security/adrs/adr-021-consumer-chain-clients",draft:!1,unlisted:!1,tags:[],version:"current",sidebarPosition:22,frontMatter:{sidebar_position:22,title:"Consumer Chain Clients"},sidebar:"tutorialSidebar",previous:{title:"Customizable Slashing and Jailing",permalink:"/interchain-security/adrs/adr-020-cutomizable_slashing_and_jailing"},next:{title:"Fault Resolutions",permalink:"/interchain-security/adrs/adr-022-fault-resolutions"}},a={},d=[{value:"Changelog",id:"changelog",level:2},{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"IBC Client Updates",id:"ibc-client-updates",level:3},{value:"Updating Consumers&#39; IBC Clients",id:"updating-consumers-ibc-clients",level:3},{value:"Decision",id:"decision",level:2},{value:"Store Provider Timestamps",id:"store-provider-timestamps",level:3},{value:"State",id:"state",level:4},{value:"Query",id:"query",level:4},{value:"ICS Conditional Clients on the Provider",id:"ics-conditional-clients-on-the-provider",level:3},{value:"Consequences",id:"consequences",level:2},{value:"Positive",id:"positive",level:3},{value:"Negative",id:"negative",level:3},{value:"Neutral",id:"neutral",level:3},{value:"References",id:"references",level:2}];function c(e){const n={a:"a",blockquote:"blockquote",code:"code",em:"em",h1:"h1",h2:"h2",h3:"h3",h4:"h4",img:"img",li:"li",p:"p",pre:"pre",strong:"strong",ul:"ul",...(0,s.a)(),...e.components},{Details:r}=n;return r||function(e,n){throw new Error("Expected "+(n?"component":"object")+" `"+e+"` to be defined: you likely forgot to import, pass, or provide it.")}("Details",!0),(0,t.jsxs)(t.Fragment,{children:[(0,t.jsx)(n.h1,{id:"adr-021-consumer-chain-clients",children:"ADR 021: Consumer Chain Clients"}),"\n",(0,t.jsx)(n.h2,{id:"changelog",children:"Changelog"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsx)(n.li,{children:"2024-08-14: Initial draft of ADR"}),"\n"]}),"\n",(0,t.jsx)(n.h2,{id:"status",children:"Status"}),"\n",(0,t.jsx)(n.p,{children:"Proposed"}),"\n",(0,t.jsx)(n.h2,{id:"context",children:"Context"}),"\n",(0,t.jsxs)(n.blockquote,{children:["\n",(0,t.jsxs)(n.p,{children:["In this document, ",(0,t.jsx)(n.em,{children:"host"})," chain and ",(0,t.jsx)(n.em,{children:"remote"})," chain are used in the following context: a light client of a remote chain is in the state of a host chain."]}),"\n"]}),"\n",(0,t.jsx)(n.h3,{id:"ibc-client-updates",children:"IBC Client Updates"}),"\n",(0,t.jsx)(n.p,{children:"IBC Client Updates require two pieces of information:"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsxs)(n.li,{children:["\n",(0,t.jsx)(n.p,{children:"A header (and a validator set) that originates from the consensus engine of the remote chain, i.e.,"}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-protobuf",children:"message Header {\n  .tendermint.types.SignedHeader signed_header = 1\n  .tendermint.types.ValidatorSet validator_set  = 2 \n  ibc.core.client.v1.Height      trusted_height = 3\n  .tendermint.types.ValidatorSet trusted_validators = 4\n}\n"})}),"\n",(0,t.jsxs)(n.p,{children:["Note that the header also contain ",(0,t.jsx)(n.code,{children:"Commit"})," information, i.e., the signatures that got the block committed."]}),"\n"]}),"\n",(0,t.jsxs)(n.li,{children:["\n",(0,t.jsxs)(n.p,{children:["The client state, that is initialized when the client is created and then maintained through client updates.\nTwo important fields of the client state are the ",(0,t.jsx)(n.code,{children:"UnbondingPeriod"})," (i.e., duration of the staking unbonding period) and the ",(0,t.jsx)(n.code,{children:"TrustingPeriod"}),", which must be smaller than the ",(0,t.jsx)(n.code,{children:"UnbondingPeriod"})," (see the ",(0,t.jsx)(n.em,{children:(0,t.jsx)(n.strong,{children:"Tendermint Security Model"})})," in the ",(0,t.jsx)(n.a,{href:"https://arxiv.org/pdf/2010.07031",children:"Tendermint Light Client paper"}),").\nThe ",(0,t.jsx)(n.code,{children:"TrustingPeriod"})," is ",(0,t.jsx)(n.em,{children:"the duration, since the timestamp of the latest header the client got updated to, during which new headers are accepted for updating the client"}),".\nThe ",(0,t.jsx)(n.code,{children:"UnbondingPeriod"})," originates from the application of the remote chain (i.e., a staking module param), which means the ",(0,t.jsx)(n.code,{children:"TrustingPeriod"})," originates from the remote application as well."]}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-golang",children:"if HeaderExpired(trustedHeader, trustingPeriod, now) {\n\treturn ErrOldHeaderExpired{trustedHeader.Time.Add(trustingPeriod), now}\n}\n\t\n// HeaderExpired return true if the given header expired.\nfunc HeaderExpired(h *types.SignedHeader, trustingPeriod time.Duration, now time.Time) bool {\n\texpirationTime := h.Time.Add(trustingPeriod)\n\treturn !expirationTime.After(now)\n}\n"})}),"\n",(0,t.jsxs)(n.p,{children:["In other words, a new header received at timestamp ",(0,t.jsx)(n.code,{children:"ts"})," is rejected if the following inequality holds for any trusted header ",(0,t.jsx)(n.code,{children:"h"}),":"]}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-golang",children:"// h is a header of the remote chain\n// h.T is a timestamp on the remote chain\n// ts is a timestamp on the host chain\nh.T + TrustingPeriod <= ts\n"})}),"\n",(0,t.jsxs)(n.p,{children:["The following figure describes the algorithm used by the host chain to reject headers outside of the ",(0,t.jsx)(n.code,{children:"TrustingPeriod"}),"."]}),"\n",(0,t.jsx)(n.p,{children:(0,t.jsx)(n.img,{alt:"IBC Client Updates",src:i(892).Z+"",width:"1510",height:"682"})}),"\n",(0,t.jsxs)(r,{children:[(0,t.jsxs)(n.p,{children:[(0,t.jsx)("summary",{children:"Intuition behind the trusting period."}),"\nThe trusting period is there to make sure that the validators that signed for the trusted header have their collateral still locked so that in case they misbehave (i.e., light client attack), this collateral can be slashed.\nNote that the validators that signed the trusted header are responsible for the untrusted header (for both Sequential Verification and Skipping Verification). For more details, see Figure 1 and 3 in the ",(0,t.jsx)(n.a,{href:"https://arxiv.org/pdf/2010.07031",children:"Tendermint Light Client paper"}),":"]}),(0,t.jsx)(n.p,{children:(0,t.jsx)(n.img,{alt:"Sequential Verification",src:i(3489).Z+"",width:"1474",height:"671"})}),(0,t.jsx)(n.p,{children:(0,t.jsx)(n.img,{alt:"Skipping Verification",src:i(3856).Z+"",width:"1582",height:"1028"})})]}),"\n"]}),"\n"]}),"\n",(0,t.jsx)(n.h3,{id:"updating-consumers-ibc-clients",children:"Updating Consumers' IBC Clients"}),"\n",(0,t.jsxs)(n.blockquote,{children:["\n",(0,t.jsx)(n.p,{children:"In the context of ICS, the provider is one of the host chains and the consumers are the remote chains. Note that other third-party chains could be host chains as well."}),"\n"]}),"\n",(0,t.jsx)(n.p,{children:"Consumer chains have their own consensus engine \u2014 validators that opt in need to run full nodes of the consumer chains, which consist of both consensus and application layer.\nThis means that consumers produce headers and a relayer could use those headers to update the consumer\u2019s IBC clients on other chains (the provider included).\nHowever, consumer chains don\u2019t have their own staking module."}),"\n",(0,t.jsxs)(n.p,{children:["In ICS, the provider is the \u201cstaking module\u201d of the consumer chains \u2014 validators lock collateral on the provider and as a result can produce blocks on consumer chains.\nThe consumer module on the consumer chains is just a representation of the provider\u2019s staking module, i.e., it provides an ",(0,t.jsx)(n.em,{children:"asynchronous"})," view of the voting powers and indirectly of the locked collateral.\nThe key word here is ",(0,t.jsx)(n.em,{children:"asynchronous"}),", which means that (in theory) there is no bound on the lag between the provider\u2019s view of stake and the consumer\u2019s view of stake.\nThe reasons for this asynchrony are relaying delays and chain liveness (e.g., a consumer could be down for a long period of time without affecting the liveness of the staking module on the provider)."]}),"\n",(0,t.jsx)(n.p,{children:"The following figure describes the problem of using the same condition (based on the trusting period), i.e.,"}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-golang",children:"// hc is a header of the consumer chain\n// hc.T is a timestamp on the consumer chain\n// ts is a timestamp on the host chain\nhc.T + TrustingPeriod <= ts\n"})}),"\n",(0,t.jsxs)(n.p,{children:["to reject consumer headers outside of the ",(0,t.jsx)(n.code,{children:"TrustingPeriod"}),".\nThe issue is that the time period ",(0,t.jsx)(n.code,{children:"hc.T"})," and ",(0,t.jsx)(n.code,{children:"T"})," (the time at which the validator set ",(0,t.jsx)(n.code,{children:"V"})," was locked on the provider) depends on the consumer chain, i.e., the consumer chain can choose an arbitrary time when to send ",(0,t.jsx)(n.code,{children:"V"})," to CometBFT.\nAs a result, even if ",(0,t.jsx)(n.code,{children:"hc.T + TrustingPeriod > ts"})," (i.e., the header is received within the trusting period), if ",(0,t.jsx)(n.code,{children:"hc.T - T"})," is large enough, then the stake of ",(0,t.jsx)(n.code,{children:"V"})," could be already unlocked on the provider."]}),"\n",(0,t.jsx)(n.p,{children:(0,t.jsx)(n.img,{alt:"ICS Client Updates",src:i(4390).Z+"",width:"1607",height:"1145"})}),"\n",(0,t.jsxs)(n.p,{children:["Note that before the ",(0,t.jsxs)(n.a,{href:"/interchain-security/adrs/adr-018-remove-vscmatured",children:["removal of ",(0,t.jsx)(n.code,{children:"VSCMaturedPackets"})]}),", the consumers had a ",(0,t.jsx)(n.em,{children:"partially synchronous"})," view of the provider\u2019s staking module.\nPartially synchronous means that the lag between the provider\u2019s view of stake and the consumer\u2019s view of stake is bounded, because consumers that exceeded this lag were forcibly removed from the protocol.\nThe issue was that whatever attack is possible with an asynchronous view of the staking module, it is eventually possible with the partially synchronous view as well.\nFor more details on this, please check out ",(0,t.jsx)(n.a,{href:"/interchain-security/adrs/adr-018-remove-vscmatured",children:"ADR 018"}),"."]}),"\n",(0,t.jsxs)(n.p,{children:["This ADR proposes a solution to this synchrony issue -- it uses ",(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc-go/issues/5112",children:"IBC conditional clients"})," to create a ",(0,t.jsx)(n.em,{children:"synchronous"})," view of the provider\u2019s staking module."]}),"\n",(0,t.jsx)(n.h2,{id:"decision",children:"Decision"}),"\n",(0,t.jsxs)(n.p,{children:["The idea is to extend the IBC light clients for ICS consumer chains to accept a new header received at timestamp ",(0,t.jsx)(n.code,{children:"ts"})," only if, given any trusted header ",(0,t.jsx)(n.code,{children:"h"}),", ",(0,t.jsx)(n.code,{children:"h.ProviderTime + TrustingPeriod > ts"}),", where ",(0,t.jsx)(n.code,{children:"h.ProviderTime"})," is the timestamp on the provider when ",(0,t.jsx)(n.code,{children:"h.Valset"})," locked its stake."]}),"\n",(0,t.jsx)(n.p,{children:"The implementation of this feature consists of three parts:"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsxs)(n.li,{children:["Store ",(0,t.jsx)(n.code,{children:"h.ProviderTime"})," (the timestamps when the consumer validator sets locked their stake) in the provider state.\nNote that this state can be pruned once the provider unbonding period elapses."]}),"\n",(0,t.jsxs)(n.li,{children:["Extend the IBC light client logic on the host chains to reject headers received at timestamp ",(0,t.jsx)(n.code,{children:"ts"})," if, given any trusted header ",(0,t.jsx)(n.code,{children:"h"}),",\n",(0,t.jsx)(n.code,{children:"h.ProviderTime + TrustingPeriod <= ts"}),".\nNote that this logic must existing both on the provider chain and on third party chains (including other consumer chains)."]}),"\n",(0,t.jsxs)(n.li,{children:["For cases when the host chain is different than the provider chain, enable relayers to work with ",(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc-go/issues/5112",children:"IBC conditional clients"}),"."]}),"\n"]}),"\n",(0,t.jsx)(n.p,{children:"The remainder of this section is addressing the first part and the second part for the case when the host chain is the provider chain.\nThe second part for the case when the host chain is different than the provider chain and the third part are outside the scope of this ADR."}),"\n",(0,t.jsx)(n.h3,{id:"store-provider-timestamps",children:"Store Provider Timestamps"}),"\n",(0,t.jsxs)(n.p,{children:["Currently, the provider module stores the validator set for every consumer chain.\nThis is done by calling ",(0,t.jsx)(n.code,{children:"SetConsumerValSet()"})," at the end of every epoch when queueing new ",(0,t.jsx)(n.code,{children:"VSCPackets"}),".\nThis is the timestamp when the validator set locked its stake (i.e., ",(0,t.jsx)(n.code,{children:"h.ProviderTime"}),").\nFor consumer chain clients, the provider needs to store these timestamps."]}),"\n",(0,t.jsx)(n.h4,{id:"state",children:"State"}),"\n",(0,t.jsxs)(n.p,{children:[(0,t.jsx)(n.code,{children:"ConsumerValidatorTimestampKey"})," - Stores the latest timestamp when the validator set ",(0,t.jsx)(n.code,{children:"V"})," of a consumer chain with ",(0,t.jsx)(n.code,{children:"consumerID"})," locked its stake on the provider chain."]}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-golang",children:"ConsumerValidatorTimestampBytePrefix | len(consumerID) | consumerID | valsetHash -> V.lockTs\n"})}),"\n",(0,t.jsxs)(n.p,{children:["where ",(0,t.jsx)(n.code,{children:"valsetHash"})," is the hash of ",(0,t.jsx)(n.code,{children:"V"}),". Note that this hash is the same as the one in the headers produced by the consumer chain validated by ",(0,t.jsx)(n.code,{children:"V"}),".\nAlso, note that ",(0,t.jsx)(n.code,{children:"V.lockTs"})," is the same as ",(0,t.jsx)(n.code,{children:"h.ProviderTime"})," above."]}),"\n",(0,t.jsxs)(n.p,{children:["The guarantee provided by the provider chain is that the stake of ",(0,t.jsx)(n.code,{children:"V"})," will be locked until ",(0,t.jsx)(n.code,{children:"V.lockTs + UnbondingPeriod"}),".\nThis is sufficient information for consumer chain clients to decide whether new headers are outside the trusting period.\nThis guarantee has two consequences.\nFirst, it is sufficient to store the latest timestamp: If a consumer chain has the same validator set ",(0,t.jsx)(n.code,{children:"V"})," over multiple epochs, the only relevant information is the timestamp until when ",(0,t.jsx)(n.code,{children:"V"}),"'s stake will be locked on the provider and this can be derived from ",(0,t.jsx)(n.code,{children:"V.lockTs"}),".\nSecond, this state can be pruned once the unbonding period elapses, i.e., once the provider block time exceeds ",(0,t.jsx)(n.code,{children:"V.lockTs + UnbondingPeriod"}),"."]}),"\n",(0,t.jsx)(n.h4,{id:"query",children:"Query"}),"\n",(0,t.jsx)(n.p,{children:"To query the timestamps when consumer validator sets are locked on the provider, the following query is introduced:"}),"\n",(0,t.jsx)(n.pre,{children:(0,t.jsx)(n.code,{className:"language-bash",children:"interchain-security-pd query provider valsetLockTs $consumerID $valsetHash\n"})}),"\n",(0,t.jsx)(n.h3,{id:"ics-conditional-clients-on-the-provider",children:"ICS Conditional Clients on the Provider"}),"\n",(0,t.jsxs)(n.p,{children:["If the host chain is different than the provider chain, then it needs to use ",(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc-go/issues/5112",children:"IBC conditional clients"})," to connect to consumer chains.\nThese conditional clients would need to query the provider chain before they can accept a new header from the consumer chains.\nIn practice, a relayer would send all the information needed (i.e., the new header and the timestamp when the provider locked the stake corresponding to the validator set that signed the trusted header) and the conditional client will verify this information using the existing light client of the provider chain.\nNote that this is also the case for consumer chains acting as host chain and connecting to other consumer chains."]}),"\n",(0,t.jsx)(n.p,{children:'This section focuses though on the case when the host chain is the provider chain.\nAs the additional information needed is already on the host chain, there is no need for a conditional client.\nInstead, the provider module needs to act as a "middleware" for all IBC ClientUpdate messages coming from consumer chains and reject headers that were signed by validators outside of the trusting period.'}),"\n",(0,t.jsx)(n.h2,{id:"consequences",children:"Consequences"}),"\n",(0,t.jsx)(n.h3,{id:"positive",children:"Positive"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsx)(n.li,{children:"Improve the security of IBC communication with consumer chains."}),"\n"]}),"\n",(0,t.jsx)(n.h3,{id:"negative",children:"Negative"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsx)(n.li,{children:"The liveness of consumer chains IBC channels depends on the liveness of the provider. Note though that as long as the provider client on the third-party chain is not expiring, the IBC channels of the consumer chains will remain live."}),"\n",(0,t.jsx)(n.li,{children:"For IBC to work, third-party chains need to have conditional clients of the consumer chains. This includes also other consumer chains."}),"\n",(0,t.jsx)(n.li,{children:"Additional state is needed on the provider chain to store previous consumer validator sets. This state can be pruned once the unbonding period elapses."}),"\n"]}),"\n",(0,t.jsx)(n.h3,{id:"neutral",children:"Neutral"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsx)(n.li,{children:"N/A"}),"\n"]}),"\n",(0,t.jsx)(n.h2,{id:"references",children:"References"}),"\n",(0,t.jsxs)(n.ul,{children:["\n",(0,t.jsx)(n.li,{children:(0,t.jsx)(n.a,{href:"/interchain-security/adrs/adr-018-remove-vscmatured",children:"ADR 018: Remove VSCMatured Packets"})}),"\n",(0,t.jsx)(n.li,{children:(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc-go/issues/5112",children:"IBC conditional clients"})}),"\n",(0,t.jsx)(n.li,{children:(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc-go/issues/5310",children:"Querier Approach for Conditional Clients"})}),"\n",(0,t.jsx)(n.li,{children:(0,t.jsx)(n.a,{href:"https://github.com/cosmos/ibc/pull/939",children:"Original conditional client idea in the IBC specs"})}),"\n"]})]})}function l(e={}){const{wrapper:n}={...(0,s.a)(),...e.components};return n?(0,t.jsx)(n,{...e,children:(0,t.jsx)(c,{...e})}):c(e)}},4390:(e,n,i)=>{i.d(n,{Z:()=>t});const t=i.p+"assets/images/adr-021-ics-trusting-period-a79587abda739a3d176b8d69c6587c79.png"},3489:(e,n,i)=>{i.d(n,{Z:()=>t});const t=i.p+"assets/images/adr-021-sequential-verification-ce70fa77ef43693e1dd13e3c1eb273f7.png"},3856:(e,n,i)=>{i.d(n,{Z:()=>t});const t=i.p+"assets/images/adr-021-skipping-verification-b4a72168bcfd75c52cdd0993e1d71da8.png"},892:(e,n,i)=>{i.d(n,{Z:()=>t});const t=i.p+"assets/images/adr-021-trusting-period-1951ffe0f757a6804923887b56a7a965.png"},1151:(e,n,i)=>{i.d(n,{Z:()=>h,a:()=>o});var t=i(7294);const s={},r=t.createContext(s);function o(e){const n=t.useContext(r);return t.useMemo((function(){return"function"==typeof e?e(n):{...n,...e}}),[n,e])}function h(e){let n;return n=e.disableParentContext?"function"==typeof e.components?e.components(s):e.components||s:o(e.components),t.createElement(r.Provider,{value:n},e.children)}}}]);