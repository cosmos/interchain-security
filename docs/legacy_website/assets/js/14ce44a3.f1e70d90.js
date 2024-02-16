"use strict";(self.webpackChunkwebsite=self.webpackChunkwebsite||[]).push([[9759],{3905:(e,n,t)=>{t.d(n,{Zo:()=>p,kt:()=>v});var i=t(7294);function o(e,n,t){return n in e?Object.defineProperty(e,n,{value:t,enumerable:!0,configurable:!0,writable:!0}):e[n]=t,e}function a(e,n){var t=Object.keys(e);if(Object.getOwnPropertySymbols){var i=Object.getOwnPropertySymbols(e);n&&(i=i.filter((function(n){return Object.getOwnPropertyDescriptor(e,n).enumerable}))),t.push.apply(t,i)}return t}function r(e){for(var n=1;n<arguments.length;n++){var t=null!=arguments[n]?arguments[n]:{};n%2?a(Object(t),!0).forEach((function(n){o(e,n,t[n])})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(t)):a(Object(t)).forEach((function(n){Object.defineProperty(e,n,Object.getOwnPropertyDescriptor(t,n))}))}return e}function s(e,n){if(null==e)return{};var t,i,o=function(e,n){if(null==e)return{};var t,i,o={},a=Object.keys(e);for(i=0;i<a.length;i++)t=a[i],n.indexOf(t)>=0||(o[t]=e[t]);return o}(e,n);if(Object.getOwnPropertySymbols){var a=Object.getOwnPropertySymbols(e);for(i=0;i<a.length;i++)t=a[i],n.indexOf(t)>=0||Object.prototype.propertyIsEnumerable.call(e,t)&&(o[t]=e[t])}return o}var l=i.createContext({}),u=function(e){var n=i.useContext(l),t=n;return e&&(t="function"==typeof e?e(n):r(r({},n),e)),t},p=function(e){var n=u(e.components);return i.createElement(l.Provider,{value:n},e.children)},d="mdxType",c={inlineCode:"code",wrapper:function(e){var n=e.children;return i.createElement(i.Fragment,{},n)}},h=i.forwardRef((function(e,n){var t=e.components,o=e.mdxType,a=e.originalType,l=e.parentName,p=s(e,["components","mdxType","originalType","parentName"]),d=u(t),h=o,v=d["".concat(l,".").concat(h)]||d[h]||c[h]||a;return t?i.createElement(v,r(r({ref:n},p),{},{components:t})):i.createElement(v,r({ref:n},p))}));function v(e,n){var t=arguments,o=n&&n.mdxType;if("string"==typeof e||o){var a=t.length,r=new Array(a);r[0]=h;var s={};for(var l in n)hasOwnProperty.call(n,l)&&(s[l]=n[l]);s.originalType=e,s[d]="string"==typeof e?e:o,r[1]=s;for(var u=2;u<a;u++)r[u]=t[u];return i.createElement.apply(null,r)}return i.createElement.apply(null,t)}h.displayName="MDXCreateElement"},7119:(e,n,t)=>{t.r(n),t.d(n,{assets:()=>l,contentTitle:()=>r,default:()=>c,frontMatter:()=>a,metadata:()=>s,toc:()=>u});var i=t(7462),o=(t(7294),t(3905));const a={sidebar_position:2,title:"ADR Template"},r="ADR 007: Pause validator unbonding during equivocation proposal",s={unversionedId:"adrs/adr-007-pause-unbonding-on-eqv-prop",id:"version-v3.1.0/adrs/adr-007-pause-unbonding-on-eqv-prop",title:"ADR Template",description:"Changelog",source:"@site/versioned_docs/version-v3.1.0/adrs/adr-007-pause-unbonding-on-eqv-prop.md",sourceDirName:"adrs",slug:"/adrs/adr-007-pause-unbonding-on-eqv-prop",permalink:"/interchain-security/legacy/v3.1.0/adrs/adr-007-pause-unbonding-on-eqv-prop",draft:!1,tags:[],version:"v3.1.0",sidebarPosition:2,frontMatter:{sidebar_position:2,title:"ADR Template"},sidebar:"tutorialSidebar",previous:{title:"ADRs",permalink:"/interchain-security/legacy/v3.1.0/adrs/intro"},next:{title:"ADR Template",permalink:"/interchain-security/legacy/v3.1.0/adrs/adr-template"}},l={},u=[{value:"Changelog",id:"changelog",level:2},{value:"Status",id:"status",level:2},{value:"Context",id:"context",level:2},{value:"Decision",id:"decision",level:2},{value:"How",id:"how",level:3},{value:"When pause",id:"when-pause",level:3},{value:"When unpause",id:"when-unpause",level:3},{value:"Consequences",id:"consequences",level:2},{value:"Positive",id:"positive",level:3},{value:"Negative",id:"negative",level:3},{value:"Neutral",id:"neutral",level:3},{value:"References",id:"references",level:2}],p={toc:u},d="wrapper";function c(e){let{components:n,...t}=e;return(0,o.kt)(d,(0,i.Z)({},p,t,{components:n,mdxType:"MDXLayout"}),(0,o.kt)("h1",{id:"adr-007-pause-validator-unbonding-during-equivocation-proposal"},"ADR 007: Pause validator unbonding during equivocation proposal"),(0,o.kt)("h2",{id:"changelog"},"Changelog"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},"2023-05-16: Initial Draft")),(0,o.kt)("h2",{id:"status"},"Status"),(0,o.kt)("p",null,"Proposed"),(0,o.kt)("h2",{id:"context"},"Context"),(0,o.kt)("p",null,"Currently, if an equivocation slashing proposal is created after more than one\nweek has passed since the equivocation, it is possible that the validator in\nquestion could unbond and get away without being slashed, since the unbonding\nperiod is 3 weeks, and the voting period is 2 weeks. For this reason, it might\nbe good to pause unbondings for validators named in an equivocation slashing\nproposal until the proposal's voting period is over."),(0,o.kt)("h2",{id:"decision"},"Decision"),(0,o.kt)("h3",{id:"how"},"How"),(0,o.kt)("p",null,"Pausing the unbonding period is already possible thanks to the changes in the\n",(0,o.kt)("inlineCode",{parentName:"p"},"staking")," module of the cosmos-sdk:"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"stakingKeeper.PutUnbondingOnHold")," pauses an unbonding period"),(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("inlineCode",{parentName:"li"},"stakingKeeper.UnbondingCanComplete")," unpauses an unbonding period")),(0,o.kt)("p",null,"These methods use a reference counter under the hood, that gets incremented\nevery time ",(0,o.kt)("inlineCode",{parentName:"p"},"PutUnbondingOnHold")," is called, and decreased when\n",(0,o.kt)("inlineCode",{parentName:"p"},"UnbondingCanComplete")," is called instead. A specific unbonding is considered\nfully unpaused when its underlying reference counter reaches 0. Therefore, as\nlong as we safeguard consistency - i.e. we make sure we eventually decrement\nthe reference counter for each time we have incremented it - we can safely use\nthis existing mechanism without conflicts with the ",(0,o.kt)("em",{parentName:"p"},"Completion of Unbonding\nOperations")," system."),(0,o.kt)("h3",{id:"when-pause"},"When pause"),(0,o.kt)("p",null,"The unbonding period (if there is any unbonding) should be paused once an\nequivocation proposal enters the voting period. For that, the ",(0,o.kt)("inlineCode",{parentName:"p"},"gov")," module's\nhook ",(0,o.kt)("inlineCode",{parentName:"p"},"AfterProposalDeposit")," can be used. "),(0,o.kt)("p",null,"If the hook is triggered with a an equivocation proposal in voting period, then\nfor each equivocation of the proposal, the unbonding operations of the related\nvalidator that were initiated after the equivocation block time must be paused"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},"i.e. the underlying reference counter has to be increased.")),(0,o.kt)("p",null,"Note that even after the voting period has started, a proposal can receive\nadditional deposits. The hook is triggered however at arrival of a deposit, so\na check to verify that the proposal is not already in voting period is\nrequired."),(0,o.kt)("h3",{id:"when-unpause"},"When unpause"),(0,o.kt)("p",null,"We can use a ",(0,o.kt)("inlineCode",{parentName:"p"},"gov")," module's hook also here and it is\n",(0,o.kt)("inlineCode",{parentName:"p"},"AfterProposalVotingPeriodEnded"),"."),(0,o.kt)("p",null,"If the hook is triggered with an equivocation proposal, then for each\nassociated equivocation, the unbonding operations of the related validator that\nwere initiated between the equivocation block time and the start of the\nproposal voting period must be unpaused - i.e. decrease the underlying\nreference counter - regardless of the proposal outcome."),(0,o.kt)("h2",{id:"consequences"},"Consequences"),(0,o.kt)("h3",{id:"positive"},"Positive"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},"Validators subject to an equivocation proposal cannot finish unbonding\ntheir tokens before the end of the voting period.")),(0,o.kt)("h3",{id:"negative"},"Negative"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},"A malicious consumer chain could forge slash packets enabling submission of\nan equivocation proposal on the provider chain, resulting in the freezing of\nvalidator's unbondings for an undeterminated amount of time."),(0,o.kt)("li",{parentName:"ul"},"Misbehavior on a consumer chain can potentially go unpunished, if no one\nsubmits an equivocation proposal in time, or if the proposal doesn't pass.")),(0,o.kt)("h3",{id:"neutral"},"Neutral"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},"This feature can't be used for social slashing, because an equivocation\nproposal is only accepted if there's a slash log for the related\nvalidator(s), meaning the consumer chain has reported the equivocation to\nthe provider chain.")),(0,o.kt)("h2",{id:"references"},"References"),(0,o.kt)("ul",null,(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("a",{parentName:"li",href:"https://github.com/cosmos/interchain-security/issues/747"},"https://github.com/cosmos/interchain-security/issues/747")),(0,o.kt)("li",{parentName:"ul"},(0,o.kt)("a",{parentName:"li",href:"https://github.com/cosmos/interchain-security/pull/791"},"https://github.com/cosmos/interchain-security/pull/791"))))}c.isMDXComponent=!0}}]);