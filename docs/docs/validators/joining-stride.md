---
sidebar_position: 6
---

https://app.excalidraw.com/l/9UFOCMAZLAI/5EVLj0WJcwt

https://github.com/Stride-Labs/mainnet/tree/main/ics-instructions

# Joining Stride

Stride is the first consumer chain to perform the standalone to consumer changeover procedure and transition from a standalone validator set to using `cosmoshub-4` validator set.

`stride-1` network (mainnet) will perform a software upgrade and at height `4616678` that will transition the network to using the Cosmos Hub's (`cosmoshub-4`) validator set.

 You can find instructions about the Stride consumer chain launch and joining the mainnet [here](https://github.com/Stride-Labs/mainnet/tree/main/ics-instructions).

 This [Excalidraw graphic](https://app.excalidraw.com/l/9UFOCMAZLAI/5EVLj0WJcwt) explains the timeline of Stride's changeover procedure.

## Note
Stride re-uses an existing `transfer` channel to send consumer rewards to the provider chain, in order to preserve existing transfer IBC denom between `stride-1` and `cosmoshub-4`.

## Resources
* [docs](https://docs.stride.zone/docs)
* [changeover procedure timeline](https://app.excalidraw.com/l/9UFOCMAZLAI/5EVLj0WJcwt)
