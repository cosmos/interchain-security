---
sidebar_position: 1
title: ADRs
---

# Architecture Decision Records (ADR)

This is a location to record all high-level architecture decisions in the Interchain Security project.

You can read more about the ADR concept in this [blog post](https://product.reverb.com/documenting-architecture-decisions-the-reverb-way-a3563bb24bd0#.78xhdix6t).

An ADR should provide:

- Context on the relevant goals and the current state
- Proposed changes to achieve the goals
- Summary of pros and cons
- References
- Changelog

Note the distinction between an ADR and a spec. The ADR provides the context, intuition, reasoning, and
justification for a change in architecture, or for the architecture of something
new. The spec is much more compressed and streamlined summary of everything as
it is or should be.

If recorded decisions turned out to be lacking, convene a discussion, record the new decisions here, and then modify the code to match.

Note the context/background should be written in the present tense.

To suggest an ADR, please make use of the [ADR template](./adr-template.md) provided.

## Table of Contents

### Accepted

- [ADR 001: Key Assignment](./adr-001-key-assignment.md)
- [ADR 002: Jail Throttling](./adr-002-throttle.md)
- [ADR 004: Denom DOS fixes](./adr-004-denom-dos-fixes.md)
- [ADR 005: Cryptographic verification of equivocation evidence](./adr-005-cryptographic-equivocation-verification.md)
- [ADR 008: Throttle with retries](./adr-008-throttle-retries.md)
- [ADR 009: Soft Opt-Out](./adr-009-soft-opt-out.md)
- [ADR 010: Standalone to Consumer Changeover](./adr-010-standalone-changeover.md)
- [ADR 013: Slashing on the provider for consumer equivocation](./adr-013-equivocation-slashing.md)

### Proposed

- [ADR 011: Improving testing and increasing confidence](./adr-011-improving-test-confidence.md)

### Rejected

- [ADR 007: Pause validator unbonding during equivocation proposal](./adr-007-pause-unbonding-on-eqv-prop.md)
- [ADR 012: Separate Releasing](./adr-012-separate-releasing.md)

### Deprecated

- [ADR 003: Equivocation governance proposal](./adr-003-equivocation-gov-proposal.md)
