## Introduction

This document highlights the tension between Cardano's opcert issue numbers and the Linear Leios specification's rules about detecting RB header equivocation and avoiding excessive EB diffusion.
It identifies a few possibilities, none of which are fully appealing.

## Relevant Summary of Linear Leios

A pillar of the Linear Leios design requires equivocation detection: a Praos election grants the right to incur enough network traffic for every node to promptly receive one EB _but not a second EB_.

A non-obvious implication is that an EB should not be certified if a corresponding proof of equivocation exists soon enough before the certification.
Without that constraint, it's possible that only exactly Quorum of all parties have already received the certified EB; the rest of the parties would need to receive that certified EB as a second received EB, since they already received one of its equivocating alternative EBs.
That would violate the pillar.
Moreover, it would also delay the adoption of the honest RB that includes the certificate, since some nodes would have to acquire the certified EB before they can validate the RB.

Thus the network must actively detect equivocation and fully diffuse proofs of it, as promptly as possible.
A new dedicated mini protocol RbHeaderRelay is introduced, since ChainSync and BlockFetch were designed for a different and incompatible purpose: diffusing _only the single best chain_ (such that any tiebreakers do not distinguish equivocating blocks)—and that separate purpose is still fitting for the RB chains within Linear Leios.

## RbHeaderRelay, Ignoring the Tension

The immutable ledger state in Cardano provides enough information to exactly determine whether a contemporary header H should be diffused via RbHeaderRelay, with one exception.
The predicates are as follows.

- The collective values found in H's fields were signed by a hot key X.
- X was signed by the cold key of the party P that H claims to be issued by.
- The honest chain elects P in the slot claimed by H—recall that the Cardano design ensures each epoch's leader schedule is fixed so much earlier than the epoch begins that all relevant chains will agree on the leader schedule.

The aforementioned exception is that only (the protocol portion of) the exact ledger state identified by H's prevhash field can determine whether party P has signed a different, [higher precedence](https://github.com/IntersectMBO/ouroboros-consensus/pull/1610) hot key than X (TODO update link once that PR merges).
If this exception is ignored, then an adversary that has acquired a party's hot key will be able to satisfy RbHeaderRelay's definition of equivocation for the victim's elections even after the victim has issued a higher precedence hot key (presumably after mitigating their nodes' exploited vulnerability).
The adversary would only lose this capability to disrupt the victim's EB rights once the KES period of the leaked key expired—up to 90 days later, on Cardano.

## The Tension

**Perhaps that caveat is acceptable as-is, in which case RbHeaderRelay can be as simple as the other Relay mini protocols**, since, in the absence of hot key precedence, nothing about RbHeaderRelay is concerned with the position of the headers within chains.
On the other hand, if RbHeaderRelay must incorporate hot key precedence, then it will need to be more sophisticated.
There are two primary challenges.

- The current highest hot key precedence for some party is shared state among the network, so it's only necessarily agreed upon if it's stable.
However, the hot key precedence mechanism is designed to take effect as soon as possible, even before it's necessarily stable, in order to bound the intersection of the honest chain and any adversarial block that abuses the victim's compromised hot key orders of magnitude sooner than the KES period inherently does.
- If each precedence number is considered a distinct party, then the adversary can trivially generate infinite parties, since the Relay mini protocol schema ignores the chain structure_ and so cannot inherit the protocol rules' rate limit on precedence increments.
Infinite parties would incur intolerable network traffic.

Some points in the space of compromises seem worth mentioning.

- If the protocol rules allowed at most N increments per stability window, then that's at most N EBs of network traffic per Praos election.
  But if a victim actually genuinely needs to increment N+1 times within a single stability window, then the hot key precedence mechanism is arguably defeated.
- Perhaps RbHeaderRelay limits increments per stability window, but the Praos protocol rules do not.
  So EBs would only be disrupted if there were more than N increments since the immutable ledger state.
  EG suppose N=2.
