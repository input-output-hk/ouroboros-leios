---
title: Earth phase, 6x mainnet throughput without even trying
description: Forty-one days of MusashiNet's Earth phase — what the first public Leios testnet phase proved, what broke, how it was fixed in the open, and what comes next in Water.
slug: musashinet-earth-phase
authors: [carlos]
tags: [testnet, musashinet, leios, throughput]
---

## TLDR

Earth, the first phase of MusashiNet, the Leios public testnet, asked whether the prototype holds in the wild. Forty-one days later, the answer is yes.

- **Six times mainnet's ceiling.** MusashiNet peaked at 26.8 TxkB/s with Leios active, against the 4.51 TxkB/s Cardano mainnet can reach with Praos alone. That's 6x mainnet's current maximum throughput.
- **The whole protocol ran end to end, in public.** More than 127,000 blocks, 30,000 endorser blocks announced, nearly 8,000 certificates on chain, 63 pools registered, and 10 releases in 6 weeks.
- **Five incidents, zero design failures.** A memory leak, two forks, frozen syncs, a one-byte serialization disagreement and a network-wide halt, all related to bugs, found and fixed in the open. The design proved to be correct.
- **The red team is already inside.** Piranha attacks the network with our published threat model in hand; so far Leios degrades in proportion to attacker stake, and the safety of the Praos layer remains untouched.
- **Water phase just started.** A fresh chain for parameter exploration, a redesigned mempool and real BLS keys, with the rewards program live, including retroactive rewards for pools that forged and voted in Earth.

[Last time](/blog/why-leios), we talked about why Cardano needs Leios and introduced MusashiNet, the Dojo where the protocol trains: five phases from Musashi's *Book of Five Rings* (Earth, Water, Fire, Wind, Void) and two swords, the short sword of Praos blocks and the long sword of endorser blocks. Earth, the first phase, has now closed. This is its story.

## What Earth gave us

The Earth phase asked one question: **does the prototype hold in the wild, at real latencies, on machines we neither control nor can see?** Holding meant running the whole protocol end-to-end: Praos blocks produced, endorser blocks announced, the stake voting on them, certificates landing on chain. The numbers that follow are that checklist, ticked.

Forty-one days. More than 127,000 blocks, 30,000 endorser blocks announced, nearly 8,000 certificates carried on chain. Sixty-three pools registered over the phase, up from the three we started with, forty producing blocks in a single epoch at the peak. Twelve releases in eight weeks, an unbroken weekly cadence that absorbed two same-week hotfixes without missing the next release.

A young testnet has no traffic of its own, so we brought our own. The **centrifuge**, our synthetic load generator, was tuned to push slightly more transactions than Praos could clear on its own, and the protocol's settings stayed at cautious first values. It ran one hour on, one hour off. Twelve hours a day, every day, the network lived in the conditions Leios was built for.

That was enough for a first test of the design at a global scale. MusashiNet peaked at 26.8 TxkB/s with Leios active, against the 4.51 TxkB/s Cardano mainnet can reach with Praos alone at today's parameters. Six times today's ceiling, with the dials barely turned. In the final days of the phase, when things were more stable, Leios was carrying 54% of everything that reached the chain.

Compared with the traffic the mainnet actually carried over the same period, the Earth phase moved 18x the transaction count and 3.3x the bytes.

<!-- truncate -->

## From paper to prototype

Leios started as a research paper: [High-Throughput Blockchain Consensus under Realistic Network Assumptions](https://eprint.iacr.org/2025/1115.pdf), presented at Crypto 2025\. A paper is not a specification, so the engineering team turned it into [CIP-164](https://github.com/cardano-foundation/CIPs/tree/master/CIP-0164), Linear Leios, a variant that could be built in reasonable time with the least disruption to the protocol Cardano already runs. The proposal evolved for months in the open, shaped by community discussion and backed by simulations, before it merged on January 6, 2026\.

A working prototype followed in under six months. **Sebastian Nagel**, the Leios architect, is leading the team that carried it across: a pragmatic, experienced engineer who knows Cardano inside out and is a productivity machine.

The goal is openly ambitious: Leios mainnet-ready by the end of the year. Consensus upgrades are usually measured in years. Going from specification to mainnet in a single year would make this among the fastest the industry has seen, and we are chasing it in the open, release by release.

## Five throws in the Dojo

![](../static/img/blog/musahi-earth.jpg)


As expected, not everything was smooth. We found bugs, forked the chain twice, and had a morning when every machine on the network stopped. None of it was a protocol failure. Every one of those was a bug in our code.

We fixed every one of them, learned from them, and moved on. Five of them are worth telling, in the order they found us.

### Leaks, crashes, and forks made for an interesting week

On the Thursday of launch week, **John Lotoski**, our system reliability node team lead, spotted the node leaking memory. Consistent across all three of our block producers.

Containment first: a daily restart on every machine; then a profiled build on one relay to catch it in the act.

In the community channel, people were noticing it too:

:::note[Kiwipool | June 29]
"_Noticed after 2 -3 days soak running the nodes RAM is up around 4.5GB <br/>
What sort of RAM usage y'all seeing?_"
:::

It was our leak, being measured from the outside. To make it more interesting, that weekend, under the centrifuge's load, the chain forked. Twice!

The forks were the easy part. The crashes were the killer: any node that met a certified block without having the endorser data died on the spot, and reviving it meant a human walking a database directory over to it. So John spliced the chain back together by hand, twice, and ran the experiment. Load off: healed within hours. Load on: collapse, on schedule.

Why the chain broke under load was still an open question. We had a suspect: in the lab, on a three-node devnet, block production had slowed as the mempool filled. That needed further investigation.

The next morning John cornered the leak. Under load, the node opened a fresh connection to its Leios database over and over and never let one go, each holding its file handle and two megabytes of cache: 173 handles an hour, a relay's entire memory in about a day. The fix taught the node to close what it opens. The crash fix changed the block header format, so, days later, we retired that first chain, and its successor kept its genesis block until the very end of the phase.

That is week one in the Dojo. You get thrown, you learn the fall, you get up.

### BROKEN, DO NOT USE

The next throw came in week two, with the release that enabled real Leios certificates: transactions were now endorsed in a block only once 75% of the stake had voted for them.

The next afternoon, the chain announced its first endorser block. The long sword's first swing.

Three operators posted the same number: fresh syncs were freezing at block 28,358. Then the nodes started segfaulting.

Two failures, with terrible timing. Sebastian was due on a fourteen-hour flight to Tokyo to talk Leios with Japanese stake pool operators (SPOs) and delegated representatives (DReps) at WebX. He threw in some ideas, handed over the incident, and went to the airport.

Luckily, we have a badass team!

**Dražen Popović**, one of our consensus engineers, a Haskell wizard with a strong cybersecurity background, turned the incident thread into a control tower: numbered updates, on the hour, each saying what was found, what was fixed, what was still broken, and what came next. Within two hours he had a hypothesis for the segfault cascade, a fix branch built, and a patched node rolling out.

Then came UPDATE 3:

:::note[Dražen Popović | UPDATE 3]
Bad news <br/>
The patch killed the segfaults, but fresh syncs are still freezing at block 28,358. 
:::

John put the patched node under full centrifuge load for 90 minutes, with zero segfaults, and that fix shipped while Sebastian was still in the air. The freeze fought on.

The frozen syncs took more forensics. **Nick Frisby**, a consensus engineer from **Tweag by Modus Create**, and one of the most knowledgeable people about Cardano internals, opened an investigation. 

Forty minutes in, Nick had that first bug: block 28,358 had announced the chain's first endorser block, block 28,359 carried its certificate, and a syncing node would download every block that followed yet could select none of them, because one check deep in the code reported ‘no certificate here’ no matter what the block said. The chain's first swing of the long sword had locked the front door behind it.

Soon he found a second bug, a cleanup routine deleting endorser blocks that arrived before their announcing block. By late afternoon he had a third, more fundamental than either: the node would sometimes throw a request away instead of sending it, then count it as sent anyway, until it believed it was too busy to ask for anything more. All three fixes were pushed, with his own build syncing the whole testnet end-to-end to be sure. Three bugs, one working day.

Sebastian landed to find the segfaults solved and shipped, and the stall understood and fixed in a branch.

The big [warning sign](https://github.com/input-output-hk/ouroboros-leios/releases/tag/prototype-2026w27) is still there: ‘Prototype 2026w27 – BROKEN, DO NOT USE.’

### It's the mempool, stupid

The suspect from the lab and from week one had still never been caught in the act. It required long periods of sustained full load to manifest, and the chain was finally steady enough to bear it again.

Sebastian posted the invitation in the community channel: stability issues resolved, come load the network yourselves. And he shipped the tool to do it: **tx-firehose**, a generator he wrote over a weekend, as powerful as our centrifuge and easier to use.

The community showed up. Kiwipool aimed theirs from New Zealand, ten transactions a second, then thirty, until their wallet ran dry. **Leon** of **HAPPY** burned a thousand test ada in a few runs. Of course, it is called a firehose for a reason\! We refilled their wallets so they could keep testing.

It worked. For the first time on MusashiNet, the mempool stayed full for ten hours straight, topped up by transactions arriving faster than Praos could clear them, half the traffic ours and half the community's.

And the problem showed. Blocks began running late. On mainnet, with a more complex topology, virtually every block reaches every node within a second of being forged. On MusashiNet that day, more than 40% of blocks took longer, and 10% were still in transit after three seconds.

Memory was the first suspect, but the garbage-collection numbers stayed flat all day. The network was next, but diffusion seemed to be working correctly, and one late block settled it: it left its origin relay 3.467 seconds late, then reached every route within tenths of a second of the first arrival. Born late, then relayed fast. The delay was at the block production stage, not in transit.

Final suspect: the forge loop. It opens by asking the mempool for a snapshot of the waiting transactions, and under full load, an operation that normally returns in milliseconds took seconds.

We had the smoking gun. It was the mempool\! Designed for Praos, it revalidates all transactions every time a node adopts a block, while holding a lock the forge loop needs. The fuller the mempool, the longer every producer waits for its own block to be forged. In the extreme, they waited past their own leadership slots.

Scaling up our own machines improved forging to a third of a second on the heaviest day of load. But that is not the right solution: every gigabyte we ask for comes out of operators' pockets, so the fix belongs in code, not hardware. The team has redesigned the mempool to revalidate off-chain, so forging never queues behind bookkeeping, and the Water phase is where it will get tested.

### The day we forked it up\!

Early one morning in week four, the network split at block 67,554, producers rejecting everything the relays offered. **VOLCY** posted their logs: the next block was failing validation on a size mismatch, 66,006 bytes against a declared 66,007.

The fork was caused by that one byte.

A block producer running another node implementation had forged a perfectly valid block. Haskell nodes accepted it, decoded it, and wrote it back to disk one byte shorter, a slightly different binary convention. Same transactions, same meaning, different bytes, wrong hash.

The other implementation did nothing wrong. The Haskell node changed the bytes. We have had a rule against this for almost a decade: **never re-serialize another node's data**, because with more than one implementation on a network, there is no such thing as an innocent re-encoding. We broke our own rule, moving fast in a young era's codec, and the network penalized us immediately.

Nick Frisby came back the same day with a fix: he stopped the node from altering block bytes on their way to disk and had it quietly repair the mangled ones still arriving, deliberately temporary while the real serialization fix was built where it belonged, upstream in the ledger. Chain density climbed back out of the hole.

Independent node implementations agreeing byte-for-byte on every block is the ultimate correctness test. The one time agreement broke, it broke by a single byte. A reminder to keep the [cardano-blueprint](https://github.com/cardano-scaling/cardano-blueprint) project up to date, and evidence that conformance tests will be more important as we approach the Leios release to mainnet.

### The morning every machine stopped

Week six opened with a big change for SPOs: real BLS keys. Until then, the keys that let a pool vote in Leios had been derived automatically, training wheels everyone knew were temporary. **Thomas Vellekoop**, one of our cryptographic engineers, had finalized the BLS implementation and had it independently audited months before. Now thw BLS registration was completely integrated in node, ledger, api, and cli. Operators started submitting key registrations on chain, and voting was moving onto the machinery mainnet will use.

Then, one morning at 10:42 UTC, every machine on the network stopped.

Not slowed. Stopped. An external experimental node had forged a block carrying a Leios certificate with an invalid signature. Input like that deserves the adversarial treatment: reject the block, disconnect the peer, carry on. Our code treated the invalid certificate as a fatal error instead, and every node that saw the block died on it; any node that restarted met the same block and died again. John's status report was six words long: ‘All machines affected, all machines stopped.’

One malformed signature shut the network down.

Fifty minutes after the halt, a patched node was built and deployed across our infrastructure for testing. We posted the public notice within two hours of the first crash, with working guidance for operators. The permanent fix merged the next day, and it is as much a one-line philosophy as a patch: a bad block from the outside world becomes a logged rejection, never a dead process. A network node's job is to survive what strangers send it.

The hotfix release went out the morning after, and Sebastian battle-tested it on his own block producer before recommending it to anyone else.

As the machines came back to life, the community continued registering keys. **PET** registered a BLS key on the day of the outage itself, **BIKES** was forging on the patched release within hours, and **Chris Gianelloni**, CEO of Blink Labs, the team behind Dingo, spent the afternoon shipping ARM64 Docker images, magnificently unbothered.

The halt lasted less than an hour on our infrastructure. The signature scheme did exactly what it was designed to do. It caught a bad signature. We just overreacted.

## The red team is already inside

One node on MusashiNet exists purely to hurt us. **Piranha** is the red team's node, written in Rust, and it connects like any other peer with a single purpose: break the protocol or die trying. Its attacks come straight from our [published threat model](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/threat-model.md): T20, withholding an endorser block it had already announced; T27, partitioning the network to split mempools; T10, sitting on the committee and declining to vote.

The verdict so far, from **Chris Tilt**, our red team lead:

> Some attacks were possible, but so far we've found the Leios protocol to be robust against attack, with degradation proportional to stake. So far, there have been no discoveries that compromise the underlying safety of the Praos layer.

The heaviest of it is still ahead, in Fire and in Wind.

## Water: same design, many configurations

Earth asked whether the prototype survives contact with reality. It does.

It is still a prototype: the mempool replacement is in review, bottlenecks remain, the pipeline is still being completed. But all of it was found and fixed in the open. **The design never failed.** And the questions that research and simulation could not answer are being answered in the only place they can be: on real machines, across real distances, by real operators.

Water opens now on a fresh chain, and Water takes the shape of whatever contains it: parameter exploration, alternative component implementations starting with that mempool, and real BLS keys as the way into the voting committee. The hunt for Leios's actual limits begins here.

The rewards program is live with it. We reward operators who run MusashiNet nodes and share the data their machines see, because the sharpest questions left can only be answered from hardware we do not own, in places we did not choose. Pools that forged blocks during the Earth phase are eligible for a retroactive reward, judged from a snapshot taken before the reset. The [rewards program page](https://leios.cardano-scaling.org/docs/testnet/rewards-program/) explains the steps.

Cardano took the trilemma in the right order: security first, decentralization second, scale last. Leios is the scale leg, and it is training in public now. If your project needs security you can reason about and an ecosystem that builds in the open, come build on Cardano.

The Dojo is open. Come train with us.  