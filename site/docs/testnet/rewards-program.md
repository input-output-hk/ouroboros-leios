---
sidebar_position: 3
sidebar_label: SPO Rewards Program
title: Musashi Testnet Rewards Program
slug: /testnet/rewards-program
description: What the Musashi Testnet Rewards Program rewards stake pool operators for, how to apply, and the criteria a pool has to meet to be paid.
keywords:
  - leios
  - musashinet
  - testnet
  - stake pool
  - incentives
  - rewards program
  - eligibility
  - rewards
---

# Musashi Testnet Rewards Program

**Last updated: 10 August 2026.** We may update this page, and every update is published here.

:::tip Apply to the Rewards Program

Applications go through the
**[application form](https://forms.gle/Y2VVFSZdykmMjFTs9)**. If you are new to MusashiNet, start with
[how to apply, step by step](#how-to-apply-step-by-step).

:::

## The goal of the Rewards Program

The Rewards Program rewards two things: running a real stake pool on MusashiNet, and sharing the
operational data that running it produces. MusashiNet is only a useful testnet when real operators
run real infrastructure on it, and what their nodes record is what validates Leios before it reaches
mainnet.

Leios moves in windows. An endorser block has to reach voters in time for them to vote on it, and
those votes have to return in time to be certified, so most of what is worth knowing about a Leios
network is a question about when something arrived. The chain does not answer that directly. It
records the ranking blocks that were adopted, the endorser blocks that reached certification, and the
votes that made it into a certificate, which is the outcome of all that timing rather than the timing
itself.

The timing lives in the nodes. Yours knows when it saw an endorser block announcement, when it
issued its vote, and what it forged and when. Every node holds one fragment of the picture, and
sharing that fragment is what the Rewards Program rewards.

Three views make up that picture:

1. **Our probe.** We run `cardano-ping` against your registered relays a few times a day. Are they
   up and running, are they serving peers, are they in sync?
2. **Your node's logs.** What it forged, what it endorsed, and when, in its own clock.
3. **Every other pool's logs.** When that same block, vote or certificate reached them.

Together they reconstruct the journey of every block and vote, including the ones the chain never
recorded, and show where the time went: distance, load, peer topology, or the node itself.

## How to apply, step by step

1. **Install and run a node.** See [install and run a node](./getting-started.md).
2. **Generate your keys and read off your pool id.** The first half of
   [register a stake pool](./register-stake-pool.md) covers this. Your pool id comes from your cold
   key, so you have it before anything reaches the chain:

   ```shell
   cardano-cli dijkstra stake-pool id --output-bech32 --cold-verification-key-file cold.vkey
   ```

   **Already running a pool on MusashiNet? Reuse the same keys.** Apply with the pool id you already
   have. This will allow you to claim rewards for the Earth phase that just concluded. 

3. **Apply** on the [application form](https://forms.gle/Y2VVFSZdykmMjFTs9), with that pool id and
   the Cardano mainnet address you want rewards paid to. Once you submit it, we email you your
   **Application Code**, together with the exact metadata payload and `cardano-cli` command for the
   next step.
4. **Register your pool**, with the Application Code in the transaction metadata and your BLS key
   in the certificate. That one transaction proves you control the pool, lets us match it to your
   application, and registers your BLS key.
5. **Request the faucet delegation.** The
   [faucet](https://faucet.leios.play.dev.cardano.org/basic-faucet) delegate widget takes your
   bech32 pool id and delegates 1M test ada.
6. **Wait for the stake snapshot**, roughly two epochs, after which your pool starts forging.

Those steps take you through the join criteria in the next section. From then on, what keeps you
qualifying each month is the monthly criteria, which we are still finalising.

**Already registered on MusashiNet?** Your BLS key is registered and your faucet delegation may be
too. Apply, then submit an updated pool registration certificate carrying the Application Code, the
same mechanism you would use to change pledge, margin or relays.

## Eligibility criteria

These are the Criteria referenced by the Musashi Testnet Rewards Program Terms and Conditions: who
can participate, what you do once to join, and what you keep doing each month to be paid.

### Who can participate

These come from the Terms and Conditions you accept with your Rewards Program application. They
hold from the moment you apply and continuously through the Program.

| | |
|---|---|
| **Age** | 18 or older, with legal capacity to accept the Terms |
| **Pool control** | You operate the pool and control its cold signing keys |
| **Pools per operator** | Up to 3. The pools you apply with must not share relay nodes |
| **Sanctions** | You are not a target of sanctions administered by OFAC, the UN, the EU or UK HM Treasury, and you are not located in or a resident of a sanctioned jurisdiction or of Singapore |
| **Affiliation** | You are not an employee, officer, director or contractor of IOG or its affiliates |
| **Identity verification** | You complete verification with our third party provider. The link they email you expires after 24 hours |
| **Payout address** | Your destination address passes sanctions and illicit activity screening |

Submitting an application on its own does not qualify you for a reward. The criteria below do.

### To join

| # | Criterion | Checked from |
|---|-----------|--------------|
| A1 | [Rewards Program application](https://forms.gle/Y2VVFSZdykmMjFTs9) submitted | Application form |
| A2 | **Pool control proven.** The Application Code we email you appears in the transaction metadata of the same transaction as your pool registration certificate | Chain |
| A3 | **Reconciliation.** The on-chain Application Code matches an application, and the pool id you claimed matches the pool registration certificate | Chain and application |
| A4 | BLS key registered | Chain |
| A5 | **Faucet delegation requested.** 1M test ada, which makes your pool eligible for block production in every epoch and a member of the voting committee once one is established | Chain |

You can apply at any point in the application period. Applying part way through a month leaves less
of that month in which to qualify.

After a respin, submit a new pool registration certificate carrying **the same Application Code we
emailed you**. An Application Code identifies a participant rather than a transaction, so
Application Codes are reusable.

### To qualify, each month

:::note To be defined

The monthly criteria are still being worked out, including which telemetry we ask for and how it is
measured. They will be published on this page once settled, and announced in
[`#musashi-testnet` on Discord](https://discord.gg/AyUXD9VHn).

:::

This does not hold up joining. Applying, registering your pool and starting to forge are the join
criteria above, and you can complete all of them now.

### What we score, and what we study

We score participation, not performance. Your orphan rate, your vote timing and how your propagation
compares with other pools never affect payment: those belong to the telemetry analysis, which runs on
its own track.

### How many pools can participate

The Program rewards up to 100 pools. If more than 100 qualify in a month, qualifying pools are ranked
by application order and the first 100 are rewarded for that month. Meeting every criterion on this page
does not guarantee rewards. Being early helps! 

## What we collect

This data is the Program's deliverable. We analyse it, and we do not disqualify anyone on it.

Examples of the kind of data we expect to ask for:

- Forging logs
- Voting logs
- Diffusion logs: block and vote propagation timings
- Node version
- Clock offset against NTP
- Host resources

Treat that list as indicative rather than final. It will change as the analysis develops and as the
protocol does. The scripts and any other supported collection methods will be published in the
[ouroboros-leios repository](https://github.com/input-output-hk/ouroboros-leios), and changes to them
announced in [`#musashi-testnet` on Discord](https://discord.gg/AyUXD9VHn).

Running an older node version or smaller hardware than another participant has no effect on your
eligibility, as long as your node keeps up: the version stays compatible with the current chain, and
the machine can follow it, forge its blocks and issue its votes.

Timestamps are cross-checked between pools. A clock that disagrees with every other pool's has its
data excluded from analysis, never a payment withheld.

## Terms of participation

Expectations rather than scored criteria. We handle these by exception.

- Respond to the engineering team when they reach out
- Join coordinated test windows
- Report honestly
- Exit cleanly at the end of the Program, with delegation returned and the pool retired

## Where to ask

Questions about these criteria go to
[`#musashi-testnet` on Discord](https://discord.gg/AyUXD9VHn). Rewards, payment and the full legal
terms are covered by the Musashi Testnet Rewards Program Terms and Conditions, which you read and
accept in the [application form](https://forms.gle/Y2VVFSZdykmMjFTs9).
