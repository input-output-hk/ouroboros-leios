# Leios demo

Ouroboros Leios prototype demos.

There are other, component-specific demos you might be looking for:

- [Visualizer](../ui) contains a few stored scenarios that are standalone demos
- [Cryptography](../crypto-benchmarks.rs/demo) demo of signing/verifying votes and certificates
- [Trace translator](../scripts/trace-translator/demo) has an example/demo

## Prototypes

Leios prototyping is visibile in the following PRs:

1. [cardano-node](https://github.com/IntersectMBO/cardano-node/pull/6386)
2. [ouroboros-consensus](https://github.com/IntersectMBO/ouroboros-consensus/pull/1793)
3. [ouroboros-network](https://github.com/IntersectMBO/ouroboros-network/tree/nfrisby/leios-202511-demo)

All prototyping artifacts are in their `leios-prototype` branch.
For each demo a special tag `leios-prototype-demo-YYYYMM` will be attached to denote the components used in the demo for a particular month.

## Flake inputs

The repository pulls in patched cardano-node and ouroboros-consensus as visible
in [flake.nix](../flake.nix):

```nix
    cardano-node.url = "github:intersectmbo/cardano-node?ref=...";

    ouroboros-consensus.url = "github:intersectmbo/ouroboros-consensus?ref=...";
```

To point to newer/different versions you want to set the appropriate
[ref](https://git-scm.com/book/en/v2/Git-Internals-Git-References).

> The refs in these two URLs need to identify commits that have up-to-date
> source-repository-packages for the custom commits used in ouroboros-network,
> ouroboros-consensus, cardano-node.

```shell
nix flake lock --update-input cardano-node --update-input ouroboros-consensus
```

## build.nix convention

Every `build.nix` files is a [flake-parts module](https://flake.parts/) and is
automatically loaded when found.

## Using the repository

Enter the shell either by

```shell
nix develop .#dev-demo
```

or if you're using Direnv the shell will automatically load once you

```shell
direnv allow
```

To invoke code formatting and checks on the entire repo use

```shell
$ nix fmt
black................................................(no files to check)Skipped
deadnix..................................................................Passed
markdownlint.............................................................Passed
nixfmt-rfc-style.........................................................Passed
shellcheck...............................................................Passed
```

or alternatively in the shell

```shell
$ pre-commit run --all
black................................................(no files to check)Skipped
deadnix..................................................................Passed
markdownlint.............................................................Passed
nixfmt-rfc-style.........................................................Passed
shellcheck...............................................................Passed
```

This repository is using
[git-hooks.nix](https://github.com/cachix/git-hooks.nix) and you can manage them in:

1. [top level configuration](../pre-commit-hooks.nix).
1. [demo configuration](./pre-commit-hooks.nix).
