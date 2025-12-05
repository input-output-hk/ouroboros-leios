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
nix develop
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
[git-hooks.nix](https://github.com/cachix/git-hooks.nix) and to manage said
hooks edit [./pre-commit-hooks.nix](./pre-commit-hooks.nix).

## Running the Leios 202511 demo

Run the Leios X-Ray

```shell
export LOG_PATH=".tmp-leios-202511-demo/*/log"
export SS_FILTER="( sport = 3001 and dport = 3002 ) or ( sport = 3002 and dport = 3001 ) or ( sport = 3002 and dport = 3003 ) or ( sport = 3003 and dport = 3002 )"
nix run git+ssh://git@github.com/IntersectMBO/ouroboros-leios#x_ray
```

Run the Leios experiment with default configuration

```shell
nix run git+ssh://git@github.com/IntersectMBO/ouroboros-leios#leios_202511_demo
```

If you want to further configure the experiment set the following environment
variables:

```shell
CARDANO_NODE=cardano-node
IMMDB_SERVER=immdb-server
DATA_DIR=data
REF_SLOT=41
SECONDS_UNTIL_REF_SLOT=5
LEIOS_MANIFEST=manifest.json
ANALYSE_PY=analyse.py
PYTHON3=python
CARDANO_NODE=cardano-node
IMMDB_SERVER=immdb-server
```

To clean up just delete the working directories

```shell
rm -fr .tmp-leios-202511-demo
rm -fr .tmp-x-ray
```
