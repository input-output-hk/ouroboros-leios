# Contributing to Leios

Thanks for considering contributing and help us on prototyping and
specifying the Mithril protocol for the whole benefit of the Cardano
community!

There are several ways in which you can contribute to this project:

* From reading the [research
  paper](https://iohk.io/en/research/library/papers/high-throughput-blockchain-consensus-under-realistic-network-assumptions/),
  identify questions that will need to be answered for a practical
  implementation of the protocol
* Analyse and document the protocol, its performance profile,
  resources requirements, etc.
* Contribute code for prototypes, simulations, numerical analysis, graphing...
* Use the provided prototypes and simulations and provide feedback

## Communication channels

Should you have any questions or need some help in getting set up, you can use
these communication channels to reach the Leios R&D community and get answers in a way
where others can benefit from it as well:

- #leios on the IOG [Discord server]https://discord.gg/Bc6ABMS3)
- GitHub [Discussions](https://github.com/input-output-hk/ouroboros-leios/discussions)

## Your first contribution

Contributing to the documentation, its translation, reporting bugs or proposing features are awesome ways to get started.

### Documentation

We host our documentation / user manual as a website [here](https://leios.cardano-scaling.org/).

Each page has an "Edit this page" button which should take you to the source
file containing the markup. Should you would want to extend the documentation or
find some errors, please file an issue pointing to the mistake or even better,
create a pull request with the changes directly!

### Issues

Whether you found a bug in some code in this repository, or have a specific request to improve it, please [submit an issue](https://github.com/input-output-hk/ouroboros-leios/issues/new).

For bug reports, it's very important to explain

- what version you used (typically a commit SHA or a released version number),
- steps to reproduce (or steps you took),
- what behavior you saw (ideally supported by logs), and
- what behavior you expected.

### Feature ideas

For ideas and questions that need some discussions, we use the [Ideas
discussions
category](https://github.com/input-output-hk/ouroboros-leios/discussions/)
to discuss. Please note that we expect all participants to those
discussions to be mindful of and respect our [Code of
Conduct](CODE-OF-CONDUCT.md).

## Making changes

When contributing code, it helps to have discussed the rationale and (ideally)
how something is implemented in a feature idea or bug ticket beforehand.

### Building & Testing

#### Haskell

To build Haskell code in this repository, you need to install:

* The [GHC](https://www.haskell.org/ghc/) compiler version 9.10.1
* [cabal](https://www.haskell.org/cabal/) build tool version 3.12.1.0

> [!NOTE]
> Installing those tools might depend on your system's details, we suggest two different methods:
>
> * Install [GHCup](https://www.haskell.org/ghcup/) to manage various tools from the Haskell ecosystem
> * Use the provided Nix shell by invoking `nix develop`

Running `cabal update && cabal build all` at the top-level of the
project should build all the Haskell components. Tests are run with
`cabal test all`.

Besides these general build instructions, some components might document
additional steps and useful tools in their `README.md` files.

### Coding standards

Make sure to read and follow our [Coding
Standards](CODING-STANDARDS.md), it includes guidelines on code
formatting, general style, and some processes. To propose new
standards or changes to the existing standards, file an issue.

### Updating the package index state

The `cabal.project` file contains the package index state, which freezes the package indices at a particular point in time. These can be updated whenever one of the Haskell projects in this repository requires a new or upgraded dependency. To upgrade these, run `cabal update -z`:

```
$ cabal update -z
Downloading the latest package lists from:
- hackage.haskell.org
- cardano-haskell-packages
Package list of cardano-haskell-packages is up to date.
The index-state is set to 2024-10-04T09:54:45Z.
Package list of hackage.haskell.org has been updated.
The index-state is set to 2024-10-04T11:45:34Z.
To revert to previous state run:
    cabal v2-update 'hackage.haskell.org,2024-10-04T10:22:50Z'
```

Then copy the new index states from the command output into the `cabal.project` file:

```
index-state:
  , hackage.haskell.org 2024-10-04T11:45:34Z
  , cardano-haskell-packages 2024-10-04T09:54:45Z
```

NOTE: Is there a cabal command to update the `cabal.project` file?


### Creating a pull request

Thank you for contributing your changes by opening a pull requests! To get
something merged we usually require:

- Description of the changes - if your commit messages are great, this is less important
- Quality of changes is ensured - through new or updated automated tests in [GitHub Actions](https://github.com/input-output-hk/ouroboros-leios/actions)
- Change is related to an issue, feature (idea) or bug report - ideally discussed beforehand
- Well-scoped - we prefer multiple PRs, rather than a big one
- All your commits must be [signed](https://docs.github.com/en/authentication/managing-commit-signature-verification/signing-commits) in order to be merged in the `main` branch

### Versioning & Changelog

TBD

### Releasing

TBD
