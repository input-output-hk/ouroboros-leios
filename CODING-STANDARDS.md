# Coding Standards

This document provides rules, guidelines, and advices on the structure
of submitted code. As we expect this repository to host code in
various languages, this document will be expanded as needed and we
might link to other relevant documents.

## Haskell

### Code formatting

* Haskell code must be formatted using [fourmolu](https://fourmolu.github.io/) tool, using [provided](fourmolu.yaml) configuration file.
* Cabal files must be formatted using [cabal-fmt](https://github.com/phadej/cabal-fmt).

Check both tools' documentation on how to set it up in your particular environment.

### Testing

We use [hspec](https://hspec.github.io) for writing tests, and we
favour [QuickCheck](https://hackage.haskell.org/package/QuickCheck)
tests over unit tests. All submitted code should be accompanied with
some tests.

## Git

### Commit message format

Here are [seven rules](https://cbea.ms/git-commit/) for great git commit messages:

* Separate subject from body with a blank line
* Limit the subject line to 50 characters (soft limit)
* Capitalize the subject line
* Do not end the subject line with a period
* Use the imperative mood in the subject line and suffix with ticket number if applicable
* Wrap the body at 72 characters (hard limit)
* Use the body to explain what and why vs. how

> [!NOTE] Why?
> Git commit messages are our only source of why something was changed the way it was changed. So we better make the readable, concise and detailed (when required).

### Squash & Rebase PRs

When merging accepted Pull Requests, use `Squash & Merge` and ensure the branch has been rebased on top of `main`.

> [!NOTE] Why?
> Individual commits history of PRs are mostly useless, and PRs should be small and self-contained.
