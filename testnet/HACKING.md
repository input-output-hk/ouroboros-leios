This document summarizes some commands that are useful for debugging an error that is reproducible on the Leios testnet (for example, a syncing node stalls).
Specifically, this is for the case where the existing trace messages do not yet provide enough information (for example, you'd like to add some `Debug.Trace` dumps, etc).

There are likely at least three moving parts.

- `ouroboros-consensus`, where most of the Leios logic lives.
- `cardano-node`, which integrates the Consensus Layer into a runnable node.
- `ouroboros-leios` (this repository), which automatically runs a node connected to the Leios testnet.

The following commands minimized my iteration time.

- To build/adjust my `cardano-node` exe:
    - Checkout the relevant "Leios release" of `cardano-node`.
        - The release page (eg https://github.com/input-output-hk/ouroboros-leios/releases/tag/prototype-2026w27b) lists the commit.
	  If you click on that commit, you'll see the changes to `flake.nix`.
	  Those should include the commit hash of the `cardano-node` repo that was used for that release.
    - Checkout the relevant "Leios release" of `ouroboros-consensus-node`.
        - That `cardano-node` commit's `cabal.project` file will have a `source-repository-package` stanza that specifies the corresponding `ouroboros-consensus` commit.
    - Back in `cardano-node` working tree, enter its development environment via `nix develop`.
        - If this fails (e.g. some `source-repository-package` stanza's commit can't be found), the easiest option is likely to comment out the relevant stanzas of `./cabal.project`.
          For our purposes, we only need the `exe:cardano-node` Cabal component to build.
    - Then delete the `ouroboros-consensus` `source-repository-package` stanza in `./cabal.project` and add the path to your local `ouroboros-consensus` working tree to its `packages:` list.
    - Then run `cabal build exe:cardano-node`, edit some files in your `ouroboros-consensus` working tree etc, repeat.
- To run my `cardano-node` exe against the testnet:
    - Checkout a recent commit of `ouroboros-leios`.
    - Enter the `./testnet` directory.
    - Enter the developer environment via `nix develop .#dev-testnet`.
    - Set the `CARDANO_NODE` environment variable to the absolute path to your `cardano-node` exe.
      (For example, what `cabal list-bin exe:cardano-node` reports from within your `cardano-node` directory.)
    - Run that node against the testnet via `XRAY=0 PATH="$(dirname $CARDANO_NODE):$PATH" ./run.sh` (the `XRAY=0` part is optional, to disable the Grafana tooling).
        - If your terminal captures the F10 keystroke, CTRL-C should also (eventually) let you exit the resulting `process-compose` TUI.
        - (Don't plan to use this terminal for anything else; if you sleep the `process-compose` TUI, its pipe buffers will overfow quite quickly.)

Those are the details of one approach that worked for me recently.
If you find a simpler and/or more reliable set of commands, please open a PR against this file.

Also, if you're bothering with this loop in order to workaround the absence of some information in the tracers, please, throughout and/or at the end of your debugging, consider enriching the tracers to including additional info.
