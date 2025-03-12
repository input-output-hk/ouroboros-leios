# Workflow for running experiments

1. Copy Haskell executable to this folder.
2. Edit [env.sh](env.sh) to set the MongoDB host and database names.
3. Execute [run-experiment.sh](run-experiment.sh).
4. Execute [run-queries.sh](run-queries.sh).
5. Execute `nix run ..` to launch a Jupyter server.
6. Run Jupyter notebook [analysis.ipynb](analysis.ipynb).
