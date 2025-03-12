# Simulation experiments at tag `leios-2025w11`

## Workflow for running experiments

1. Copy Haskell executable to this folder.
2. Edit [env.sh](env.sh) to set the MongoDB host and database names.
3. Execute [run-experiment.sh](run-experiment.sh).
4. Execute [run-queries.sh](run-queries.sh).
5. Execute `nix run ..` to launch a Jupyter server.
6. Run Jupyter notebook [analysis.ipynb](analysis.ipynb).

## Archive of results


### CPU usage

- https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w11/cpus.csv.gz

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -     | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -     | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -     | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-body-avg-size-bytes    | B     | scenario | The size of the IBs.                                                                          |
| ib-generation-probability | #/s   | scenario | The rate of IB generation.                                                                    |
| leios-stage-length-slots  | s     | scenario | The length of each pipeline stage.                                                            |
| slot                      | s     | output   | The slot number in which the task was completed.                                              |
| node                      | -     | output   | The unique identifier for the node that performed the task.                                   |
| task                      | -     | output   | The name of the task performed.                                                               |
| duration                  | s     | output   | CPU time spent on the task.                                                                   |


### IB generation

- https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w11/ibgen.csv.gz

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -     | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -     | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -     | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-body-avg-size-bytes    | B     | scenario | The size of the IBs.                                                                          |
| ib-generation-probability | #/s   | scenario | The rate of IB generation.                                                                    |
| leios-stage-length-slots  | s     | scenario | The length of each pipeline stage.                                                            |
| time                      | s     | output   | The time when the IB was generated.                                                           |
| node                      | -     | output   | The unique identifier for the node that generated the IB.                                     |
| ib                        | -     | output   | The unique identifier for the IB.                                                             |
| size                      | B     | output   | The size of the IB.                                                                           |
| eb-count                  | #     | output   | The number of EBs referencing the IB.                                                         |
| eb-first                  | s     | output   | The time when the IB was first referenced by an EB.                                           |
| eb-last                   | s     | output   | The time when the IB was last referenced by an EB.                                            |


### EB generation

- https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w11/ebgen.csv.gz

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -     | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -     | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -     | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-body-avg-size-bytes    | B     | scenario | The size of the IBs.                                                                          |
| ib-generation-probability | #/s   | scenario | The rate of IB generation.                                                                    |
| leios-stage-length-slots  | s     | scenario | The length of each pipeline stage.                                                            |
| time                      | s     | output   | The time when the EB was generated.                                                           |
| node                      | -     | output   | The unique identifier for the node that generated the EB.                                     |
| eb                        | -     | output   | The unique identifier for the EB.                                                             |
| size                      | B     | output   | The size of the EB.                                                                           |
| ib-count                  | #     | output   | The number of IBs referenced by the EB.                                                       |
| rb-count                  | #     | output   | The number of RBs referencing the EB via a certificate.                                       |
| rb-first                  | s     | output   | The time when the EB was first referenced by an RB.                                           |
| rb-last                   | s     | output   | The time when the EB was last referenced by an RB.                                            |


### RB generation

- https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w11/rbgen.csv.gz

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -     | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -     | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -     | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-body-avg-size-bytes    | B     | scenario | The size of the IBs.                                                                          |
| ib-generation-probability | #/s   | scenario | The rate of IB generation.                                                                    |
| leios-stage-length-slots  | s     | scenario | The length of each pipeline stage.                                                            |
| time                      | s     | output   | The time when the RB was generated.                                                           |
| node                      | -     | output   | The unique identifier for the node that generated the RB.                                     |
| rb                        | -     | output   | The unique identifier for the RB.                                                             |
| size                      | B     | output   | The size of the RB.                                                                           |
| eb-count                  | #     | output   | The number of EBs referenced by the RB.                                                       |


### Receipt of messages

- https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w11/receipts.csv.gz

| Field                     | Units | Type     | Description                                                                                   |
|---------------------------|-------|----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -     | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -     | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -     | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-body-avg-size-bytes    | B     | scenario | The size of the IBs.                                                                          |
| ib-generation-probability | #/s   | scenario | The rate of IB generation.                                                                    |
| leios-stage-length-slots  | s     | scenario | The length of each pipeline stage.                                                            |
| kind                      | -     | output   | The kind of item: `IB`, `EB`, `RB`, or `VT`.                                                  |
| item                      | -     | output   | The unique identifier for the item.                                                           |
| producer                  | -     | output   | The unique identifier for the node that generated the item.                                   |
| sent                      | s     | output   | The time when the item was originally sent from the producer.                                 |
| recipient                 | -     | output   | The unique identifier for the node that received the item.                                    |
| received                  | s     | output   | The time when the item was received.                                                          |
| elapsed                   | s     | output   | The time elapsed between when the item was originally sent by the producer and then received. |
