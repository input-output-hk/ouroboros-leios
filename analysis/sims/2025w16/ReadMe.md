# Simulation experiments at tag `leios-2025w16`


## Workflow for running experiments

1. Copy the Haskell and Rust executables to this folder.
2. Execute [build-experiments.sh](build-experiments.sh).
3. Execute [run-experiments.sh](run-experiments.sh).
4. Execute [combine-results.sh](combine-results.sh).
5. The results are in the `results/` folder.
6. Execute `nix run ..` to launch a Jupyter server.
7. Run Jupyter notebook [analysis.ipynb](analysis.ipynb).


## Archive of results

| Results             | 100-node network                                                             |
|---------------------|------------------------------------------------------------------------------|
| Resource usage      | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/resources.csv.gz |
| CPU usage           | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/cpus.csv.gz      |
| IB generation       | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/ibgen.csv.gz     |
| EB generation       | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/ebgen.csv.gz     |
| RB generation       | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/rbgen.csv.gz     |
| Receipt of messages | https://leios-sim-output.s3.us-east-1.amazonaws.com/2025w16/receipts.csv.gz  |


### Data dictionary


#### Resource usage

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| node                      | -          | output   | The unique identifier for the node that performed the task.                                   |
| egress                    | B          | output   | The number of bytes leaving the node during the simulation.                                   |
| disk                      | B          | output   | The number of bytes stored to disk during the simulation.                                     |
| total\_cpu                | s          | output   | The total CPU consumed during the simulation.                                                 |
| maximum\_cpu              | %/100      | output   | The one-second average peak CPU fraction consumed during the simulation.                      |


#### CPU usage

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| slot                      | s          | output   | The slot number in which the task was completed.                                              |
| node                      | -          | output   | The unique identifier for the node that performed the task.                                   |
| task                      | -          | output   | The name of the task performed.                                                               |
| duration                  | s          | output   | CPU time spent on the task.                                                                   |


#### IB generation

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| ib                        | -          | output   | The unique identifier for the IB.                                                             |
| node                      | -          | output   | The unique identifier for the node that generated the IB.                                     |
| time                      | s          | output   | The time when the IB was generated.                                                           |
| size                      | B          | output   | The size of the IB.                                                                           |
| eb-count                  | #          | output   | The number of EBs referencing the IB.                                                         |


#### EB generation

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| eb                        | -          | output   | The unique identifier for the EB.                                                             |
| node                      | -          | output   | The unique identifier for the node that generated the EB.                                     |
| time                      | s          | output   | The time when the EB was generated.                                                           |
| size                      | B          | output   | The size of the EB.                                                                           |
| ib-count                  | #          | output   | The number of IBs referenced by the EB.                                                       |
| eb-count                  | #          | output   | The number of EBs referenced by the EB.                                                       |
| rb-count                  | #          | output   | The number of RBs referencing the EB via a certificate.                                       |


#### RB generation

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| rb                        | -          | output   | The unique identifier for the RB.                                                             |
| node                      | -          | output   | The unique identifier for the node that generated the RB.                                     |
| time                      | s          | output   | The time when the RB was generated.                                                           |
| size                      | B          | output   | The size of the RB.                                                                           |
| eb-count                  | #          | output   | The number of EBs referenced by the RB.                                                       |


### Receipt of messages

| Field                     | Units      | Type     | Description                                                                                   |
|---------------------------|-------     |----------|-----------------------------------------------------------------------------------------------|
| simulator                 | -          | scenario | The name of the simulator used to run the experiment.                                         |
| label                     | -          | scenario | A string describing the experiment, in this case `default`.                                   |
| network                   | -          | scenario | A string describing the network, in this case `100 ` since the 100-node test network is used. |
| ib-generation-probability | #/s        | scenario | The rate of IB generation.                                                                    |
| ib-body-avg-size-bytes    | B          | scenario | The size of the IBs.                                                                          |
| eb-generation-probability | #/pipeline | scenario | The rate of EB generation.                                                                    |
| leios-stage-length-slots  | s          | scenario | The length of each pipeline stage.                                                            |
| kind                      | -          | output   | The kind of item: `IB`, `EB`, `RB`, or `VT`.                                                  |
| item                      | -          | output   | The unique identifier for the item.                                                           |
| recipient                 | -          | output   | The unique identifier for the node that received the item.                                    |
| received                  | s          | output   | The time when the item was received.                                                          |
| producer                  | -          | output   | The unique identifier for the node that generated the item.                                   |
| sent                      | s          | output   | The time when the item was originally sent from the producer.                                 |
| size                      | B          | output   | The size of the item.                                                                         |
| elapsed                   | s          | output   | The time elapsed between when the item was originally sent by the producer and then received. |
