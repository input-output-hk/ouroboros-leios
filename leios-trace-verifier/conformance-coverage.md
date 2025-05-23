# Potential conformance tests

| Test                                                                                         | Currently<br/>in Agda spec | Potentially<br/>in Agda spec | Potentially<br/>outside of Agda spec |
| -------------------------------------------------------------------------------------------- | :------------------------: | :--------------------------: | :----------------------------------: |
| Node either produces an IB or declares not                                                   |             ✔              |                              |                                      |
| Node either produces and EB or declares not                                                  |             ✔              |                              |                                      |
| Node either votes or declares not                                                            |             ✔              |                              |                                      |
| Node produces IB iff sortition requires                                                      |             ✘              |              ✔               |                                      |
| Node produces EB iff sortition requires                                                      |             ✘              |              ✔               |                                      |
| Node produces a maximum of one IB per slot                                                   |           **?**            |                              |                                      |
| Node produces a maximum of one EB per stage                                                  |           **?**            |                              |                                      |
| Node produces a maximum of one vote per stage                                                |           **?**            |                              |                                      |
| Node votes iff sortition requires                                                            |             ✘              |              ✔               |                                      |
| Node votes on EB iff it is in the same pipeline as the voting                                |           **?**            |                              |                                      |
| Node diffuses non-expired IBs iff not equivocated twice or more                              |           **?**            |                              |                                      |
| Node diffuses non-expired EBs iff not equivocated twice or more                              |           **?**            |                              |                                      |
| Node does not diffuse expired IBs                                                            |           **?**            |                              |                                      |
| Node does not reference expired IBs in EBs                                                   |           **?**            |                              |                                      |
| Node does not diffuse expired EBs                                                            |           **?**            |                              |                                      |
| Node does not reference expired EBs in EBs                                                   |           **?**            |                              |                                      |
| Node does not reference expired EBs in RB certificates                                       |           **?**            |                              |                                      |
| Nodes does not reference an IB by a new EB if the IB is known to be referenced by another EB |           **?**            |                              |                                      |
| Node's produced EB references the most recent RB known to it                                 |           **?**            |                              |                                      |
| Node's produced EB includes IBs from current pipeline iff the IB has arrived in time         |           **?**            |                              |                                      |
| Node's produced EB includes IBs from prior pipelines iff the IBs are eligible                |           **?**            |                              |                                      |
| Node certifies EB and includes it in RB iff there is a quorum of votes                       |           **?**            |                              |                                      |
| Node diffuses IBs in freshest-first order                                                    |           **?**            |                              |                                      |
| Node diffuses EBs in freshest-first order                                                    |           **?**            |                              |                                      |
| Node diffuses votes in freshest-first order                                                  |           **?**            |                              |                                      |
| Node includes txs in IB iff the IB has the correct shard                                     |             ✘              |                              |                                      |
| Node does not include txs in IB if it has seen a conflicting tx in an IB                     |             ✘              |                              |                                      |
|                                                                                              |                            |                              |                                      |
