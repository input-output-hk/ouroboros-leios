## Quick TODO list

## Show consensus ChainTree in node inspector

Post the node's consensus chain tree in its stats update as a list of
blocks with number, hash and previous hash.  UI displays this as a horizontal
line of linked squares with additional 'tracks' for forks, each block
shown with number and hash suffix as in the node tip.  Scale it to either
the last 10 blocks or the earliest fork point, whichever is earlier.

## Make the inspector an overlay

The inspector is getting limited by width with the chain display.
Make it a semi-transparent overlay, on the right-hand 50% of the graph
which only appears when a node is selected.  The side bar can be all
event log.

## Cluster control

Control of the cluster from the UI - ability to set size, degree
and latency parameters and restart the cluster

## Sample models

Provide a dropdown of sample models to load to set cluster parameters
before 
