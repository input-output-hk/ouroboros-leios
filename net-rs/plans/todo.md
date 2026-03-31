## Quick TODO list

## Show consensus ChainTree in node inspector

Post the node's consensus chain tree in its stats update as a list of
blocks with number, hash and previous hash.  UI displays this as a horizontal
line of linked squares with additional 'tracks' for forks, each block
shown with number and hash suffix as in the node tip.  Scale it to either
the last 10 blocks or the earliest fork point, whichever is earlier.

## UI memory leak

The UI has a serious memory leak.  11G after an hour.

## Cluster control

Control of the cluster from the UI - ability to set size, degree
and latency parameters and restart the cluster

## Sample models

Provide a dropdown of sample models to load to set cluster parameters
before 
