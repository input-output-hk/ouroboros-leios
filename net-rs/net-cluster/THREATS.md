Threat models usage
====================

This document describes threat models config files provided, and 
gives hints about their invocation and research.

Implemented threat models
----------------------------

The implemented models are activated by the proper `net-cluster` configuration.
Default configurations are provided in `configs` subdirectory, here is their list:

| Config file           | Threat model                          |
|-----------------------|---------------------------------------|
|sample-cluster-t22.toml| T21 and T22 threat model: EB messages |
|                       | propagation disruption for committee  |
|                       | nodes (T21) and ordinary nodes (T22). |

Invocation
-------------

To invoke a threat model, use the following command:

`cargo run --release -p net-cluster -- --config net-cluster/configs/THREAT-CONFIG.toml`

Here, instead of `THREAT-CONFIG`, insert the name of the corresponding threat config.

In order to visualize the network activity in the corresponding configuration,
invoke `net-ui` interface in a separate console, then press 'o' and 'ENTER',
when `net-ui` console will start. This operation will open a web-browser with the
net cluster UI.

Specific threat models
-----------------------

### T21 and T22 threats

These threats are implemented using the same code, the difference between them is 
in parameters configuration.

They both suppose disruption of EB messages delivery: T21 for the committee nodes, and
T22 for non-committee (non-voting) nodes.
More information about the mechanism is given in comments to the behaviour implementation:
`shared-rs/consensus/src/behaviour/behaviours/t22.rs` and in the corresponding config file.

#### Notes about visualisation.

* In order to visualise the network activity, use `net-ui` module.
* Depending on the config file parameters, one should see disruptions to EB propagation:
  the bigger disruption, the smaller amount of eb blocks is certified. Or, in other words,
  the smaller are thresholds, the smaller amount of eb blocks is certified.
* The disruptions are visualised as smaller amount of blocks with '*' in chain view of UI.
* In more detail this can be viewed in VotePanel (activated by 5th icon on the left sidebar).
  One can see the actual EB messages in the panel, received by nodes, and the actual votes cast.
* The icons at slot/node intersection can be read as follows:
  * green tick means that the node received EB message for the slot.
  * green circle with tick means that the node generated this EB message for the slot 
    and voted for it.
  * cyan circle means that the node received RB + EB.
  * yellow circle means that the node received RB, but did not receive anything else.
  * grey circle means that the node did not receive any messages for the slot
  * red circle means that the node has 'impossible' status: e.g. it did not receive RB, but
    received EB. This may happen due to delays (net-cluster received events info with delay,
    then this status will disappear quite soon), but also can happen due to a bug.

The more disruptions in the network, the smaller number of EB messages -- and smaller
amount of votes. If the number of votes for a block is less than 75% of the committee size
(less than 75% of nodes in a slot have green tick), then the block will not be certified, 
and '*' will not appear. By adjusting the thresholds, one can visualise the number of
received eb blocks and number of votes cast.
