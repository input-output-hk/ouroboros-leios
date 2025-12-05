# Leios Demo NixOS test

Leios demo with NixOS test based setup for spawning reproducible and/or interactive demo scenarios. Also includes observability stack using prometheus, loki and grafana.

``` mermaid
flowchart LR

  subgraph Mock upstream
    immdb-node
  end

  subgraph System under test
    leios-node
  end

  subgraph Mock downstream
    downstream-node
  end

  immdb-node --> leios-node --> downstream-node
  downstream-node --> leios-node --> immdb-node


  immdb-node -.-> tracer-node
  leios-node -.-> tracer-node
  downstream-node -.-> tracer-node


  subgraph tracer-node
    direction TB
    cardano-tracer --> prometheus
    cardano-tracer --> journald --> alloy --> loki
    prometheus --> grafana
    loki --> grafana
  end
```

## Files and directories

- `./test.nix` contains the NixOS test definition where we can script various scenarios.
- `./leios-node/` contains the NixOS definition for the "leios-node" that runs the "Ouroboros Leios" patched cardano-node under test.
- `./downstream-node/` contains the NixOS definition for the "downstrem-node" that runs node which downloads blocks from `leios-node`.
- `./immdb-node/` contains the NixOS definition for the "immdb-node" that runs the Immutable DB server.
- `./tracer-node/` contains the NixOS definition for the "tracer-node" that collects logs from all cardano-node hosts.
- `./services/` - contains various NixOS service definitions

## Nix build targets

To run the test scenario with Nix:

```shell
$ nix build .#leios-demo-nixos-test
$ find result/
result/
result/immdb-node
result/immdb-node/immdb-server.logs.json
result/immdb-node/immdb-server.logs
result/tracer-node
result/tracer-node/cardano-tracer.logs.json
result/tracer-node/cardano-tracer.logs
```

Once it finishes the `result` directory will contains the logs collected from the "immdb-node" and the rest of the logs are sent to`the "tracer-node" from which we download the logs.

### Interactive demo

Fun part! To start the nodes defined by the test scenario run:

```shell
$ nix run .#leios-demo-nixos-test.driverInteractive
additionally exposed symbols:
    immdb-node, leios-node,
    vlan1,
    start_all, test_script, machines, vlans, driver, log, os, create_machine, subtest, run_tests, join_all, retry, serial_stdout_off, serial_stdout_on, polling_condition, Machine
>>>
```

This puts you in a IPython shell. To start all nodes run:

```python
>>> start_all()
```

After a bit you should see QEMU windows corresponding to each node in the test scenario.
Login as "root".
