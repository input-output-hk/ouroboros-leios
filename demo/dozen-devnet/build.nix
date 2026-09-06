{
  perSystem =
    {
      pkgs,
      config,
      lib,
      system,
      inputs',
      ...
    }:
    lib.optionalAttrs (system == "x86_64-linux") {
      devShells.dev-demo-dozen-devnet = pkgs.mkShell {
        name = "dev-demo-dozen-devnet";
        src = ./.;
        inputsFrom = [
          config.devShells.dev-demo
          config.devShells.dev-demo-extras-x-ray
        ];
        packages = [
          pkgs.process-compose
          pkgs.sqlite
          pkgs.jq
          pkgs.yq
          pkgs.envsubst
          pkgs.iproute2 # ip, tc — namespaces and traffic control
          # Patched cardano-node, matching CLI, and tx-firehose (push-based
          # N2C load generator targeting a relay) — all from leios-prototype.
          inputs'.cardano-node-leios.packages.cardano-node
          inputs'.cardano-node-leios.packages.cardano-cli
          inputs'.cardano-node-leios.packages.tx-firehose
          # Its observer: reads a mempool over N2C, reports whose load it holds.
          inputs'.cardano-node-leios.packages.mempool-monitor
          # Eventlog analysis, for forge-loop investigations. Arm a node with
          # NODE_RTS="-l"; the vanilla RTS is enough, no profiling build.
          #
          # eventlog2html is a *heap* profile renderer: without -hT it has almost
          # nothing to draw, and it never draws GC pause bars. Add -hT (heap by
          # closure type, also vanilla-RTS) to see what the forge loop allocates.
          # For "where are the GCs", use threadscope (per-capability timeline,
          # GC as bars) or ghc-events (raw events with timestamps, greppable).
          # Cheapest of all and needing none of these: NODE_RTS="-S" writes a
          # line per GC to stderr, which lands in node.log interleaved with the
          # forge traces, so the correlation is direct.
          #
          # hs-speedscope is the one that needs a profiled build: it turns the
          # cost-centre samples written under "-l -p" into a speedscope profile,
          # which beats a static flamegraph because you can filter to the slow
          # interval.
          pkgs.haskellPackages.eventlog2html
          pkgs.haskellPackages.hs-speedscope
          pkgs.haskellPackages.ghc-events
          pkgs.haskellPackages.threadscope
        ];
        # To easily interact with the relay that takes the load from within the
        # demo dir
        CARDANO_NODE_NETWORK_ID = 164;
        CARDANO_NODE_SOCKET_PATH = "tmp-devnet/relay11/node.socket";
      };

      packages.demo-dozen-devnet = pkgs.writeShellApplication {
        name = "leios-demo-dozen-devnet";
        runtimeInputs =
          config.devShells.dev-demo-dozen-devnet.nativeBuildInputs
          ++ config.devShells.dev-demo-dozen-devnet.buildInputs
          ++ [ pkgs.sqlite ] # XXX: why is this not picked up from above?
          # XXX: Integration like this is a bit weird, but required if we want
          # to have the same environment overriding + process-compose
          # integration?
          ++ config.devShells.dev-demo-extras-x-ray.buildInputs;
        runtimeEnv = {
          # Override paths to point to nix store
          SOURCE_DIR = ./.;
          # Genesis, pool keys, delegator keys, Alloy modules and dashboards are
          # shared with proto-devnet rather than duplicated.
          SHARED_CONFIG_DIR = ../proto-devnet/config;
          XRAY_SOURCE_DIR = ../extras/x-ray;
          GRAFANA_SHARE = "${pkgs.grafana}/share/grafana";
        };
        text = builtins.readFile ./run.sh;
      };
    };
}
