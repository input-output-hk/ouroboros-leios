{
  inputs,
  outputs,
  pkgs,
  ...
}:
{
  name = "Leios Demo NixOS test";

  nodes = {
    immdb-node = {
      imports = [
        (import ./immdb-node/os.nix {
          inherit inputs outputs pkgs;
          immdb-server =
            inputs.ouroboros-consensus.legacyPackages."${pkgs.system
            }".hsPkgs.ouroboros-consensus-cardano.getComponent
              "exe:immdb-server";
        })
      ];
      networking.domain = "local";
    };
    leios-node = {
      imports = [
        (import ./leios-node/os.nix { inherit inputs outputs pkgs; })
      ];
      networking.domain = "local";
      environment.systemPackages = [ pkgs.dnsutils ];
      services.resolved.enable = true;
    };
    downstream-node = {
      imports = [
        (import ./downstream-node/os.nix { inherit inputs outputs pkgs; })
      ];
      networking.domain = "local";
      environment.systemPackages = [ pkgs.dnsutils ];
      services.resolved.enable = true;
    };
    tracer-node = {
      imports = [
        (import ./tracer-node/os.nix { inherit inputs outputs pkgs; })
      ];
      networking.domain = "local";
      environment.systemPackages = [ pkgs.dnsutils ];
      services.resolved.enable = true;
      virtualisation.forwardPorts = [
        {
          from = "host";
          host.port = 3001;
          guest.port = 3001;
        }
        {
          from = "host";
          host.port = 3000;
          guest.port = 3000;
        }
        {
          from = "host";
          host.port = 12345;
          guest.port = 12345;
        }
      ];
    };
  };

  testScript = ''
    start_all()

    # Wait until the respective services are up
    tracer_node.wait_for_unit("cardano-tracer.service")
    immdb_node.wait_for_unit("immdb-server.service")
    leios_node.wait_for_unit("cardano-node.service")
    downstream_node.wait_for_unit("cardano-node.service")

    # Wait until leios-node and downstream-node synced with immdb-node
    # NOTE(bladyjoker): Block 51 is the tip
    # [0.139717s] BlockNo 51  SlotNo 994      6685f44f32433d0817b6edf5f9e00aaaa3c4986524b8b453a620825747a936cc
    leios_node.wait_until_succeeds("cardano-cli query tip | grep hash | grep -q '6685f4'")
    downstream_node.wait_until_succeeds("cardano-cli query tip | grep hash | grep -q '6685f4'")

    # Collect logs from immdb-node (read them in result/ after nix build)
    immdb_node.execute("journalctl -u immdb-server --no-pager > immdb-server.logs")
    immdb_node.execute("journalctl -u immdb-server --output json > immdb-server.logs.json")
    immdb_node.copy_from_vm("immdb-server.logs", "immdb-node")
    immdb_node.copy_from_vm("immdb-server.logs.json", "immdb-node")

    # Collect logs from tracer-node (read them in result/ after nix build)
    tracer_node.execute("journalctl -u cardano-tracer --no-pager > cardano-tracer.logs")
    tracer_node.execute("journalctl -u cardano-tracer --output json > cardano-tracer.logs.json")
    tracer_node.copy_from_vm("cardano-tracer.logs", "tracer-node")
    tracer_node.copy_from_vm("cardano-tracer.logs.json", "tracer-node")
  '';
}
