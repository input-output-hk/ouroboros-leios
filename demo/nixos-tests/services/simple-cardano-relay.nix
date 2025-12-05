{ cardano-node, ... }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.cardano.relay;
in
{

  imports = [
  ];

  options.cardano.relay = {
    enable = lib.mkEnableOption ''Run cardano-node relay as service'';

    config = lib.mkOption {
      type = lib.types.path;
      description = "Path to cardano-node config file";
    };

    topology = lib.mkOption {
      type = lib.types.path;
      description = "Path to topology file";
    };

    genesisAlonzo = lib.mkOption {
      type = lib.types.path;
    };

    genesisConway = lib.mkOption {
      type = lib.types.path;
    };

    genesisByron = lib.mkOption {
      type = lib.types.path;
    };

    genesisShelley = lib.mkOption {
      type = lib.types.path;
    };

    package = lib.mkOption {
      type = lib.types.package;
      description = "cardano-node package to use";
      default = cardano-node;
    };

    address = lib.mkOption {
      type = lib.types.str;
      description = "Address to serve on";
      default = "0.0.0.0";
    };

    port = lib.mkOption {
      type = lib.types.port;
      description = "Port to serve on";
      default = 3001;
    };

    tracerAddress = lib.mkOption {
      type = lib.types.str;
      description = "Tracer hostname to connect to";
    };

    tracerPort = lib.mkOption {
      type = lib.types.port;
      description = "Tracer port to connect to";
    };

    user = lib.mkOption {
      type = lib.types.str;
      default = "cardano-node";
      description = "User to run cardano-node service as";
    };

    group = lib.mkOption {
      type = lib.types.str;
      default = "cardano-node";
      description = "Group to run cardano-node service as";
    };

    leiosDb = lib.mkOption {
      type = lib.types.path;
      description = "Leios DB";
    };

  };

  config = lib.mkIf cfg.enable {
    users = {
      users = {
        ${cfg.user} = {
          description = "User to run cardano-node service";
          inherit (cfg) group;
          createHome = false;
          isSystemUser = true;
        };
      };

      groups = {
        ${cfg.group} = {
          members = [ cfg.user ];
        };
      };
    };

    networking.firewall.allowedTCPPorts = [ cfg.port ];

    environment.etc = {
      "cardano-node/config.json" = {
        inherit (cfg) user group;
        source = cfg.config;
        mode = "0600"; # NOTE: We're patching this file in `preStart`
      };
      "cardano-node/genesis-alonzo.json" = {
        source = cfg.genesisAlonzo;
      };
      "cardano-node/genesis-conway.json" = {
        source = cfg.genesisConway;
      };
      "cardano-node/genesis-byron.json" = {
        source = cfg.genesisByron;
      };
      "cardano-node/genesis-shelley.json" = {
        source = cfg.genesisShelley;
      };
      "cardano-node/topology.json" = {
        source = cfg.topology;
      };
    };

    environment.variables = {
      CARDANO_NODE_SOCKET_PATH = "/run/${builtins.head config.systemd.services.cardano-node.serviceConfig.RuntimeDirectory}/node.socket";
      CARDANO_NODE_NETWORK_ID = with builtins; (fromJSON (readFile cfg.genesisShelley)).networkMagic;
    };

    systemd.services.cardano-node = {
      enable = true;
      after = [ "network.target" ];
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        Restart = "on-failure";
        RemainAfterExit = true;
        User = cfg.user;
        Group = cfg.group;
        ConfigurationDirectory = [ "cardano-node" ];
        StateDirectory = [ "cardano-node" ];
        RuntimeDirectory = [ "cardano-node" ];
      };

      path = [
        cfg.package
        pkgs.jq
        pkgs.socat
      ];

      preStart = ''
        cat ${cfg.config} | jq ".AlonzoGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-alonzo.json\"" \
          | jq ".ByronGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-byron.json\"" \
          | jq ".ShelleyGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-shelley.json\"" \
          | jq ".ConwayGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-conway.json\"" \
          > "$CONFIGURATION_DIRECTORY/config.json"

        if [ ! -d "$STATE_DIRECTORY/db" ]; then
            echo "cardano-node DB directory $STATE_DIRECTORY/db does not exist. Creating it now."
            mkdir -p "$STATE_DIRECTORY/db"
            cp ${cfg.leiosDb} "$STATE_DIRECTORY/leios.db"
            chmod +rw "$STATE_DIRECTORY/leios.db"
        else
            echo "cardano-node DB directory already exists."
        fi
      '';

      script = ''
        LEIOS_DB_PATH="$STATE_DIRECTORY/leios.db"
        export LEIOS_DB_PATH
        chmod g+rw $RUNTIME_DIRECTORY
        socat UNIX-LISTEN:"$RUNTIME_DIRECTORY/tracer.socket",fork,reuseaddr,unlink-early TCP4:${cfg.tracerAddress}:${builtins.toString cfg.tracerPort} &
        sleep 2

        cardano-node run \
             --start-as-non-producing-node \
             --config "$CONFIGURATION_DIRECTORY/config.json" \
             --topology "$CONFIGURATION_DIRECTORY/topology.json" \
             --database-path "$STATE_DIRECTORY/db" \
             --socket-path "$RUNTIME_DIRECTORY/node.socket" \
             --tracer-socket-path-connect "$RUNTIME_DIRECTORY/tracer.socket" \
             --host-addr ${cfg.address} --port ${builtins.toString cfg.port}
      '';
    };

  };

}
