{ immdb-server, ... }:
{
  config,
  lib,
  pkgs,
  ...
}:
let
  cfg = config.cardano.immdb-server;
in
{

  imports = [
  ];

  options.cardano.immdb-server = {
    enable = lib.mkEnableOption ''Run ourborous-consensus's immdb-server as a service'';

    db = lib.mkOption {
      type = lib.types.path;
      description = "Path to the ImmutableDB";
    };

    config = lib.mkOption {
      type = lib.types.path;
      description = "Path to config file, in the same format as for the node or db-analyser";
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

    initialSlot = lib.mkOption {
      type = lib.types.int;
      description = "Reference slot number (SlotNo). This, together with the initial-time will be used for time translations";
      default = 0;
    };

    initialTime = lib.mkOption {
      type = lib.types.nullOr lib.types.int;
      description = "UTC time for the reference slot, provided as POSIX seconds (Unix timestamp)";
      default = null;
    };

    leiosSchedule = lib.mkOption {
      type = lib.types.path;
      description = "Leios schedule JSON file";
    };

    leiosDb = lib.mkOption {
      type = lib.types.path;
      description = "Leios DB";
    };

    user = lib.mkOption {
      type = lib.types.str;
      default = "immdb-server";
      description = ''User to run immdb-server service as'';
    };

    group = lib.mkOption {
      type = lib.types.str;
      default = "immdb-server";
      description = ''Group to run immdb-server service as'';
    };

  };

  config = lib.mkIf cfg.enable {
    users = {
      users = {
        ${cfg.user} = {
          description = "User to run immdb-server service";
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
      "immdb-server/config.json" = {
        inherit (cfg) user group;
        source = cfg.config;
        mode = "0600"; # NOTE: We're patching this file in `preStart`
      };
      "immdb-server/genesis-alonzo.json" = {
        inherit (cfg) user group;
        source = cfg.genesisAlonzo;
      };
      "immdb-server/genesis-conway.json" = {
        inherit (cfg) user group;
        source = cfg.genesisConway;
      };
      "immdb-server/genesis-byron.json" = {
        inherit (cfg) user group;
        source = cfg.genesisByron;
      };
      "immdb-server/genesis-shelley.json" = {
        inherit (cfg) user group;
        source = cfg.genesisShelley;
      };

    };

    systemd.services.immdb-server = {
      enable = true;
      after = [ "network.target" ];
      wantedBy = [ "multi-user.target" ];
      serviceConfig = {
        Restart = "on-failure";
        RemainAfterExit = true;
        User = "immdb-server";
        Group = "immdb-server";
        ConfigurationDirectory = [ "immdb-server" ];
        StateDirectory = [ "immdb-server" ];
      };

      path = [
        immdb-server
        pkgs.jq
      ];

      preStart = ''
        cat ${cfg.config} | jq ".AlonzoGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-alonzo.json\"" \
          | jq ".ByronGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-byron.json\"" \
          | jq ".ShelleyGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-shelley.json\"" \
          | jq ".ConwayGenesisFile = \"$CONFIGURATION_DIRECTORY/genesis-conway.json\"" \
          > "$CONFIGURATION_DIRECTORY/config.json"

        if [ ! -d "$STATE_DIRECTORY/immutable" ]; then
            echo "immdb-server DB directory $STATE_DIRECTORY/immutable does not exist. Creating it now."
            mkdir -p "$STATE_DIRECTORY/immutable";
            cp -r ${cfg.db}/* "$STATE_DIRECTORY/immutable";
            chmod +rw $STATE_DIRECTORY/immutable/*;
            cp ${cfg.leiosSchedule} "$STATE_DIRECTORY/schedule.json"
            cp ${cfg.leiosDb} "$STATE_DIRECTORY/leios.db"
        else
            echo "immdb-server DB directory already exists."
        fi
      '';

      script = ''
        echo "Starting Immutable DB server with ${builtins.toJSON cfg}";

        immdb-server \
          --db "$STATE_DIRECTORY/immutable" \
          --config "$CONFIGURATION_DIRECTORY/config.json" \
          --address ${cfg.address} \
          --port ${builtins.toString cfg.port} \
          --initial-slot ${builtins.toString cfg.initialSlot} \
          --initial-time ${
            if cfg.initialTime == null then "$(date +%s)" else builtins.toString cfg.initialTime
          } \
          --leios-schedule "$STATE_DIRECTORY/schedule.json" \
          --leios-db "$STATE_DIRECTORY/leios.db";
      '';
    };

  };

}
