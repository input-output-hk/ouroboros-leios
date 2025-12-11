{

  perSystem =
    {
      pkgs,
      config,
      ...
    }:
    {
      packages = {

        ss_prom = pkgs.writeShellApplication {
          name = "ss_prom";

          runtimeInputs = [
            pkgs.procps
            pkgs.coreutils
            pkgs.iproute2
          ];

          text = builtins.readFile ./ss_prom.sh;
        };

        ss_http_exporter = pkgs.writeShellApplication {
          name = "ss_http_exporter";

          runtimeInputs = [
            config.packages.http_command
            config.packages.ss_prom
          ];

          text = builtins.readFile ./ss_http_exporter.sh;
        };
      };

      checks = {

        test_ss_to_prometheus = pkgs.stdenv.mkDerivation {
          name = "test_ss_to_prometheus";
          src = ./.;
          buildPhase = ''
            . ${./ss_prom.sh}
            cat ${./test/dport_https_sockets.ss} | ss_to_prometheus > result.prom
            diff result.prom ${./test/dport_https_sockets.prom}
            touch $out
          '';
        };

        test_ss_prom = pkgs.stdenv.mkDerivation {
          name = "test_ss_prom";
          src = ./.;
          buildInputs = [
            config.packages.ss_prom
            pkgs.netcat
            pkgs.gnused
          ];
          buildPhase = ''
            nc -l 1234 &
            sleep 2
            nc -p 1337 127.0.0.1 1234 &
            sleep 2
            ss_prom "dport = 1234" > result.prom
            cat result.prom | grep -v "#" | cut -d " " -f 1 | sed 's/pid="[0-9]*"/pid="XX"/g' > got
            cat ${./test/localhost_1234.prom} | grep -v "#" | cut -d " " -f 1 | sed 's/pid="[0-9]*"/pid="XX"/g' > wanted
            diff wanted got
            mv result.prom $out
          '';
        };

        test_ss_http_exporter = pkgs.stdenv.mkDerivation {
          name = "test_ss_http_exporter";
          src = ./.;
          buildInputs = [
            config.packages.ss_http_exporter
            pkgs.curl
            pkgs.netcat
            pkgs.gnused
          ];
          buildPhase = ''
            nc -l 1234 &
            sleep 2
            nc -p 1337 127.0.0.1 1234 &
            sleep 2
            ss_http_exporter 127.0.0.1 9100 "dport = 1234" &
            sleep 2
            curl 127.0.0.1:9100 > result.prom
            cat result.prom | grep -v "#" | cut -d " " -f 1 | sed 's/pid="[0-9]*"/pid="XX"/g' > got
            cat ${./test/localhost_1234.prom} | grep -v "#" | cut -d " " -f 1 | sed 's/pid="[0-9]*"/pid="XX"/g' > wanted
            diff wanted got
            mv result.prom $out
          '';
        };

      };
    };
}
