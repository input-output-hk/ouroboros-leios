{

  perSystem =
    {
      pkgs,
      config,
      ...
    }:
    {
      packages = {
        http_command_on_request = pkgs.writeShellApplication {
          name = "on_request";
          text = builtins.readFile ./on_request.sh;
        };

        http_command = pkgs.writeShellApplication {
          name = "http_command";
          runtimeInputs = [
            pkgs.socat
            config.packages.http_command_on_request
          ];
          text = builtins.readFile ./server.sh;
        };
      };

      checks.test_http_command = pkgs.stdenv.mkDerivation {
        name = "test_http_command";
        src = ./.;
        buildInputs = [
          pkgs.curl
          config.packages.http_command
        ];
        buildPhase = ''
          touch $out
          before=$(ls)
          http_command 127.0.0.1 1337 "ls" &
          sleep 5
          after=$(curl 127.0.0.1:1337)
          if [[ "$before" != "$after" ]]; then
              echo "Before and after should match"
              echo before: $before
              echo after: $after
              exit 1
          fi
        '';
      };
    };
}
