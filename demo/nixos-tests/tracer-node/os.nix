{
  inputs,
  pkgs,
  ...
}:
{
  imports = [
    (import ../services/simple-cardano-tracer.nix {
      inherit (inputs.cardano-node.packages."${pkgs.system}") cardano-tracer;
    })
  ];

  environment.systemPackages = [ ];

  cardano.tracer = {
    enable = true;
    config = ./config.json;
    address = "0.0.0.0";
    port = 8888;
    prometheusAddress = "0.0.0.0";
    prometheusPort = 3000;
  };
}
