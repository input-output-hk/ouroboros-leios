{
  inputs,
  outputs,
  pkgs,
  ...
}:
{
  imports = [
    (import ../services/simple-cardano-relay.nix {
      inherit (inputs.cardano-node.packages."${pkgs.system}") cardano-node;
    })
  ];
  environment.systemPackages = [ inputs.cardano-node.packages."${pkgs.system}".cardano-cli ];
  cardano.relay = {
    enable = true;
    config = ./config.json;
    topology = ./topology.json;
    genesisAlonzo = "${outputs.packages.${pkgs.system}.genesis}/genesis.alonzo.json";
    genesisConway = "${outputs.packages.${pkgs.system}.genesis}/genesis.conway.json";
    genesisShelley = "${outputs.packages.${pkgs.system}.genesis}/genesis.shelley.json";
    genesisByron = "${outputs.packages.${pkgs.system}.genesis}/genesis.byron.json";
    tracerAddress = "tracer-node";
    tracerPort = 8888;
    leiosDb = outputs.packages.${pkgs.system}.leios-empty-db;
  };
}
