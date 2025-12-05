{
  immdb-server,
  outputs,
  pkgs,
  ...
}:
{
  imports = [
    (import ../services/immdb-server.nix { inherit immdb-server; })
  ];

  environment.systemPackages = [ pkgs.sqlite ];

  cardano.immdb-server = {
    enable = true;
    config = ./config.json;
    genesisAlonzo = "${outputs.packages.${pkgs.system}.genesis}/genesis.alonzo.json";
    genesisConway = "${outputs.packages.${pkgs.system}.genesis}/genesis.conway.json";
    genesisShelley = "${outputs.packages.${pkgs.system}.genesis}/genesis.shelley.json";
    genesisByron = "${outputs.packages.${pkgs.system}.genesis}/genesis.byron.json";
    initialSlot = 500;
    db = outputs.packages.${pkgs.system}.immutable-db;
    leiosSchedule = outputs.packages.${pkgs.system}.leios-busy-db.schedule;
    leiosDb = outputs.packages.${pkgs.system}.leios-busy-db;
  };
}
