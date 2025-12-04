{pkgs, ...}:

let

  # FIXME: Ugly but necessary!
  nixpkgs_version = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/11cb3517b3af6af300dd6c055aeda73c9bf52c48.tar.gz";
    sha256 = "sha256:1915r28xc4znrh2vf4rrjnxldw2imysz819gzhk9qlrkqanmfsxd";
  };
  rPackages = (import nixpkgs_version {system = "x86_64-linux";}).rPackages;

in

{
  kernel.python.minimal = {
    enable = true;
    extraPackages = p: with p; [
      numpy
      pandas
    ];
  };
  kernel.r.minimal = {
    enable = true;
    extraRPackages = p: with p; [
      bit64
      cowplot
      curl
      data_table
      dplyr
      ggpattern
      ggplot2
      ggExtra
      igraph
      ltsa
      lubridate
      mongolite
      poibin
      quantreg
      RPostgres
      R_utils
      stringr
      svglite
      VGAM
    ];
  };
}
