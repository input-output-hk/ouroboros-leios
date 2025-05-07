{pkgs, ...}: {
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
      curl
      data_table
      dplyr
      ggpattern
      ggplot2
      ggExtra
      lubridate
      mongolite
      RPostgres
      R_utils
      stringr
      svglite
    ];
  };
}
