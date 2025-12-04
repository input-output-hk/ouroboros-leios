{
  kernel.python.minimal = {
    enable = true;
    extraPackages =
      p: with p; [
        numpy
        pandas
      ];
  };
  kernel.r.minimal = {
    enable = true;
    extraRPackages =
      p: with p; [
        bit64
        cowplot
        curl
        data_table
        dplyr
        ggpattern
        ggplot2
        ggExtra
        igraph
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
