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
        geosphere
        ggExtra
        ggpattern
        ggplot2
        ggraph
        # ggtda
        igraph
        ltsa
        lubridate
        mapproj
        maps
        mongolite
        poibin
        quantreg
        R_utils
        ripserr
        RPostgres
        stringr
        svglite
        TDAstats
        VGAM
      ];
  };
}
