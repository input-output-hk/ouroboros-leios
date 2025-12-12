# NOTE(bladyjoker): Sadly needed because the repo contains files and directories that are invalid Nix Store path names
# TODO(bladyjoker): If the repo adjusts the naming scheme one can simply use lib.filesystem.listFilesRecursive
{
  lib,
  toInclude,
  dir,
}:
let
  # Regex for characters allowed in Nix store paths:
  # Alphanumeric, dots (.), underscores (_), plus (+), and hyphens (-)
  isValidName = name: builtins.match "[a-zA-Z0-9._+-]+" name != null;

  internalFunc =
    dir:
    (lib.mapAttrsToList (
      name: type:
      if isValidName name then
        if type == "directory" then
          internalFunc (dir + "/${name}")
        else if toInclude name then
          [ (dir + "/${name}") ]
        else
          [ ]
      else
        [ ]
    ) (builtins.readDir dir));
in
lib.flatten (internalFunc dir)
