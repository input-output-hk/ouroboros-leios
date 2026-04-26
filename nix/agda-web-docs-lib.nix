{
  pkgs,
  lib,
  ...
}:

pkgs.buildNpmPackage {
  pname = "agda-web-docs-lib";
  version = "1.0.8";

  src = pkgs.fetchFromGitHub {
    owner = "will-break-it";
    repo = "agda-web-docs-lib";
    rev = "v1.0.8";
    hash = "sha256-mTUzYz6ET+bmJ9K6ZbZuFMtkpJDIGkytA8wXgvnp9Xk=";
  };

  npmDepsHash = "sha256-SObPqlkvsAFfByWj+h8CPfSIBrlGofaObqslGyJtsMM=";

  # Patch copyFileSync calls to chmod the destination writable afterwards.
  # Without this, files copied from the nix store inherit read-only permissions
  # and subsequent overwrites fail.
  postPatch = ''
    substituteInPlace src/cli.ts \
      --replace-fail \
        'fs.copyFileSync(sourcePath, destPath);' \
        'fs.copyFileSync(sourcePath, destPath); fs.chmodSync(destPath, 0o644);' \
      --replace-fail \
        "fs.copyFileSync(searchScriptPath, path.join(outputDir, 'search.js'));" \
        "fs.copyFileSync(searchScriptPath, path.join(outputDir, 'search.js')); fs.chmodSync(path.join(outputDir, 'search.js'), 0o644);"
  '';

  # The build script: tsc && cp -r src/styles dist/ && cp -r src/scripts dist/
  buildPhase = ''
    npm run build
  '';

  # Install the CLI and its runtime dependencies
  dontNpmInstall = true;

  installPhase = ''
    mkdir -p $out/lib/node_modules/agda-web-docs-lib
    cp -r dist $out/lib/node_modules/agda-web-docs-lib/
    cp -r node_modules $out/lib/node_modules/agda-web-docs-lib/
    cp package.json $out/lib/node_modules/agda-web-docs-lib/

    mkdir -p $out/bin
    ln -s $out/lib/node_modules/agda-web-docs-lib/dist/cli.js $out/bin/agda-docs
  '';

  meta = {
    description = "Library for enhancing Agda-generated HTML documentation with interactive features";
    homepage = "https://github.com/will-break-it/agda-web-docs-lib";
    license = lib.licenses.mit;
    mainProgram = "agda-docs";
  };
}
