{
  pkgs ? import <nixpkgs> { },
}:

let
  hlib = pkgs.haskell.lib.compose;

  hackage =
    self: pkg: ver: sha256:
    hlib.dontCheck (self.callHackageDirect { inherit pkg ver sha256; } { });

  hsPkgs = pkgs.haskell.packages.ghc9103.override {
    overrides = self: super: {
      lsp = hackage self "lsp" "2.8.0.0" "1y4xawk6ssf9205a2zwwsrrpf6am8g4b8a0cgnymrni5lbl827yr";
      lsp-types = hackage self "lsp-types" "2.4.0.0" "1xrwlnj93w9fp73gf2r82zbg94d3hhs9bcy321q1gdryyrc5m2cm";
      lsp-test = hackage self "lsp-test" "0.18.0.0" "1q7a0gjmbw6yzl4cpnxkfyf1jgi1pprl527mcm35ii3pf1gv1qwq";
      hie-bios = hackage self "hie-bios" "0.21.0" "1g5q3s3k0p5jzim0zpbixx82g0q8sd02z1zr3g5h9g54zla167xm";
      hiedb = hackage self "hiedb" "0.8.0.0" "07jh3xzjmswkv9wjffa0bkmmc6v7sxnp39dy1bhvvpxiqh9jvba9";
      hls-graph = hackage self "hls-graph" "2.15.0.0" "029vh9h0yam8152n8dpw24wq4ixr7277sx8i36w709j5f7cwghzf";
      hls-plugin-api = hackage self "hls-plugin-api" "2.15.0.0" "12a1zhqkxp800qb0sqr2y6wmjm3fg1zq0k46s6jyyqpnq8785j7g";
      hls-test-utils = hackage self "hls-test-utils" "2.15.0.0" "0b0wjfgzf6bmn7gvp1ci4p2ncz69jmqina4wzj9qlk6s7p0155ia";

      ghcide = hlib.overrideCabal (drv: {
        postPatch = (drv.postPatch or "") + ''
          sed -i 's/unordered-containers *>=0.2.21/unordered-containers/' ghcide.cabal
        '';
      }) (hackage self "ghcide" "2.15.0.0" "0cv13yr1px32j1xkqilzykkwda7hqlvj1pz051d3kwrlkm10n1mw");

      haskell-language-server = hlib.overrideCabal (drv: {
        version = "2.15.0.0";
        sha256 = "1gzancqji9h5dkr7pkbxpd9lp4d9md1bj1s1abwkzp3bc4rcvw0f";
        revision = null;
        editedCabalFile = null;
        libraryHaskellDepends = drv.libraryHaskellDepends ++ [ self.table-layout ];
        enableLibraryProfiling = false;
        doHaddock = false;
      }) super.haskell-language-server;
    };
  };
in
pkgs.mkShell {
  packages = [
    hsPkgs.ghc
    hsPkgs.haskell-language-server
    pkgs.cabal-install
    pkgs.haskellPackages.cabal-gild
    pkgs.haskellPackages.fourmolu
    pkgs.zlib
    pkgs.pkg-config
  ];
}