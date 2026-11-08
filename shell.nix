{
  pkgs ? import <nixpkgs> { },
}:

let
  hsPkgs = pkgs.haskell.packages.ghc912;
in
pkgs.mkShell {
  packages = [
    hsPkgs.ghc
    (pkgs.haskell-language-server.override { supportedGhcVersions = [ "912" ]; })
    pkgs.cabal-install
    pkgs.haskellPackages.cabal-gild
    pkgs.haskellPackages.fourmolu
    pkgs.haskellPackages.hlint
    pkgs.zlib
    pkgs.pkg-config
  ];
}
