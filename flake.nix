{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self, nixpkgs, lean4-nix }:
    let
      system = "x86_64-linux";
      lean4-nix-path = lean4-nix.sourceInfo.outPath;
      rc2Manifest = {
        tag = "v4.30.0-rc2";
        rev = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
        toolchain.x86_64-linux = {
          url = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux.tar.zst";
          hash = "sha256-o47cQjSLK5YL8YZ2raaj+mGAvvO+dIDfVeP2L+WoyMs=";
        };
        bootstrap = (import "${lean4-nix-path}/manifests/v4.29.0.nix").bootstrap;
        buildLeanPackage = (import "${lean4-nix-path}/manifests/v4.29.0.nix").buildLeanPackage;
      };
      leanOverlay = final: prev: {
        lean = (final.callPackage "${lean4-nix-path}/lib/toolchain.nix" { }).fetchBinaryLean rc2Manifest;
      };
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ leanOverlay ];
      };
      lake2nix = pkgs.callPackage lean4-nix.lake { };
      deps = lake2nix.buildDeps { src = ./compiler; };
    in
    {
      packages.${system} = {
        somac = lake2nix.mkPackage {
          name = "somac";
          src = ./compiler;
          lakeDeps = deps;
        };
        default = self.packages.${system}.somac;
      };
    };
}
