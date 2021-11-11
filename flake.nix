{
  description = "lh-playground";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-21.05;
    flake-utils.url = github:numtide/flake-utils;
    liquidhaskell.url = github:plredmond/liquidhaskell/nix-flake;
    liquidhaskell.inputs.nixpkgs.follows = "nixpkgs";
    liquidhaskell.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, liquidhaskell }: flake-utils.lib.eachDefaultSystem (system: {
    devShell = self.defaultPackage.${system}.env;
    defaultPackage =
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ liquidhaskell.overlay.${system} ];
        };
        # ghc version is coupled to the ghc version in the liquidhaskell flake,
        # because that flake overrides the haskell package set for only ony
        # compiler
        ghc = "ghc8104";
        src = pkgs.nix-gitignore.gitignoreSource [ "*.nix" "result" "build-env" "*.cabal" "deploy/" ] ./.;
        drv = pkgs.haskell.packages.${ghc}.callCabal2nix "lh-playground" src { };
      in
      pkgs.haskell.lib.overrideCabal drv (old: {
        # enableLibraryProfiling is coupled to the value in the
        # liquidhaskell flake
        enableLibraryProfiling = false;
        buildTools = old.buildTools or [ ] ++ [ pkgs.z3 ];
      });
  });
}
