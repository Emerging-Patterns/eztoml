{
  description = "eztoml: TOML for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.35 (the v2.0.35 tag
  # still packages 2.0.34)
  inputs.bend = {
    url = "github:bendlang/bend/5a0b523f7759335164f1dead0e0815234a5fd9dc";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # ez (and the bolt it builds) follows this bend
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      version = "0.8.0"; # x-release-please-version
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      ez = inputs.ez.lib.${system};
      ezBin = inputs.ez.packages.${system}.default;
      bend = inputs.bend.packages.${system}.default;
      bend-cc = ez.bend-cc;
      demo = ez.mkPackage {
        inherit bend;
        src = self;
        pname = "demo";
        entry = "examples/demo/main.bend";
      };

      bench = import ./bench {
        inherit pkgs bend bend-cc self;
        lib = pkgs.lib;
      };
    in {
      packages.${system} = {
        inherit bend demo bend-cc;
        ez = ezBin;
        default = demo;
      } // bench.packages;

      apps.${system} = bench.apps;

      checks.${system} = {
        inherit demo;
        # every PROOF.bend must print ALL PROOFS CHECK (ez prove)
        proofs = ez.mkProofs { ez = ezBin; src = self; };
        # bolt at the `[tools.bolt]` pin in ez.lock.toml, graded by ./bolt.bend
        lint = ez.mkLint { src = self; };
      } // bench.checks;

      # `src` puts every locked `[tools.*]` (bolt) on PATH
      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [
          bend
          bend-cc
          ezBin
          pkgs.python3
          pkgs.cargo
          pkgs.rustc
          bench.packages.eztoml-bench-drv
          bench.packages.eztoml-rust-ref
          bench.packages.eztoml-wave-check
          bench.packages.eztoml-wave-bench
        ];
      };
    };
}
