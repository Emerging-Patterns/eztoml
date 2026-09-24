{
  description = "eztoml: TOML for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      version = "0.2.2"; # x-release-please-version
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
