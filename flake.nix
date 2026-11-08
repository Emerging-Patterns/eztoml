{
  description = "eztoml: TOML for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.40 (the v2.0.40 tag
  # may still package 2.0.39)
  inputs.bend = {
    url = "github:bendlang/bend/222de9901d4e3551c2b347da02e02a10098a28b2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.follows = "bend";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      version = "0.10.0"; # x-release-please-version
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEach = nixpkgs.lib.genAttrs systems;
      outputsFor = system:
        let
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
          packages = {
            inherit bend demo bend-cc;
            ez = ezBin;
            default = demo;
          } // bench.packages;

          apps = bench.apps;

          checks = {
            inherit demo;
            # every PROOF.bend must print ALL PROOFS CHECK (ez prove, on 2.0.40)
            proofs = ez.mkProofs { ez = ezBin; src = self; };
            # bolt at the `[tools.bolt]` pin in ez.lock.toml, graded by ./bolt.bend
            lint = ez.mkLint { src = self; };
          } // bench.checks;

          # `src` puts every locked `[tools.*]` (bolt) on PATH
          devShells.default = ez.mkShell {
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
      perSystem = forEach outputsFor;
      each = name: forEach (system: perSystem.${system}.${name});
    in {
      packages = each "packages";
      checks = each "checks";
      apps = each "apps";
      devShells = each "devShells";
    };
}
