{
  description = "eztoml: TOML for Bend 2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # bendlang/bend's flake at the commit that packages 2.0.38 (the v2.0.38 tag
  # may still package 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };
  # Interim: ez 1.5.0 does not build on 2.0.38 yet, so ez (and the bolt it
  # builds for mkLint) stays on the bend its own flake.lock records (2.0.36).
  # The tooling pass puts `inputs.bend.follows = "bend"` and ez.mkProofs back
  # once ez releases on 2.0.38.
  inputs.ez = {
    url = "github:Emerging-Patterns/ez";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.bend.url = "github:bendlang/bend/eebc18cd04daeade06c3f68c3c96c1faefd3462f";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      version = "0.9.0"; # x-release-please-version
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
        # every PROOF.bend must print ALL PROOFS CHECK on the flake's bend
        # (2.0.38); interim stand-in for ez.mkProofs, whose ez runs on 2.0.36
        proofs = pkgs.runCommand "eztoml-proofs" {
          nativeBuildInputs = [ bend ];
          BEND_LIB = ez.bendLib ./ez.lock.toml;
        } ''
          export HOME=$TMPDIR
          cp -r ${self} src && chmod -R u+w src && cd src
          for p in $(find . -name PROOF.bend -not -path './.ez/*' | sort); do
            first=$(cd "$(dirname "$p")" && bend "$(basename "$p")" | head -n 1)
            echo "$p: $first"
            [ "$first" = "ALL PROOFS CHECK" ] || exit 1
          done
          touch $out
        '';
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
