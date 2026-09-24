# Rust toml crate vs eztoml bench: native Bend driver + Rust ref + Nix-embedded
# compare script. No checked-in *.py — compare text lives in compare.nix.
#
# Fairness: both sides time N iterations in-process (Bend IO.now / Rust Instant)
# on in-memory TOML. Reference is the `toml` crate (decode+encode), never a
# TOML CLI and never Python tomllib. Timing is not part of the flake check.
{
  pkgs,
  lib,
  bend,
  bend-cc,
  # Flake `self` (repo root). Used only to copy main.bend + bench sources.
  self,
}:

let
  llvm = pkgs.llvmPackages_19;

  # Sandbox-safe CC: nixpkgs clang (native ELF). Local `nix develop` still
  # exports CC=bend-cc for host-ld native builds; both are non-JS.
  drv = pkgs.stdenv.mkDerivation {
    pname = "eztoml-bench-drv";
    version = "0.1.0";
    dontUnpack = true;
    nativeBuildInputs = [ bend llvm.clang ];
    buildPhase = ''
      cp ${self}/main.bend ./main.bend
      mkdir -p bench
      cp ${./main.bend} bench/main.bend
      cd bench
      export CC=${llvm.clang}/bin/clang
      export BEND_NO_TELEMETRY=1
      bend main.bend -o eztoml-bench
    '';
    installPhase = ''
      mkdir -p $out/bin
      cp eztoml-bench $out/bin/eztoml-bench
    '';
    meta = {
      description = "Native ELF driver for eztoml vs Rust toml benches";
      mainProgram = "eztoml-bench";
    };
  };

  rustRef = pkgs.rustPlatform.buildRustPackage {
    pname = "eztoml-rust-ref";
    version = "0.1.0";
    src = ./ref;
    cargoLock.lockFile = ./ref/Cargo.lock;
    meta = {
      description = "In-process Rust toml crate reference for eztoml benches";
      mainProgram = "eztoml-rust-ref";
    };
  };

  compareText = import ./compare.nix {
    drvBin = "eztoml-bench";
    refBin = "eztoml-rust-ref";
  };
  comparePy = pkgs.writeText "eztoml-wave-compare.py" compareText;

  py = pkgs.python3;

  makeRunner = mode: pkgs.writeShellApplication {
    name = if mode == "correctness" then "eztoml-wave-check" else "eztoml-wave-bench";
    runtimeInputs = [ drv rustRef py ];
    text = ''
      set -euo pipefail
      export EZTOML_BENCH_DRV=${drv}/bin/eztoml-bench
      export EZTOML_BENCH_REF=${rustRef}/bin/eztoml-rust-ref
      export EZTOML_BENCH_WORK="''${EZTOML_BENCH_WORK:-$(mktemp -d)}"
      export EZTOML_BENCH_MODE=${mode}
      mkdir -p "$EZTOML_BENCH_WORK"
      exec ${py}/bin/python ${comparePy} "$@"
    '';
  };

  checkBin = makeRunner "correctness";
  benchBin = makeRunner "all";

  # Flake check: correctness must pass. Timing is not part of this derivation.
  waveCheck = pkgs.runCommand "eztoml-wave-compare" {
    nativeBuildInputs = [ checkBin ];
  } ''
    export EZTOML_BENCH_WORK="$PWD/work"
    mkdir -p "$EZTOML_BENCH_WORK"
    eztoml-wave-check | tee $out
  '';
in
{
  inherit drv rustRef waveCheck;
  packages = {
    eztoml-bench-drv = drv;
    eztoml-rust-ref = rustRef;
    eztoml-wave-check = checkBin;
    eztoml-wave-bench = benchBin;
  };
  apps = {
    wave-check = {
      type = "app";
      program = "${checkBin}/bin/eztoml-wave-check";
    };
    wave-bench = {
      type = "app";
      program = "${benchBin}/bin/eztoml-wave-bench";
    };
  };
  checks = {
    wave = waveCheck;
  };
}
