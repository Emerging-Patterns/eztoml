# eztoml vs Rust toml-crate compare script text (embedded; not a checked-in .py).
# Consumed by writeText / writeShellApplication in default.nix.
#
# Fairness / what the numbers mean:
# - Decode speed: eztoml parse (in-memory, bytes preloaded) vs Rust toml::from_str
#   timed for N iterations *inside* the Rust binary. No per-op process spawn.
# - Encode speed: eztoml render (doc loaded+parsed outside IO.now) vs Rust
#   toml::to_string timed for N iterations inside the Rust binary.
# - Reference is never a TOML CLI, never Python tomllib, never subprocess-per-op.
# - Speed fixtures are product-shaped multi-KB configs (tables, arrays of tables,
#   nested keys, strings/datetimes/floats). LAWS edge cases stay in correctness.
# - IO.now is 1 ms. If MS is 0, N is raised; if still unresolved, wall/n is
#   reported honestly without claiming a vs-Rust ratio.
# - ratio = eztoml_ms / rust_ms (>1 ⇒ eztoml slower).
{ drvBin ? "eztoml-bench", refBin ? "eztoml-rust-ref" }:
''
import os, subprocess, sys, time, traceback

DRV = os.environ.get("EZTOML_BENCH_DRV", "${drvBin}")
REF = os.environ.get("EZTOML_BENCH_REF", "${refBin}")
WORK = os.environ.get("EZTOML_BENCH_WORK", os.path.join(os.environ.get("TMPDIR", "/tmp"), "eztoml-bench-work"))
MODE = os.environ.get("EZTOML_BENCH_MODE", "correctness")  # correctness | speed | all
os.makedirs(WORK, exist_ok=True)

lines, cases, speed_rows = [], [], []
fails = 0

def log(msg=""):
    print(msg, flush=True)
    lines.append(msg)

def run(bin, args, timeout):
    t0 = time.perf_counter()
    try:
        r = subprocess.run([bin, *args], capture_output=True, timeout=timeout)
        return {"rc": r.returncode, "out": r.stdout.decode("utf-8", "replace"),
                "err": r.stderr.decode("utf-8", "replace"), "wall": time.perf_counter() - t0,
                "timeout": False}
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""; err = e.stderr or b""
        if isinstance(out, str): out = out.encode()
        if isinstance(err, str): err = err.encode()
        return {"rc": None, "out": out.decode("utf-8", "replace"),
                "err": err.decode("utf-8", "replace"),
                "wall": time.perf_counter() - t0, "timeout": True}

def ez(args, timeout=60):
    return run(DRV, args, timeout)

def rust(args, timeout=60):
    return run(REF, args, timeout)

def parse_bench(out):
    parts = out.split()
    if len(parts) < 8 or parts[0] != "MS":
        return None
    d = {}
    i = 0
    while i + 1 < len(parts):
        d[parts[i]] = int(parts[i + 1]) if parts[i + 1].lstrip("-").isdigit() else parts[i + 1]
        i += 2
    return d

def add_case(group, name, status, detail, hard=True):
    global fails
    cases.append({"group": group, "name": name, "status": status, "detail": detail, "hard": hard})
    log(f"[{status}] {group} | {name}")
    log(f"    {detail}")
    if hard and status != "PASS":
        fails += 1

def write_fix(name, text):
    path = os.path.join(WORK, name)
    open(path, "w", encoding="utf-8").write(text)
    return path

# --- TOML v1.0.0 fixtures (correctness cites toml.io/en/v1.0.0 / toml.abnf) ---

# Closed equalities mirrored from eztoml/LAWS.bend where possible.
VALID_LAWS = [
    ("toml_comment", '# comment\nkey = "v"\n'),
    ("toml_bool", "a = true\nb = false\n"),
    ("toml_string_basic", 's = "A\\nB\\tC\\"D\\\\E"\n'),
    ("toml_string_literal", "s = 'A\\\\nB'\n"),
    ("toml_integer", "a = +99\nb = 42\nc = 0\nd = -17\ne = 1_000\n"),
    ("toml_integer_hex", "a = 0x10\nb = 0o10\nc = 0b10\n"),
    ("toml_float", "a = +1.0\nb = -0.01\nc = 5e+22\nd = 6.626e-34\n"),
    ("toml_float_special", "a = inf\nb = -inf\nc = nan\n"),
    ("toml_table", '[pkg]\nname = "eztoml"\n'),
    ("toml_dotted", "a.b = 1\nfruit.name = \"banana\"\n"),
    ("toml_inline", "p = { x = 1, y = 2 }\nanimal = { type.name = \"pug\" }\n"),
    ("toml_array", "a = [1, 2,]\nb = []\nc = [[1], [2, 3]]\n"),
    ("toml_aot", '[[fruit]]\nname = "apple"\n\n[[fruit]]\nname = "banana"\n'),
    ("toml_datetime", "a = 1979-05-27T07:32:00Z\nb = 1979-05-27T00:32:00-07:00\nc = 1979-05-27\nd = 07:32:00\n"),
    ("toml_keyval", 'first = "Tom"\nlast = "Preston-Werner"\n'),
    ("toml_quoted_key", '"127.0.0.1" = "value"\n\'key2\' = "value"\n'),
]

# Rejected by TOML v1.0.0 / LAWS (eztoml must surface a non-empty bad).
INVALID_LAWS = [
    ("true_capital", "a = True\n"),
    ("leading_zero", "a = 01\n"),
    ("bad_escape", 's = "\\q"\n'),
    ("inline_trailing_comma", "p = { x = 1, }\n"),
    ("inline_newline", "p = { x = 1\n}\n"),
    ("duplicate_key", 'name = "a"\nname = "b"\n'),
    ("duplicate_table", "[fruit]\na = 1\n\n[fruit]\nb = 2\n"),
    ("aot_then_table", "[[fruit]]\nn = 1\n\n[fruit]\nx = 2\n"),
    ("empty_keyval", 'key =\n'),
    ("two_pairs_one_line", 'first = "Tom" last = "Preston-Werner"\n'),
    ("i64_overflow", "a = 9223372036854775808\n"),
]

def package_manifest(n_deps=40):
    # Product-shaped Cargo/app-style manifest: nested tables, arrays of tables,
    # strings, floats, datetimes — multi-KB, not empty / [a]\\nb=1.
    lines = [
        'name = "wavebench"',
        'version = "1.4.2"',
        "edition = 2021",
        "publish = false",
        "authors = [" + ", ".join(f'"author-{i}@example.com"' for i in range(8)) + "]",
        "",
        "[package.metadata.release]",
        "sign-commit = true",
        'pre-release-commit-message = "chore: release v{{version}}"',
        "rate = 0.0125",
        'shipped = 2024-06-15T18:30:00Z',
        "",
        "[dependencies]",
    ]
    for i in range(n_deps):
        opt = "true" if (i % 2 == 0) else "false"
        lines.append(
            f'dep-{i:02d} = {{ version = "={i}.{i % 10}.{i % 7}", '
            f'optional = {opt}, features = ["a", "b-{i}"] }}'
        )
    lines += [
        "",
        "[features]",
        'default = ["std", "serde"]',
        'std = []',
        'serde = ["dep-00"]',
        "",
        "[profile.release]",
        "lto = true",
        "codegen-units = 1",
        "opt-level = 3",
        "panic = \"abort\"",
        "",
    ]
    for i in range(12):
        lines += [
            "[[bin]]",
            f'name = "tool-{i:02d}"',
            f'path = "src/bin/tool_{i:02d}.rs"',
            f"required-features = [\"std\"]",
            "",
        ]
    for i in range(6):
        lines += [
            f"[target.'cfg(target_os = \"linux\")'.dependencies.os-dep-{i}]",
            f'version = "1.{i}.0"',
            "default-features = false",
            "",
        ]
    # Nested workspace-ish tables + mixed scalars
    lines += [
        "[workspace.package]",
        'license = "MIT"',
        'repository = "https://example.com/wavebench"',
        "",
        "[workspace.dependencies]",
        'shared = { path = "../shared", version = "0.1.0" }',
        "",
        "[[workspace.members]]",
        'path = "crates/core"',
        "",
        "[[workspace.members]]",
        'path = "crates/cli"',
        "",
    ]
    return "\n".join(lines) + "\n"

def app_config():
    # App/runtime config: deep nesting, AoT servers, mixed types.
    servers = []
    for i in range(20):
        servers.append(
            f'[[servers]]\n'
            f'name = "svc-{i:02d}"\n'
            f'host = "10.0.{i//256}.{i%256}"\n'
            f"port = {8000+i}\n"
            f"weight = {0.5 + (i%10)*0.05}\n"
            f"enabled = {str(i%3!=0).lower()}\n"
            f'started = 2023-{(i%12)+1:02d}-{(i%28)+1:02d}T12:00:00Z\n'
            f'tags = ["prod", "tier-{i%4}", "az-{(i%3)+1}"]\n'
            f"[servers.tls]\n"
            f'cert = "/etc/certs/svc-{i:02d}.pem"\n'
            f"alpn = [\"h2\", \"http/1.1\"]\n"
        )
    head = (
        "[app]\n"
        'name = "wave-gateway"\n'
        'env = "production"\n'
        "workers = 16\n"
        "timeout_ms = 2500\n"
        "ratio = 0.875\n"
        'boot = 2022-01-01T00:00:00Z\n'
        "\n"
        "[app.logging]\n"
        'level = "info"\n"
        'format = "json"\n'
        "\n"
        "[app.logging.targets.stdout]\n"
        "enabled = true\n"
        "\n"
        "[database]\n"
        'url = "postgres://user:pass@db.internal:5432/app"\n'
        "pool = 32\n"
        "\n"
        "[database.read_replicas]\n"
        'hosts = ["r1.internal", "r2.internal", "r3.internal"]\n'
        "\n"
    )
    return head + "\n".join(servers)

def cargo_lockish(n=80):
    # Lockfile-shaped: many [[package]] AoT entries with nested tables.
    chunks = ['# This file is automatically @generated.\nversion = 3\n']
    for i in range(n):
        chunks.append(
            f"[[package]]\n"
            f'name = "crate-{i:03d}"\n'
            f'version = "1.{i%20}.{i%7}"\n'
            f'source = "registry+https://github.com/rust-lang/crates.io-index"\n'
            f'checksum = "{"a"*64}"\n'
            f"dependencies = [\n"
            f'  "crate-{(i+1)%n:03d}",\n'
            f'  "crate-{(i+7)%n:03d} 2.0",\n'
            f"]\n"
        )
    return "\n".join(chunks)

SPEED_FIXTURES = [
    ("pkg-manifest-sm", package_manifest(20)),
    ("pkg-manifest-md", package_manifest(40)),
    ("pkg-manifest-lg", package_manifest(80)),
    ("app-config", app_config()),
    ("lockfile-shaped", cargo_lockish(80)),
]

def correct_laws():
    log("\n== Correctness (TOML v1.0.0 / toml.abnf; LAWS-shaped) ==")
    log("Cite: https://toml.io/en/v1.0.0 — valid docs parse; invalid docs reject.")
    for name, text in VALID_LAWS:
        path = write_fix("ok_" + name + ".toml", text)
        # A: Rust reference accepts
        rr = rust(["parse", path], 30)
        rust_ok = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("OK")
        add_case("A rust parse", name, "PASS" if rust_ok else "FAIL",
                 f"rc={rr['rc']} out={rr['out'][:120]!r} err={rr['err'][:80]!r}")

        # B: eztoml accepts (BAD empty → OK line)
        er = ez(["parse", path], 60)
        ez_ok = (not er["timeout"]) and er["rc"] == 0 and er["out"].startswith("OK")
        add_case("B eztoml parse", name, "PASS" if ez_ok else "FAIL",
                 f"rc={er['rc']} out={er['out'][:120]!r} err={er['err'][:80]!r}")

        # C: eztoml round-trip → Rust re-parse
        dst = path + ".rt.toml"
        rt = ez(["rt", path, dst], 60)
        if rt["timeout"] or rt["rc"] != 0 or not os.path.exists(dst):
            add_case("C eztoml→rust rt", name, "FAIL", f"rt rc={rt['rc']} err={rt['err'][:120]}")
        else:
            rp = rust(["parse", dst], 30)
            ok = (not rp["timeout"]) and rp["rc"] == 0 and rp["out"].startswith("OK")
            add_case("C eztoml→rust rt", name, "PASS" if ok else "FAIL",
                     f"rendered {os.path.getsize(dst)}B → rust {rp['out'][:100]!r}")

    for name, text in INVALID_LAWS:
        path = write_fix("bad_" + name + ".toml", text)
        er = ez(["parse", path], 60)
        # eztoml must report BAD (non-empty why) on the OK/BAD line, or die.
        out = er["out"].strip()
        ez_reject = (not er["timeout"]) and (
            out.startswith("BAD ") and len(out) > 4
            or er["rc"] not in (0, None) and "BAD" not in out  # die path also OK
            or out.startswith("BAD")
        )
        # Prefer explicit BAD line from parse command
        ez_reject = (not er["timeout"]) and er["rc"] == 0 and out.startswith("BAD ") and len(out) > 4
        add_case("D eztoml reject", name, "PASS" if ez_reject else "FAIL",
                 f"rc={er['rc']} out={out[:140]!r}")

        rr = rust(["parse", path], 30)
        rust_reject = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("ERR")
        add_case("D rust reject", name, "PASS" if rust_reject else "FAIL",
                 f"rc={rr['rc']} out={rr['out'][:140]!r}",
                 hard=True)

def correct_product():
    log("\n== Correctness (product-shaped fixtures) ==")
    for name, text in SPEED_FIXTURES:
        path = write_fix("prod_" + name + ".toml", text)
        rr = rust(["parse", path], 60)
        rust_ok = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("OK")
        add_case("E rust product", name, "PASS" if rust_ok else "FAIL",
                 f"bytes={len(text)} out={rr['out'][:100]!r}")
        er = ez(["parse", path], 120)
        ez_ok = (not er["timeout"]) and er["rc"] == 0 and er["out"].startswith("OK")
        add_case("E eztoml product", name, "PASS" if ez_ok else "FAIL",
                 f"bytes={len(text)} out={er['out'][:100]!r}")
        dst = path + ".rt.toml"
        rt = ez(["rt", path, dst], 120)
        if rt["timeout"] or rt["rc"] != 0 or not os.path.exists(dst):
            add_case("E eztoml product rt", name, "FAIL", f"rc={rt['rc']}")
        else:
            rp = rust(["parse", dst], 60)
            ok = (not rp["timeout"]) and rp["rc"] == 0 and rp["out"].startswith("OK")
            add_case("E eztoml product rt→rust", name, "PASS" if ok else "FAIL",
                     f"rt {os.path.getsize(dst)}B → {rp['out'][:100]!r}")

def ms_per(parsed, wall, n):
    if parsed is None:
        return None, "no-parse"
    ms = parsed.get("MS", 0)
    if isinstance(ms, int) and ms > 0:
        return ms / float(n), "timer"
    return (wall * 1000.0 / float(n)), "MS=0; wall/n"

def run_bench_bump(bin_run, args_prefix, n0, timeout, max_n=8192):
    # Raise N until MS>0 or max_n (IO.now / Instant both 1ms granularity).
    n = n0
    last = None
    while True:
        r = bin_run([*args_prefix, str(n)], timeout)
        parsed = parse_bench(r["out"]) if not r["timeout"] else None
        last = (r, parsed, n)
        if r["timeout"] or parsed is None:
            return last
        if parsed.get("MS", 0) > 0 or n >= max_n:
            return last
        n = min(max_n, max(n * 4, n + 1))

def speed():
    log("\n== Speed (printable; does not fail the check) ==")
    log("FAIR: in-memory vs in-memory. Rust toml crate loops N inside one process.")
    log("FAIR: eztoml parse/render timed via IO.now; load (and render's parse) outside.")
    log("NOT a speed ref: Python tomllib, toml CLI, per-op process spawn, disk open/write.")
    log("Fixtures: product-shaped multi-KB configs (manifest / app / lockfile-shaped).")
    log("ratio = eztoml/rust (>1 ⇒ eztoml slower). If MS=0 after bumping N, no vs-rust claim.")

    jobs = []
    for name, text in SPEED_FIXTURES:
        path = write_fix("spd_" + name + ".toml", text)
        jobs.append((name, path, len(text)))

    log("\n-- Decode / parse (in-memory vs in-memory) --")
    log(f"{'fixture':<22} {'bytes':>7} {'N':>5} {'eztoml ms/op':>14} {'rust ms/op':>12} {'ratio':>8}")
    for name, path, nbytes in jobs:
        n0 = 4 if nbytes > 12000 else (8 if nbytes > 4000 else 20)
        er, ep, en = run_bench_bump(ez, ["bench-parse", path], n0, 300)
        rr, rp, rn = run_bench_bump(rust, ["bench-parse", path], en, 300)
        # Use the same N for ratio when both resolved; prefer max N that both ran.
        n = max(en, rn)
        if en != rn:
            # Re-run both at shared N for an apples-to-apples ratio.
            er = ez(["bench-parse", path, str(n)], 300)
            ep = parse_bench(er["out"]) if not er["timeout"] else None
            rr = rust(["bench-parse", path, str(n)], 300)
            rp = parse_bench(rr["out"]) if not rr["timeout"] else None
        if er["timeout"] or rr["timeout"] or ep is None or rp is None:
            row = f"ERROR parse {name} ez={er.get('rc')} rust={rr.get('rc')}"
            log(row); speed_rows.append(row); continue
        ez_per, ez_note = ms_per(ep, er["wall"], n)
        ru_per, ru_note = ms_per(rp, rr["wall"], n)
        if ep.get("MS", 0) > 0 and rp.get("MS", 0) > 0 and ru_per > 0:
            ratio = ez_per / ru_per
            row = (f"{name:<22} {nbytes:7d} {n:5d} {ez_per:14.4f} {ru_per:12.4f} {ratio:7.1f}x"
                   f"  ({ez_note}/{ru_note})")
        else:
            row = (f"{name:<22} {nbytes:7d} {n:5d} {ez_per:14.4f} {ru_per:12.4f}    n/a"
                   f"  ({ez_note}/{ru_note}; no vs-rust claim)")
        log(row); speed_rows.append("parse " + row)

    log("\n-- Encode / render (in-memory vs in-memory) --")
    log(f"{'fixture':<22} {'bytes':>7} {'N':>5} {'eztoml ms/op':>14} {'rust ms/op':>12} {'ratio':>8}")
    for name, path, nbytes in jobs:
        n0 = 4 if nbytes > 12000 else (8 if nbytes > 4000 else 20)
        er, ep, en = run_bench_bump(ez, ["bench-render", path], n0, 300)
        rr, rp, rn = run_bench_bump(rust, ["bench-render", path], en, 300)
        n = max(en, rn)
        if en != rn:
            er = ez(["bench-render", path, str(n)], 300)
            ep = parse_bench(er["out"]) if not er["timeout"] else None
            rr = rust(["bench-render", path, str(n)], 300)
            rp = parse_bench(rr["out"]) if not rr["timeout"] else None
        if er["timeout"] or rr["timeout"] or ep is None or rp is None:
            row = f"ERROR render {name} ez={er.get('rc')} rust={rr.get('rc')}"
            log(row); speed_rows.append(row); continue
        ez_per, ez_note = ms_per(ep, er["wall"], n)
        ru_per, ru_note = ms_per(rp, rr["wall"], n)
        if ep.get("MS", 0) > 0 and rp.get("MS", 0) > 0 and ru_per > 0:
            ratio = ez_per / ru_per
            row = (f"{name:<22} {nbytes:7d} {n:5d} {ez_per:14.4f} {ru_per:12.4f} {ratio:7.1f}x"
                   f"  ({ez_note}/{ru_note})")
        else:
            row = (f"{name:<22} {nbytes:7d} {n:5d} {ez_per:14.4f} {ru_per:12.4f}    n/a"
                   f"  ({ez_note}/{ru_note}; no vs-rust claim)")
        log(row); speed_rows.append("render " + row)

def main():
    log("eztoml vs Rust toml crate bench (Nix-embedded harness)")
    log(f"driver={DRV}")
    log(f"ref={REF}")
    log(f"mode={MODE}")
    log("Decode+encode ref: Rust toml 0.5 Value in-process. Timing never fails the check.")
    ping = ez(["ping"], 10)
    if ping["out"].strip() != "pong":
        log("FAIL: eztoml driver ping"); log(repr(ping)); sys.exit(2)
    log("eztoml driver ping ok (native ELF)")
    rping = rust(["ping"], 10)
    if rping["out"].strip() != "pong":
        log("FAIL: rust ref ping"); log(repr(rping)); sys.exit(2)
    log("rust ref ping ok")
    try:
        if MODE in ("correctness", "all"):
            correct_laws(); correct_product()
        if MODE in ("speed", "all"):
            speed()
    except Exception:
        log("HARNESS EXCEPTION"); log(traceback.format_exc()); sys.exit(2)
    log(f"\n== Summary: {fails} hard failure(s) of {len(cases)} cases ==")
    for c in cases:
        if c["status"] != "PASS" and c["hard"]:
            log(f"  FAIL {c['group']} | {c['name']}")
    if fails:
        sys.exit(1)
    log("ALL HARD CHECKS PASSED")

if __name__ == "__main__":
    main()
''
