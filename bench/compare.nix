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
# - ratio = eztoml_ms / rust_ms (>1 => eztoml slower).
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
Q = chr(34)
SQ = chr(39)

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
    log("[%s] %s | %s" % (status, group, name))
    log("    %s" % detail)
    if hard and status != "PASS":
        fails += 1

def write_fix(name, text):
    path = os.path.join(WORK, name)
    open(path, "w", encoding="utf-8").write(text)
    return path

# --- TOML v1.0.0 fixtures (correctness cites toml.io/en/v1.0.0 / toml.abnf) ---

VALID_LAWS = [
    ("toml_comment", "# comment\nkey = " + Q + "v" + Q + "\n"),
    ("toml_bool", "a = true\nb = false\n"),
    ("toml_string_basic", "s = " + Q + "A\\nB\\tC\\" + Q + "D\\\\E" + Q + "\n"),
    ("toml_string_literal", "s = " + SQ + "A\\\\nB" + SQ + "\n"),
    ("toml_integer", "a = +99\nb = 42\nc = 0\nd = -17\ne = 1_000\n"),
    ("toml_integer_hex", "a = 0x10\nb = 0o10\nc = 0b10\n"),
    ("toml_float", "a = +1.0\nb = -0.01\nc = 5e+22\nd = 6.626e-34\n"),
    ("toml_float_special", "a = inf\nb = -inf\nc = nan\n"),
    ("toml_table", "[pkg]\nname = " + Q + "eztoml" + Q + "\n"),
    ("toml_dotted", "a.b = 1\nfruit.name = " + Q + "banana" + Q + "\n"),
    ("toml_inline", "p = { x = 1, y = 2 }\nanimal = { type.name = " + Q + "pug" + Q + " }\n"),
    ("toml_array", "a = [1, 2,]\nb = []\nc = [[1], [2, 3]]\n"),
    ("toml_aot", "[[fruit]]\nname = " + Q + "apple" + Q + "\n\n[[fruit]]\nname = " + Q + "banana" + Q + "\n"),
    ("toml_datetime", "a = 1979-05-27T07:32:00Z\nb = 1979-05-27T00:32:00-07:00\nc = 1979-05-27\nd = 07:32:00\n"),
    ("toml_keyval", "first = " + Q + "Tom" + Q + "\nlast = " + Q + "Preston-Werner" + Q + "\n"),
    ("toml_quoted_key", Q + "127.0.0.1" + Q + " = " + Q + "value" + Q + "\n" + SQ + "key2" + SQ + " = " + Q + "value" + Q + "\n"),
]

INVALID_LAWS = [
    ("true_capital", "a = True\n"),
    ("leading_zero", "a = 01\n"),
    ("bad_escape", "s = " + Q + "\\q" + Q + "\n"),
    ("inline_trailing_comma", "p = { x = 1, }\n"),
    ("inline_newline", "p = { x = 1\n}\n"),
    ("duplicate_key", "name = " + Q + "a" + Q + "\nname = " + Q + "b" + Q + "\n"),
    ("duplicate_table", "[fruit]\na = 1\n\n[fruit]\nb = 2\n"),
    ("aot_then_table", "[[fruit]]\nn = 1\n\n[fruit]\nx = 2\n"),
    ("empty_keyval", "key =\n"),
    ("two_pairs_one_line", "first = " + Q + "Tom" + Q + " last = " + Q + "Preston-Werner" + Q + "\n"),
    ("i64_overflow", "a = 9223372036854775808\n"),
]

def package_manifest(n_deps=40):
    lines = [
        "name = " + Q + "wavebench" + Q,
        "version = " + Q + "1.4.2" + Q,
        "edition = 2021",
        "publish = false",
        "authors = [" + ", ".join(Q + "author-%d@example.com" % i + Q for i in range(8)) + "]",
        "",
        "[package.metadata.release]",
        "sign-commit = true",
        "pre-release-commit-message = " + Q + "chore: release vX" + Q,
        "rate = 0.0125",
        "shipped = 2024-06-15T18:30:00Z",
        "",
        "[dependencies]",
    ]
    for i in range(n_deps):
        opt = "true" if (i % 2 == 0) else "false"
        lines.append(
            "dep-%02d = { version = %s=%d.%d.%d%s, optional = %s, features = [%sa%s, %sb-%d%s] }"
            % (i, Q, i, i % 10, i % 7, Q, opt, Q, Q, Q, i, Q)
        )
    lines += [
        "",
        "[features]",
        "default = [" + Q + "std" + Q + ", " + Q + "serde" + Q + "]",
        "std = []",
        "serde = [" + Q + "dep-00" + Q + "]",
        "",
        "[profile.release]",
        "lto = true",
        "codegen-units = 1",
        "opt-level = 3",
        "panic = " + Q + "abort" + Q,
        "",
    ]
    for i in range(12):
        lines += [
            "[[bin]]",
            "name = " + Q + ("tool-%02d" % i) + Q,
            "path = " + Q + ("src/bin/tool_%02d.rs" % i) + Q,
            "required-features = [" + Q + "std" + Q + "]",
            "",
        ]
    for i in range(6):
        # Literal dotted key uses single quotes so the cfg string may hold doubles.
        lines += [
            "[target." + SQ + "cfg(target_os = " + Q + "linux" + Q + ")" + SQ + ".dependencies.os-dep-%d]" % i,
            "version = " + Q + ("1.%d.0" % i) + Q,
            "default-features = false",
            "",
        ]
    lines += [
        "[workspace.package]",
        "license = " + Q + "MIT" + Q,
        "repository = " + Q + "https://example.com/wavebench" + Q,
        "",
        "[workspace.dependencies]",
        "shared = { path = " + Q + "../shared" + Q + ", version = " + Q + "0.1.0" + Q + " }",
        "",
        "members = [" + Q + "crates/core" + Q + ", " + Q + "crates/cli" + Q + "]",
        "",
    ]
    return "\n".join(lines) + "\n"

def app_config():
    servers = []
    for i in range(20):
        en = "true" if (i % 3 != 0) else "false"
        mo = (i % 12) + 1
        dy = (i % 28) + 1
        servers.append("\n".join([
            "[[servers]]",
            "name = " + Q + ("svc-%02d" % i) + Q,
            "host = " + Q + ("10.0.%d.%d" % (i // 256, i % 256)) + Q,
            "port = %d" % (8000 + i),
            "weight = %.2f" % (0.5 + (i % 10) * 0.05),
            "enabled = %s" % en,
            "started = 2023-%02d-%02dT12:00:00Z" % (mo, dy),
            "tags = [" + Q + "prod" + Q + ", " + Q + ("tier-%d" % (i % 4)) + Q + ", " + Q + ("az-%d" % ((i % 3) + 1)) + Q + "]",
            "[servers.tls]",
            "cert = " + Q + ("/etc/certs/svc-%02d.pem" % i) + Q,
            "alpn = [" + Q + "h2" + Q + ", " + Q + "http/1.1" + Q + "]",
            "",
        ]))
    head = "\n".join([
        "[app]",
        "name = " + Q + "wave-gateway" + Q,
        "env = " + Q + "production" + Q,
        "workers = 16",
        "timeout_ms = 2500",
        "ratio = 0.875",
        "boot = 2022-01-01T00:00:00Z",
        "",
        "[app.logging]",
        "level = " + Q + "info" + Q,
        "format = " + Q + "json" + Q,
        "",
        "[app.logging.targets.stdout]",
        "enabled = true",
        "",
        "[database]",
        "url = " + Q + "postgres://user:pass@db.internal:5432/app" + Q,
        "pool = 32",
        "",
        "[database.read_replicas]",
        "hosts = [" + Q + "r1.internal" + Q + ", " + Q + "r2.internal" + Q + ", " + Q + "r3.internal" + Q + "]",
        "",
    ])
    return head + "\n" + "\n".join(servers)

def cargo_lockish(n=80):
    chunks = ["# This file is automatically @generated.\nversion = 3\n"]
    for i in range(n):
        chunks.append("\n".join([
            "[[package]]",
            "name = " + Q + ("crate-%03d" % i) + Q,
            "version = " + Q + ("1.%d.%d" % (i % 20, i % 7)) + Q,
            "source = " + Q + "registry+https://github.com/rust-lang/crates.io-index" + Q,
            "checksum = " + Q + ("a" * 64) + Q,
            "dependencies = [",
            "  " + Q + ("crate-%03d" % ((i + 1) % n)) + Q + ",",
            "  " + Q + ("crate-%03d 2.0" % ((i + 7) % n)) + Q + ",",
            "]",
            "",
        ]))
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
    log("Cite: https://toml.io/en/v1.0.0 - valid docs parse; invalid docs reject.")
    for name, text in VALID_LAWS:
        path = write_fix("ok_" + name + ".toml", text)
        rr = rust(["parse", path], 30)
        rust_ok = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("OK")
        add_case("A rust parse", name, "PASS" if rust_ok else "FAIL",
                 "rc=%s out=%r err=%r" % (rr["rc"], rr["out"][:120], rr["err"][:80]))
        er = ez(["parse", path], 60)
        ez_ok = (not er["timeout"]) and er["rc"] == 0 and er["out"].startswith("OK")
        add_case("B eztoml parse", name, "PASS" if ez_ok else "FAIL",
                 "rc=%s out=%r err=%r" % (er["rc"], er["out"][:120], er["err"][:80]))
        dst = path + ".rt.toml"
        rt = ez(["rt", path, dst], 60)
        if rt["timeout"] or rt["rc"] != 0 or not os.path.exists(dst):
            add_case("C eztoml->rust rt", name, "FAIL", "rt rc=%s err=%s" % (rt["rc"], rt["err"][:120]))
        else:
            rp = rust(["parse", dst], 30)
            ok = (not rp["timeout"]) and rp["rc"] == 0 and rp["out"].startswith("OK")
            add_case("C eztoml->rust rt", name, "PASS" if ok else "FAIL",
                     "rendered %dB -> rust %r" % (os.path.getsize(dst), rp["out"][:100]))
    for name, text in INVALID_LAWS:
        path = write_fix("bad_" + name + ".toml", text)
        er = ez(["parse", path], 60)
        out = er["out"].strip()
        ez_reject = (not er["timeout"]) and er["rc"] == 0 and out.startswith("BAD ") and len(out) > 4
        add_case("D eztoml reject", name, "PASS" if ez_reject else "FAIL",
                 "rc=%s out=%r" % (er["rc"], out[:140]))
        rr = rust(["parse", path], 30)
        rust_reject = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("ERR")
        add_case("D rust reject", name, "PASS" if rust_reject else "FAIL",
                 "rc=%s out=%r" % (rr["rc"], rr["out"][:140]), hard=True)

def correct_product():
    log("\n== Correctness (product-shaped fixtures) ==")
    for name, text in SPEED_FIXTURES:
        path = write_fix("prod_" + name + ".toml", text)
        rr = rust(["parse", path], 60)
        rust_ok = (not rr["timeout"]) and rr["rc"] == 0 and rr["out"].startswith("OK")
        add_case("E rust product", name, "PASS" if rust_ok else "FAIL",
                 "bytes=%d out=%r" % (len(text), rr["out"][:100]))
        er = ez(["parse", path], 120)
        ez_ok = (not er["timeout"]) and er["rc"] == 0 and er["out"].startswith("OK")
        add_case("E eztoml product", name, "PASS" if ez_ok else "FAIL",
                 "bytes=%d out=%r" % (len(text), er["out"][:100]))
        dst = path + ".rt.toml"
        rt = ez(["rt", path, dst], 120)
        if rt["timeout"] or rt["rc"] != 0 or not os.path.exists(dst):
            add_case("E eztoml product rt", name, "FAIL", "rc=%s" % rt["rc"])
        else:
            rp = rust(["parse", dst], 60)
            ok = (not rp["timeout"]) and rp["rc"] == 0 and rp["out"].startswith("OK")
            add_case("E eztoml product rt->rust", name, "PASS" if ok else "FAIL",
                     "rt %dB -> %r" % (os.path.getsize(dst), rp["out"][:100]))

def ms_per(parsed, wall, n):
    if parsed is None:
        return None, "no-parse"
    ms = parsed.get("MS", 0)
    if isinstance(ms, int) and ms > 0:
        return ms / float(n), "timer"
    return (wall * 1000.0 / float(n)), "MS=0; wall/n"

def run_bench_bump(bin_run, args_prefix, n0, timeout, max_n=8192):
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
    log("FAIR: eztoml parse/render timed via IO.now; load (and render parse) outside.")
    log("NOT a speed ref: Python tomllib, toml CLI, per-op process spawn, disk open/write.")
    log("Fixtures: product-shaped multi-KB configs (manifest / app / lockfile-shaped).")
    log("ratio = eztoml/rust (>1 => eztoml slower). If MS=0 after bumping N, no vs-rust claim.")
    jobs = []
    for name, text in SPEED_FIXTURES:
        path = write_fix("spd_" + name + ".toml", text)
        jobs.append((name, path, len(text)))
    log("\n-- Decode / parse (in-memory vs in-memory) --")
    log("%-22s %7s %5s %14s %12s %8s" % ("fixture", "bytes", "N", "eztoml ms/op", "rust ms/op", "ratio"))
    for name, path, nbytes in jobs:
        n0 = 4 if nbytes > 12000 else (8 if nbytes > 4000 else 20)
        er, ep, en = run_bench_bump(ez, ["bench-parse", path], n0, 300)
        rr, rp, rn = run_bench_bump(rust, ["bench-parse", path], en, 300)
        n = max(en, rn)
        if en != rn:
            er = ez(["bench-parse", path, str(n)], 300)
            ep = parse_bench(er["out"]) if not er["timeout"] else None
            rr = rust(["bench-parse", path, str(n)], 300)
            rp = parse_bench(rr["out"]) if not rr["timeout"] else None
        if er["timeout"] or rr["timeout"] or ep is None or rp is None:
            row = "ERROR parse %s ez=%s rust=%s" % (name, er.get("rc"), rr.get("rc"))
            log(row); speed_rows.append(row); continue
        ez_per, ez_note = ms_per(ep, er["wall"], n)
        ru_per, ru_note = ms_per(rp, rr["wall"], n)
        if ep.get("MS", 0) > 0 and rp.get("MS", 0) > 0 and ru_per > 0:
            ratio = ez_per / ru_per
            row = "%-22s %7d %5d %14.4f %12.4f %7.1fx  (%s/%s)" % (
                name, nbytes, n, ez_per, ru_per, ratio, ez_note, ru_note)
        else:
            row = "%-22s %7d %5d %14.4f %12.4f    n/a  (%s/%s; no vs-rust claim)" % (
                name, nbytes, n, ez_per, ru_per, ez_note, ru_note)
        log(row); speed_rows.append("parse " + row)
    log("\n-- Encode / render (in-memory vs in-memory) --")
    log("%-22s %7s %5s %14s %12s %8s" % ("fixture", "bytes", "N", "eztoml ms/op", "rust ms/op", "ratio"))
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
            row = "ERROR render %s ez=%s rust=%s" % (name, er.get("rc"), rr.get("rc"))
            log(row); speed_rows.append(row); continue
        ez_per, ez_note = ms_per(ep, er["wall"], n)
        ru_per, ru_note = ms_per(rp, rr["wall"], n)
        if ep.get("MS", 0) > 0 and rp.get("MS", 0) > 0 and ru_per > 0:
            ratio = ez_per / ru_per
            row = "%-22s %7d %5d %14.4f %12.4f %7.1fx  (%s/%s)" % (
                name, nbytes, n, ez_per, ru_per, ratio, ez_note, ru_note)
        else:
            row = "%-22s %7d %5d %14.4f %12.4f    n/a  (%s/%s; no vs-rust claim)" % (
                name, nbytes, n, ez_per, ru_per, ez_note, ru_note)
        log(row); speed_rows.append("render " + row)

def main():
    log("eztoml vs Rust toml crate bench (Nix-embedded harness)")
    log("driver=%s" % DRV)
    log("ref=%s" % REF)
    log("mode=%s" % MODE)
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
    log("\n== Summary: %d hard failure(s) of %d cases ==" % (fails, len(cases)))
    for c in cases:
        if c["status"] != "PASS" and c["hard"]:
            log("  FAIL %s | %s" % (c["group"], c["name"]))
    if fails:
        sys.exit(1)
    log("ALL HARD CHECKS PASSED")

if __name__ == "__main__":
    main()
''
