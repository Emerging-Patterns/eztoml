// Fair in-process TOML reference for eztoml benches (toml crate Value).
// Decode: toml::from_str. Encode: toml::to_string.
// Timed loops run entirely inside this process — callers pass N; no per-op spawn.
use std::env;
use std::fs;
use std::process;
use std::time::Instant;

fn die(msg: &str) -> ! {
    eprintln!("{msg}");
    process::exit(1);
}

fn fingerprint(v: &toml::Value) -> u64 {
    // Stable-enough checksum so the timed loop is not DCE'd.
    let s = toml::to_string(v).unwrap_or_default();
    let mut h: u64 = s.len() as u64;
    for (i, b) in s.bytes().enumerate() {
        h = h
            .wrapping_mul(131)
            .wrapping_add(b as u64)
            .wrapping_add(i as u64);
    }
    h
}

fn cmd_ping() {
    println!("pong");
}

fn cmd_parse(path: &str) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| die(&format!("read {path}: {e}")));
    match text.parse::<toml::Value>() {
        Ok(v) => println!("OK SUM {} BYTES {}", fingerprint(&v), text.len()),
        Err(e) => println!("ERR {}", e),
    }
}

fn cmd_render(path: &str, dst: &str) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| die(&format!("read {path}: {e}")));
    let v: toml::Value = text
        .parse()
        .unwrap_or_else(|e| die(&format!("parse: {e}")));
    let out = toml::to_string(&v).unwrap_or_else(|e| die(&format!("encode: {e}")));
    fs::write(dst, out).unwrap_or_else(|e| die(&format!("write {dst}: {e}")));
}

fn cmd_rt(path: &str, dst: &str) {
    // Parse then encode (reference round-trip into dst).
    cmd_render(path, dst);
}

fn cmd_bench_parse(path: &str, n: u32) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| die(&format!("read {path}: {e}")));
    let bytes = text.len();
    // Warm once outside the timer so the measured window is steady-state.
    let _ = text.parse::<toml::Value>();
    let t0 = Instant::now();
    let mut sum: u64 = 0;
    for _ in 0..n {
        match text.parse::<toml::Value>() {
            Ok(v) => sum = sum.wrapping_add(fingerprint(&v)),
            Err(_) => sum = sum.wrapping_add(1),
        }
    }
    let ms = t0.elapsed().as_millis();
    println!("MS {ms} SUM {sum} N {n} BYTES {bytes}");
}

fn cmd_bench_render(path: &str, n: u32) {
    let text = fs::read_to_string(path).unwrap_or_else(|e| die(&format!("read {path}: {e}")));
    let v: toml::Value = text
        .parse()
        .unwrap_or_else(|e| die(&format!("parse: {e}")));
    let bytes = text.len();
    let _ = toml::to_string(&v);
    let t0 = Instant::now();
    let mut sum: u64 = 0;
    for _ in 0..n {
        match toml::to_string(&v) {
            Ok(s) => sum = sum.wrapping_add(s.len() as u64),
            Err(_) => sum = sum.wrapping_add(1),
        }
    }
    let ms = t0.elapsed().as_millis();
    println!("MS {ms} SUM {sum} N {n} BYTES {bytes}");
}

fn main() {
    let mut args = env::args().skip(1);
    let cmd = args.next().unwrap_or_default();
    match cmd.as_str() {
        "ping" => cmd_ping(),
        "parse" => {
            let path = args.next().unwrap_or_else(|| die("parse needs <path>"));
            cmd_parse(&path);
        }
        "render" => {
            let path = args.next().unwrap_or_else(|| die("render needs <src> <dst>"));
            let dst = args.next().unwrap_or_else(|| die("render needs <src> <dst>"));
            cmd_render(&path, &dst);
        }
        "rt" => {
            let path = args.next().unwrap_or_else(|| die("rt needs <src> <dst>"));
            let dst = args.next().unwrap_or_else(|| die("rt needs <src> <dst>"));
            cmd_rt(&path, &dst);
        }
        "bench-parse" => {
            let path = args
                .next()
                .unwrap_or_else(|| die("bench-parse needs <path> <n>"));
            let n: u32 = args
                .next()
                .unwrap_or_else(|| die("bench-parse needs <path> <n>"))
                .parse()
                .unwrap_or_else(|_| die("bad n"));
            cmd_bench_parse(&path, n);
        }
        "bench-render" => {
            let path = args
                .next()
                .unwrap_or_else(|| die("bench-render needs <path> <n>"));
            let n: u32 = args
                .next()
                .unwrap_or_else(|| die("bench-render needs <path> <n>"))
                .parse()
                .unwrap_or_else(|_| die("bad n"));
            cmd_bench_render(&path, n);
        }
        other => die(&format!("unknown command {other}")),
    }
}
