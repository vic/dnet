//! `dnx` — userland Nix on δ-nets. Subcommand dispatch over the consolidated
//! crates: `dnx-lang` (eval), `dnx-flake` (flake show / `.#attr`),
//! `dnx-drv` (`realize`), `dnx-store` (content-addressed store).

use dnx_drv::{from_attrs, Derivation};
use dnx_flake::{Flake, LockStatus, OutputKind};
use dnx_lang::is_literal_attrset;
use dnx_lang::runtime::{NixEvalResult, NixRuntime};
use dnx_pyparse::PyRuntime;
use dnx_store::Store;
use dnx_test::{run_computed_suite, run_suite, DiskResultCache, Outcome};
use std::path::{Path, PathBuf};
use std::process;

const USAGE: &str = "\
dnx — userland Nix on δ-nets

usage: dnx <command> [args]

commands:
  eval [--file PATH | EXPR]   evaluate a Nix expression
  py eval EXPR                evaluate a Python-subset expression
  py FILE.py                  evaluate a Python-subset file
                              (same δ-net engine as Nix — one substrate)
  test FILE [--jobs N]        run a nix-unit-style test suite in parallel
       [--no-cache]           (re-runs hit a content cache; --no-cache to bypass)
  build [-f PATH|.#ATTR|EXPR] build a derivation → store path
  flake show [PATH]           list a flake's outputs (dir or flake.nix; default .)
  flake check [PATH]          evaluate all outputs; nonzero exit on any error
  flake metadata [PATH]       print a flake's description, inputs, lock status
  store add PATH              add a path to the store
  store path PATH             print the store path a file would get
  daemon start                serve a warm cache over the user socket
  daemon status               print the running daemon's version + queue depth
  daemon stop                 ask the running daemon to drain and exit

  -h, --help                  show this help
  -V, --version               show version";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("eval") => cmd_eval(&args[2..]),
        Some("py") => cmd_py(&args[2..]),
        Some("test") => cmd_test(&args[2..]),
        Some("build") => cmd_build(&args[2..]),
        Some("flake") => cmd_flake(&args[2..]),
        Some("store") => cmd_store(&args[2..]),
        Some("daemon") => cmd_daemon(&args[2..]),
        Some("-h") | Some("--help") | Some("help") => println!("{USAGE}"),
        Some("-V") | Some("--version") => println!("dnx {}", env!("CARGO_PKG_VERSION")),
        Some(cmd) => {
            eprintln!("unknown command: {cmd}\n\n{USAGE}");
            process::exit(1);
        }
        None => {
            eprintln!("{USAGE}");
            process::exit(1);
        }
    }
}

fn die(msg: impl std::fmt::Display) -> ! {
    eprintln!("error: {msg}");
    process::exit(1);
}

/// True if any arg is `-h`/`--help`. Each `cmd_*` checks this BEFORE parsing so
/// a help request prints usage and exits 0 instead of being treated as a
/// positional/expression arg (which previously evaluated `--help` as Nix → an
/// opaque engine error: the "--help trap", cli-ux.md §2/§5).
fn wants_help(args: &[String]) -> bool {
    args.iter().any(|a| a == "-h" || a == "--help")
}

/// Print a subcommand's usage line(s) and exit 0 (a help request succeeded).
fn help(usage: &str) -> ! {
    println!("{usage}");
    process::exit(0);
}

// ── daemon ────────────────────────────────────────────────────────────────

/// `dnx daemon {start|status|stop}` over the userland socket (no root). The
/// daemon holds a warm in-memory cache and serializes builds so two clients
/// asking for the same derivation build it once ("compute once, serve many").
fn cmd_daemon(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx daemon {start|status|stop}\n\
             \n\
             start   serve a warm cache over the user socket (blocks)\n\
             status  print the running daemon's version (exit 1 if not running)\n\
             stop    ask the running daemon to drain and exit",
        );
    }
    let sock = dnx_daemon::default_socket();
    match args.first().map(String::as_str) {
        Some("start") => {
            let store = match Store::open() {
                Ok(s) => s,
                Err(e) => die(format!("daemon: open store: {e}")),
            };
            println!("daemon: serving on {}", sock.display());
            match dnx_daemon::serve(&sock, dnx_daemon::Daemon::new(store)) {
                Ok(_) => println!("daemon: stopped"),
                Err(e) => die(format!("daemon: {e}")),
            }
        }
        Some("status") => match dnx_daemon::ping(&sock) {
            Some(version) => println!("daemon: running (version {version}), queue depth 0"),
            None => {
                println!("daemon: not running");
                process::exit(1);
            }
        },
        Some("stop") => match dnx_daemon::client_shutdown(&sock) {
            Ok(()) => println!("daemon: stopping"),
            Err(e) => die(format!("daemon: {e}")),
        },
        Some(other) => die(format!("daemon: unknown subcommand {other:?}")),
        None => die("daemon: expected start, status, or stop"),
    }
}

// ── eval ────────────────────────────────────────────────────────────────────

fn cmd_eval(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx eval [--file PATH | EXPR]\n\
             \n\
             Evaluate a Nix expression and print the result.\n\
             --file PATH   evaluate the expression in PATH\n\
             EXPR          evaluate the given expression string",
        );
    }
    let rt = NixRuntime::pure();
    let result = if args.first().map(String::as_str) == Some("--file") {
        match args.get(1) {
            Some(path) => rt.eval_file(Path::new(path)),
            None => die("--file requires a path"),
        }
    } else {
        let expr = args.join(" ");
        if expr.is_empty() {
            die("eval requires an expression");
        }
        rt.eval(&expr)
    };
    print_eval(&result);
}

/// Render a float as cppNix's value printer does: `src/libexpr/print.cc`
/// `printFloat` writes `output << v.fpoint()`, i.e. C++ default `ostream`
/// formatting for `double`, which equals C `printf("%.6g", x)` — 6 significant
/// digits, trailing zeros (and a bare `.`) stripped, scientific notation when
/// the decimal exponent is ≥ 6 or ≤ −5. So `3.0` → `3`, `1000000.0` → `1e+06`.
/// (Distinct from `toString`/interpolation, which cppNix renders with `%f`.)
fn fmt_float(x: f64) -> String {
    if x == 0.0 {
        return "0".to_string();
    }
    if !x.is_finite() {
        return format!("{x}");
    }
    const P: i32 = 6;
    let sci = format!("{:.*e}", (P - 1) as usize, x);
    // `{:e}` always emits `…e<int>`; if the exponent is somehow absent, fall
    // back to scientific form rather than guessing a fixed layout.
    let exp = sci.split_once('e').and_then(|(_, e)| e.parse::<i32>().ok());
    let body = match exp {
        Some(exp) if (-4..P).contains(&exp) => {
            format!("{:.*}", (P - 1 - exp).max(0) as usize, x)
        }
        _ => sci,
    };
    match body.split_once('e') {
        Some((mant, e)) => {
            let exp = e.parse::<i32>().unwrap_or_default();
            let sign = if exp < 0 { '-' } else { '+' };
            format!("{}e{}{:02}", strip_float(mant), sign, exp.abs())
        }
        None => strip_float(&body).to_string(),
    }
}

/// Strip trailing zeros, and a trailing `.`, from a fixed-point mantissa (a
/// no-op when there is no decimal point, so integers keep their digits).
fn strip_float(s: &str) -> &str {
    if s.contains('.') {
        s.trim_end_matches('0').trim_end_matches('.')
    } else {
        s
    }
}

/// Print a `NixEvalResult` in the human one-line form; exit 1 on an eval error
/// (so a script never reads a failed eval as success).
fn print_eval(result: &NixEvalResult) {
    match result {
        NixEvalResult::Int(n) => println!("{n}"),
        NixEvalResult::Float(f) => println!("{}", fmt_float(*f)),
        NixEvalResult::Str(s) => println!("{s}"),
        NixEvalResult::Bool(b) => println!("{b}"),
        NixEvalResult::Null => println!("null"),
        NixEvalResult::List(xs) => println!("[{} items]", xs.len()),
        NixEvalResult::AttrSet(kvs) => println!("{{ {} attrs }}", kvs.len()),
        NixEvalResult::Lambda(_) => println!("<lambda>"),
        NixEvalResult::Error(e) => die(e),
    }
}

// ── py ──────────────────────────────────────────────────────────────────────

/// `dnx py eval EXPR` (a Python-subset expression) or `dnx py FILE.py` (a
/// Python-subset file). Python lowers to the *same* core IR as Nix and runs on
/// the *same* engine, so the readback prints in the identical `print_eval` form
/// (dnx-py-interop.md §4) — a Python `derivation(...)` reads back as the same
/// attrset a Nix `derivationStrict {...}` does.
fn cmd_py(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx py [eval [--file PATH] EXPR | FILE.py]\n\
             \n\
             Evaluate a Python-subset program on the same δ-net engine as Nix.\n\
             eval EXPR          evaluate the given expression string\n\
             eval --file PATH   evaluate the Python-subset file at PATH\n\
             FILE.py            evaluate the Python-subset file FILE.py",
        );
    }
    let src = match args.first().map(String::as_str) {
        Some("eval") => match args.get(1).map(String::as_str) {
            Some("--file") | Some("-f") => match args.get(2) {
                Some(path) => read_py_file(path),
                None => die("py eval --file requires a path"),
            },
            Some(_) => args[1..].join(" "),
            None => die("py eval requires an expression"),
        },
        Some(path) if path.ends_with(".py") => read_py_file(path),
        Some(other) => die(format!(
            "py: expected `eval EXPR` or a FILE.py, got {other:?}"
        )),
        None => die("py: expected `eval EXPR` or a FILE.py"),
    };
    print_eval(&PyRuntime::pure().eval(&src));
}

/// Read a `.py` source file, dying with the path on an I/O error (so a script
/// never reads a missing file as an empty program).
fn read_py_file(path: &str) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| die(format!("{path}: {e}")))
}

// ── test ──────────────────────────────────────────────────────────────────

/// `dnx test FILE [--jobs N] [--no-cache]` — run a nix-unit-style suite. Each
/// `{ expr; expected; }` case is evaluated independently and in parallel; the
/// case passes iff `expr` and `expected` are convertible (dnx-test-runner-design.md).
/// Exits 0 iff every case passes (a CI gate, like `runTests` ≡ `[]`).
fn cmd_test(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx test FILE [--jobs N] [--no-cache]\n\
             \n\
             Run a nix-unit-style test suite (FILE must eval to an attrset of\n\
             `{ expr; expected; }` cases). Exit 0 iff every case passes.\n\
             --jobs N     run with N parallel jobs (default: CPU count)\n\
             --no-cache   bypass the content-addressed re-run cache",
        );
    }
    let mut file: Option<&str> = None;
    let mut jobs: Option<usize> = None;
    let mut use_cache = true;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--jobs" | "-j" => {
                jobs = Some(
                    it.next()
                        .and_then(|n| n.parse().ok())
                        .unwrap_or_else(|| die("--jobs requires a positive integer")),
                );
            }
            "--no-cache" => use_cache = false,
            other if other.starts_with('-') => die(format!("test: unknown flag {other:?}")),
            path => {
                if file.replace(path).is_some() {
                    die("test: more than one FILE given");
                }
            }
        }
    }
    let file = file.unwrap_or_else(|| die("test: expected a FILE.nix"));
    let src = std::fs::read_to_string(file).unwrap_or_else(|e| die(format!("{file}: {e}")));
    let jobs = jobs.unwrap_or_else(default_jobs);

    let cache = if use_cache {
        Some(open_test_cache())
    } else {
        None
    };
    // Dispatch on the suite's shape (computed-suite-runner.md §4c). A syntactic
    // attrset top takes the LITERAL path — per-case re-eval + the source-keyed
    // cache. But a literal-top suite whose VALUES are computed (the gen-adapter
    // splice form `{ s = m.flake.tests.s; … }`) walks to ZERO syntactic cases:
    // fall back to evaluating the whole file to a value tree and reading its
    // leaves. A non-attrset top (`mapAttrs`/`flatten`/application) goes straight
    // to the computed path.
    let report = if is_literal_attrset(&src) {
        match run_suite(&src, jobs, cache.as_ref()) {
            Ok(r) if !r.cases.is_empty() => Ok(r),
            Ok(_) => run_computed_suite(&src, jobs),
            Err(e) => Err(e),
        }
    } else {
        run_computed_suite(&src, jobs)
    }
    .unwrap_or_else(|e| die(e));

    for c in &report.cases {
        let tag = if c.cached {
            " (cached, 0 interactions)"
        } else {
            ""
        };
        match &c.outcome {
            Outcome::Pass => println!("  PASS  {}{}", c.path, tag),
            Outcome::Fail { expected, got } => {
                println!("  FAIL  {} — expected {expected}, got {got}{tag}", c.path)
            }
            Outcome::Error(msg) => println!("  ERROR {} — {msg}{tag}", c.path),
        }
    }
    println!(
        "\n{} passed, {} failed, {} errored, {} cached  in {:.1}ms ({} job{})",
        report.passed(),
        report.failed(),
        report.errored(),
        report.cached(),
        report.wall_micros as f64 / 1000.0,
        report.jobs,
        if report.jobs == 1 { "" } else { "s" },
    );
    if !report.all_passed() {
        process::exit(1);
    }
}

/// Default parallelism = available CPUs (1 if the count is unavailable).
fn default_jobs() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

/// Where re-run results persist: `$DNX_TEST_CACHE`, else `$HOME/.cache/dnx/test`,
/// else a temp dir. A failure to open the cache is fatal (the user asked for it).
fn open_test_cache() -> DiskResultCache {
    let dir = std::env::var_os("DNX_TEST_CACHE")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache/dnx/test")))
        .unwrap_or_else(|| std::env::temp_dir().join("dnx-test-cache"));
    DiskResultCache::open(&dir).unwrap_or_else(|e| die(format!("test cache {dir:?}: {e}")))
}

// ── build ─────────────────────────────────────────────────────────────────

/// `dnx build -f PATH` (a .nix file evaluating to a derivation attrset),
/// `dnx build .#ATTR` (resolve a flake output), or `dnx build EXPR` (an inline
/// Nix expression evaluating to a derivation attrset). Evaluates to a
/// derivation attrset, realizes it, and prints the resulting store path(s).
fn cmd_build(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx build [-f PATH | .#ATTR | EXPR]\n\
             \n\
             Build a derivation and print its store path(s).\n\
             -f PATH   evaluate the .nix file at PATH to a derivation\n\
             .#ATTR    resolve a flake output attribute\n\
             EXPR      evaluate an inline Nix expression to a derivation",
        );
    }
    let result = match args.first().map(String::as_str) {
        Some("-f") | Some("--file") => match args.get(1) {
            Some(path) => NixRuntime::pure().eval_file(Path::new(path)),
            None => die("build -f requires a path"),
        },
        Some(arg) if arg.starts_with(".#") => resolve_flake_attr(&arg[2..]),
        // Inline expression: everything else is joined and evaluated as Nix
        // (mirrors `dnx eval EXPR`), then realized like the file/flake forms.
        Some(_) => NixRuntime::pure().eval(&args.join(" ")),
        None => die("build: expected `-f PATH`, `.#ATTR`, or an inline EXPR"),
    };

    let attrs = match result {
        NixEvalResult::AttrSet(kvs) => kvs,
        NixEvalResult::Error(e) => die(e),
        other => die(format!(
            "build: expression must evaluate to a derivation attrset, got {}",
            kind_of(&other)
        )),
    };

    let drv: Derivation = from_attrs(&attrs).unwrap_or_else(|e| die(e));
    let store = Store::open().unwrap_or_else(|e| die(e));
    let outputs = drv.realize(&store).unwrap_or_else(|e| die(e));
    for (_name, path) in outputs {
        println!("{path}");
    }
}

fn resolve_flake_attr(attr: &str) -> NixEvalResult {
    let flake = Flake::load(Path::new(".")).unwrap_or_else(|e| die(e));
    flake.resolve_attr(attr).unwrap_or_else(|e| die(e))
}

fn kind_of(r: &NixEvalResult) -> &'static str {
    match r {
        NixEvalResult::Int(_) => "int",
        NixEvalResult::Float(_) => "float",
        NixEvalResult::Str(_) => "string",
        NixEvalResult::Bool(_) => "bool",
        NixEvalResult::Null => "null",
        NixEvalResult::List(_) => "list",
        NixEvalResult::AttrSet(_) => "set",
        NixEvalResult::Lambda(_) => "lambda",
        NixEvalResult::Error(_) => "error",
    }
}

// ── flake ─────────────────────────────────────────────────────────────────

/// `dnx flake show [PATH]` — evaluate `<PATH>/flake.nix` (or `PATH` if it is the
/// file itself; default `.`) and list each output: a derivation leaf with its
/// drvPath, a plain value with its type, or the eval-seam reason it is
/// unresolved. `dnx flake check [PATH]` evaluates the same and exits nonzero if
/// any output is unresolved.
fn cmd_flake(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx flake {show|check|lock|metadata} [PATH]\n\
             \n\
             show      list a flake's outputs (PATH is a dir or flake.nix; default .)\n\
             check     evaluate all outputs; nonzero exit on any unresolved output\n\
             lock      pin every declared input by content hash; write flake.lock\n\
             metadata  print the flake's description, inputs, and lock status",
        );
    }
    match args.first().map(String::as_str) {
        Some("show") => flake_report(flake_path(&args[1..]), false),
        Some("check") => flake_report(flake_path(&args[1..]), true),
        Some("lock") => flake_lock(flake_path(&args[1..])),
        Some("metadata") => flake_metadata(flake_path(&args[1..])),
        Some(sub) => die(format!(
            "flake: unknown subcommand {sub:?} (try `flake show` / `flake check` / `flake lock` / `flake metadata`)"
        )),
        None => die("flake: expected a subcommand (try `flake show` / `flake check` / `flake lock` / `flake metadata`)"),
    }
}

/// `dnx flake metadata [PATH]` — print the flake's declared `description`, its
/// inputs (name → local-path url), and the on-disk `flake.lock` status. A pure
/// surface read; nothing is evaluated or written.
fn flake_metadata(path: &Path) {
    let flake = Flake::load(path).unwrap_or_else(|e| die(e));
    let description = flake.description().unwrap_or_else(|e| die(e));
    println!(
        "description: {}",
        description.as_deref().unwrap_or("(none)")
    );
    let inputs = flake.inputs().unwrap_or_else(|e| die(e));
    if inputs.entries().is_empty() {
        println!("inputs: (none)");
    } else {
        println!("inputs:");
        for input in inputs.entries() {
            println!("  {} -> {}", input.name(), input.url());
        }
    }
    let status = match flake.lock_status().unwrap_or_else(|e| die(e)) {
        LockStatus::Absent => "absent (run `dnx flake lock`)",
        LockStatus::UpToDate => "up to date",
        LockStatus::Stale => "stale (run `dnx flake lock`)",
    };
    println!("lock: {status}");
}

/// `dnx flake lock [PATH]` — resolve every declared input and pin it by content
/// hash, writing `flake.lock` (our flat format) next to the flake's `flake.nix`.
fn flake_lock(path: &Path) {
    let flake = Flake::load(path).unwrap_or_else(|e| die(e));
    let lock = flake.lock().unwrap_or_else(|e| die(e));
    let dir = if path.is_dir() {
        path.to_path_buf()
    } else {
        path.parent().map(Path::to_path_buf).unwrap_or_default()
    };
    let out = dir.join("flake.lock");
    std::fs::write(&out, lock.to_text()).unwrap_or_else(|e| die(format!("{}: {e}", out.display())));
    println!("wrote {} ({} inputs)", out.display(), lock.entries().len());
}

/// The flake directory-or-file argument (default `.`); rejects extra args.
fn flake_path(args: &[String]) -> &Path {
    match args {
        [] => Path::new("."),
        [p] => Path::new(p),
        _ => die("flake: expected at most one PATH (a directory or a flake.nix)"),
    }
}

/// Evaluate every output of the flake at `path` and print the report. When
/// `gate` (the `check` mode), exit nonzero if any output is unresolved.
fn flake_report(path: &Path, gate: bool) {
    let flake = Flake::load(path).unwrap_or_else(|e| die(e));
    let store = Store::open().unwrap_or_else(|e| die(e));
    let report = flake.report(&store).unwrap_or_else(|e| die(e));
    for (attr, kind) in report.entries() {
        match kind {
            OutputKind::Derivation { drv_path } => println!("{attr} = derivation {drv_path}"),
            OutputKind::Value { kind } => println!("{attr} = {kind}"),
            OutputKind::Unresolved { reason } => println!("{attr} = unresolved ({reason})"),
        }
    }
    if gate && !report.ok() {
        process::exit(1);
    }
}

// ── store ─────────────────────────────────────────────────────────────────

/// `dnx store add PATH` (capture a file/dir into the store) and
/// `dnx store path PATH` (predict the store path without writing).
fn cmd_store(args: &[String]) {
    if wants_help(args) {
        help(
            "usage: dnx store {add|path} PATH\n\
             \n\
             add   capture a file/dir into the store and print its store path\n\
             path  print the store path PATH would get, without writing it",
        );
    }
    match args.first().map(String::as_str) {
        Some("add") => {
            let path = args
                .get(1)
                .unwrap_or_else(|| die("store add requires a PATH"));
            let store = Store::open().unwrap_or_else(|e| die(e));
            let sp = add_path(&store, Path::new(path));
            println!("{sp}");
        }
        Some("path") => {
            // Predict the path by adding to an isolated temp store, so no global
            // state is mutated by a query. The hash is content-addressed, so the
            // path component is identical to what `store add` would produce.
            let path = args
                .get(1)
                .unwrap_or_else(|| die("store path requires a PATH"));
            let tmp = std::env::temp_dir().join(format!("dnx-store-path-{}", std::process::id()));
            let store = Store::open_at(&tmp).unwrap_or_else(|e| die(e));
            let sp = add_path(&store, Path::new(path));
            let _ = std::fs::remove_dir_all(&tmp);
            println!("{sp}");
        }
        Some(sub) => die(format!(
            "store: unknown subcommand {sub:?} (try `add` / `path`)"
        )),
        None => die("store: expected a subcommand (try `add` / `path`)"),
    }
}

fn add_path(store: &Store, path: &Path) -> dnx_store::StorePath {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or_else(|| die(format!("store: path {path:?} has no file name")));
    let meta = std::fs::metadata(path).unwrap_or_else(|e| die(e));
    if meta.is_dir() {
        store.add_tree(name, path).unwrap_or_else(|e| die(e))
    } else {
        let bytes = std::fs::read(path).unwrap_or_else(|e| die(e));
        store.add(name, &bytes).unwrap_or_else(|e| die(e))
    }
}

#[cfg(test)]
mod tests {
    use super::fmt_float;

    /// Oracle: each expected string was produced by real cppNix
    /// (`nix eval --expr '<lit>'`) for the matching literal, so `fmt_float`
    /// reproduces the reference value printer (`%.6g`) exactly.
    #[test]
    fn float_renders_like_cpp_nix() {
        let cases = [
            (3.0, "3"),
            (0.0, "0"),
            (10.0, "10"),
            (1.5, "1.5"),
            (1.6, "1.6"),
            (2.5, "2.5"),
            (2000.0, "2000"),
            (123456.0, "123456"),
            (999999.0, "999999"),
            (0.0001, "0.0001"),
            (0.000001, "1e-06"),
            (0.00001, "1e-05"),
            (1000000.0, "1e+06"),
            (1234567.0, "1.23457e+06"),
            (9999999.0, "1e+07"),
            (12345678.0, "1.23457e+07"),
            (100000000.0, "1e+08"),
            (1.0e20, "1e+20"),
        ];
        for (x, want) in cases {
            assert_eq!(fmt_float(x), want, "fmt_float({x})");
        }
    }

    #[test]
    fn negative_floats_match_cpp_nix() {
        assert_eq!(fmt_float(-1.5), "-1.5");
        assert_eq!(fmt_float(-1000000.0), "-1e+06");
        assert_eq!(fmt_float(-3.0), "-3");
    }
}
