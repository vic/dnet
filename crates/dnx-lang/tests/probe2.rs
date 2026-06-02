use dnx_lang::runtime::{NixEvalResult, NixRuntime};
#[test]
fn probe() {
    let rt = NixRuntime::pure();
    let tag = |r: NixEvalResult| match r {
        NixEvalResult::Int(n) => format!("Int({n})"),
        NixEvalResult::Str(s) => format!("Str({s})"),
        NixEvalResult::Lambda(_) => "Lambda".into(),
        NixEvalResult::Error(e) => format!("Error({e:?})"),
        _ => "other".into(),
    };
    for e in [
        "length [1]",
        "length [1 2]",
        "length [1 2 3]",
        "foldl' (a: b: a + b) 0 [1]",
        "foldl' (a: b: a + b) 0 [1 2]",
        "head (map (x: x + 1) [10])",
        "elem 2 [1 2]",
    ] {
        eprintln!("P2 [{e}] => {}", tag(rt.eval(e)));
    }
}
