//! Every prelude source in `zed/prelude/` builds and formats: `zedc fmt` reads it, and what it
//! writes builds to the same statements, keeps its comments, and formats to itself. The prelude
//! is Zed source that later steps read, so a file the parser refuses is a defect found here
//! rather than by the step that first reads it (`axioms.zed` named a field `law`, a keyword).

use zedc::format::format_source;

#[test]
fn every_prelude_file_formats_to_a_fixed_point() {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/prelude");
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "zed") {
            files.push(path);
        }
    }
    files.sort();
    let mut failed = Vec::new();
    for path in &files {
        let bytes = std::fs::read(path).unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        match format_source(&bytes) {
            Err(e) => failed.push(format!("{name}:{e}")),
            Ok(out) => {
                let text = String::from_utf8(bytes).unwrap();
                let r = std::panic::catch_unwind(|| super::fmt(&text));
                match r {
                    Ok(same) if same == out => {}
                    Ok(_) => failed.push(format!("{name}: zedc fmt and the test differ")),
                    Err(_) => failed.push(format!("{name}: no fixed point (see the panic above)")),
                }
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    // Seven files when this test was written; later steps add more.
    assert!(files.len() >= 7, "{} prelude files", files.len());
}
