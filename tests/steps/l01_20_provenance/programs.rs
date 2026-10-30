//! Provenance of whole programs with ports, through `Program::provenance`.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Lookup, Value};
use zedc::run::load;

use super::origins;

/// A `Files` port holding `files`; every other path is `#notFound`.
#[derive(Debug)]
struct Disk(BTreeMap<&'static str, &'static str>);

impl Lookup for Disk {
    fn get(&self, key: &Value) -> Result<Value, String> {
        Ok(match key {
            Value::Str(k) => self
                .0
                .get(k.as_ref())
                .map_or(Value::atom("notFound"), |v| Value::str(v)),
            _ => Value::atom("notFound"),
        })
    }
}

fn trace(src: &str, stdin: &str, files: &[(&'static str, &'static str)]) -> zed_kernel::Provenance {
    let p = load(src.as_bytes()).unwrap();
    let mut lines = BTreeMap::new();
    lines.insert("stdin".to_string(), stdin.as_bytes().to_vec());
    let disk: Arc<dyn Lookup> = Arc::new(Disk(files.iter().copied().collect()));
    let (_, prov) = p.provenance(&lines, |_| disk.clone()).unwrap();
    assert!(prov.repeated().is_empty(), "{:?}", prov.repeated());
    prov
}

#[test]
fn a_failed_total_names_the_bad_quantity_and_the_missing_price_file() {
    let src = "main(stdin: Lines, fs: Files) -> (stdout: Lines) {\n  \
               qty = int(stdin[1]);\n  unit = int(fs[\"price.txt\"]);\n  \
               total = qty * unit;\n  stdout <- String(total) else \"no total\";\n}\n";
    let p = trace(src, "three\n", &[]);
    let i = p
        .facts()
        .iter()
        .rposition(|f| f.value.as_ref().is_some_and(|v| v.errs().is_some()))
        .expect("the merged failure");
    let o = origins(&p, i);
    assert_eq!(
        o,
        [
            ("fs(\"price.txt\")".into(), "#notFound".into()),
            ("int(tupleGet(stdin, 1))".into(), "#invalid".into()),
        ]
    );
}

#[test]
fn every_keypath_of_a_wave_starts_with_its_stamp() {
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  \
               stdout <- \"${int(stdin[1]) else 0}\";\n}\n";
    let p = trace(src, "4\n", &[]);
    assert!(
        p.facts()
            .iter()
            .all(|f| f.address.keypath.front() == Some(&Value::Int(0)))
    );
}
