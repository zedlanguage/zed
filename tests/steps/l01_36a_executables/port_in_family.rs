//! A port read inside a family runs in an executable as under `zedc run` (DESIGN.md sec:ports:
//! `main::files` is read "from any function at any depth of calls", and Example 16 writes
//! `files.map(read)`).

use std::collections::BTreeMap;
use std::path::Path;

use rustix::fs::inotify;

use super::{Ran, built, dir, executable, interpreter};

/// The program of
/// `l01_19_whole_file_ports::outside::a_function_reading_main_files_runs_under_every_higher_order_form`,
/// each form and standard input read inside a `map`, built and run: the executable gives what
/// `zedc run` gives, status, output and errors.
#[test]
fn every_higher_order_form_reading_a_port_runs_in_an_executable_as_in_zedc_run() {
    let d = dir("port_in_family_forms");
    let (a, b) = (d.join("a.txt"), d.join("b.txt"));
    std::fs::write(&a, "A").unwrap();
    std::fs::write(&b, "B").unwrap();
    let names = format!(
        "[\"{}\", \"{}\", \"{}\"]",
        a.display(),
        b.display(),
        d.join("absent.txt").display()
    );
    let mut wrong = Vec::new();
    for (name, expr) in [
        ("where", "names.where(p -> text(p) != \"-\").map(text)"),
        ("foldl", "names.foldl(\"\", (acc, p) -> acc ++ text(p))"),
        ("nested_map", "[names, names].map(ns -> ns.map(text))"),
        ("lambda", "names.map(p -> main::files[p] else \"?\")"),
        ("chain", "names.map(loud)"),
        ("stdin", "[0, 1, 2].map(i -> m.stdin[i] else \"-\")"),
    ] {
        let src = d.join(format!("{name}.zed"));
        std::fs::write(
            &src,
            format!(
                "text(positional p: String) = main::files[p] else \"-\";\n\
                 loud(positional p: String) = text(p) ++ \"!\";\n\
                 main(m: MainArgs) {{\n  names = {names};\n  m.stdout <- \"${{{expr}}}\";\n}}\n"
            ),
        )
        .unwrap();
        let want = interpreter(&src, &[], b"x\ny\n");
        assert_eq!(want.status, 0, "{name}: {want:?}");
        let exe = d.join(name);
        built(&src, &exe);
        let got = executable(&exe, &[], b"x\ny\n");
        if got != want {
            wrong.push(format!("{name}: built {got:?}, zedc run {want:?}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The number of times each file in `dir` was opened, from the events of `watch`.
fn opens(watch: &rustix::fd::OwnedFd) -> BTreeMap<String, usize> {
    let mut buf = [std::mem::MaybeUninit::uninit(); 4096];
    let mut events = inotify::Reader::new(watch, &mut buf);
    let mut out = BTreeMap::new();
    loop {
        match events.next() {
            Ok(e) => {
                if let Some(name) = e.file_name() {
                    *out.entry(name.to_string_lossy().into_owned()).or_default() += 1;
                }
            }
            Err(rustix::io::Errno::AGAIN) => return out,
            Err(e) => panic!("reading the watch: {e}"),
        }
    }
}

/// A lookup port read inside families is asked once per distinct key in an executable, as in
/// `zedc run` (zed-kernel `Evaluator::ask_port`): each of two files, read at three elements of
/// a `map`, again in a second `map` and in a `map` inside a `map`, is opened once.
#[test]
fn a_lookup_port_read_in_families_is_asked_once_per_key_in_an_executable() {
    let d = dir("port_in_family_once");
    let data = d.join("data");
    std::fs::create_dir_all(&data).unwrap();
    let (a, b) = (data.join("a.txt"), data.join("b.txt"));
    std::fs::write(&a, "A").unwrap();
    std::fs::write(&b, "B").unwrap();
    let src = d.join("once.zed");
    std::fs::write(
        &src,
        format!(
            "text(positional p: String) = main::files[p] else \"-\";\n\
             main(m: MainArgs) {{\n  names = [\"{a}\", \"{b}\", \"{a}\", \"{a}\", \"{b}\", \"{a}\"];\n  \
             m.stdout <- \"${{names.map(text)}} ${{names.map(text)}} ${{[names].map(ns -> ns.map(text))}}\";\n}}\n",
            a = a.display(),
            b = b.display(),
        ),
    )
    .unwrap();
    let exe = d.join("once");
    built(&src, &exe);
    let watch =
        inotify::init(inotify::CreateFlags::NONBLOCK | inotify::CreateFlags::CLOEXEC).unwrap();
    inotify::add_watch(&watch, Path::new(&data), inotify::WatchFlags::OPEN).unwrap();
    let ran = executable(&exe, &[], b"");
    let row = "{0 -> \"A\", 1 -> \"B\", 2 -> \"A\", 3 -> \"A\", 4 -> \"B\", 5 -> \"A\"}";
    assert_eq!(
        ran,
        Ran {
            status: 0,
            stdout: format!("{row} {row} {{0 -> {row}}}\n"),
            stderr: String::new(),
        }
    );
    assert_eq!(
        opens(&watch),
        BTreeMap::from([("a.txt".to_string(), 1), ("b.txt".to_string(), 1)])
    );
}

/// The program of `l01_19_whole_file_ports::outside::a_function_given_to_map_reads_main_files`,
/// a function given to `map` that reads `main::files`, built and run: it prints what `zedc run`
/// prints for it, `{0 -> "A", 1 -> "B", 2 -> "-"}`.
#[test]
fn a_function_given_to_map_reads_main_files_in_an_executable() {
    let d = dir("port_in_family");
    let (a, b) = (d.join("a.txt"), d.join("b.txt"));
    std::fs::write(&a, "A").unwrap();
    std::fs::write(&b, "B").unwrap();
    let src = d.join("mapped_read.zed");
    std::fs::write(
        &src,
        format!(
            "text(p: String) = main::files[p] else \"-\";\n\
             main(m: MainArgs) {{\n  names = [\"{a}\", \"{b}\", \"{c}\"];\n  \
             m.stdout <- \"${{names.map(text)}}\";\n}}\n",
            a = a.display(),
            b = b.display(),
            c = d.join("absent.txt").display()
        ),
    )
    .unwrap();
    let exe = d.join("mapped_read");
    built(&src, &exe);
    assert_eq!(
        executable(&exe, &[], b""),
        Ran {
            status: 0,
            stdout: "{0 -> \"A\", 1 -> \"B\", 2 -> \"-\"}\n".into(),
            stderr: String::new(),
        }
    );
}
