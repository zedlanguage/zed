//! Completeness of the unit item `@log(#off);` (plan row TEST-complete-ports, COMPLETENESS.md
//! beside this file): each place in a unit it may stand and each place it may not.

use super::resolved;

#[test]
fn the_unit_item_is_recorded_wherever_it_stands_at_the_top_level() {
    let item = "@log(#off);";
    let cases = [
        ("alone", "@log(#off);\n".to_string()),
        ("alone_without_a_line_end", "@log(#off);".to_string()),
        ("first", "@log(#off);\nf(x) = x;\n".to_string()),
        (
            "last_without_a_line_end",
            "f(x) = x;\n@log(#off);".to_string(),
        ),
        (
            "between_two_functions",
            "f(x) = x;\n@log(#off);\ng(x) = x;\n".to_string(),
        ),
        (
            "on_the_line_of_a_function",
            "@log(#off); f(x) = x;\n".to_string(),
        ),
        (
            "after_a_comment",
            "// quiet\n@log(#off);\nf(x) = x;\n".to_string(),
        ),
        (
            "before_main",
            "@log(#off);\nmain(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n".to_string(),
        ),
        (
            "after_a_test_table",
            "f(x: int) = x test { 1 -> 1 }\n@log(#off);\n".to_string(),
        ),
    ];
    let mut wrong = Vec::new();
    for (name, text) in &cases {
        let start = text.find(item).unwrap();
        match resolved(text) {
            Ok(r) => {
                let got = r.log_off.map(|s| (s.start, s.end));
                if got != Some((start, start + item.len())) {
                    wrong.push(format!("{name}: recorded {got:?}"));
                }
            }
            Err(e) => wrong.push(format!("{name}: refused {e:?}")),
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn the_unit_item_in_any_block_is_refused_at_its_place() {
    let want = |at: &str| {
        format!(
            "{at}: `@log(#off);` is an item of a unit and stands at its top level, not in a \
             block; write `@log(#off)` before a function's declaration to drop the lines of \
             its body"
        )
    };
    for (text, at) in [
        ("main(m: MainArgs) {\n  @log(#off);\n}\n", "2:3"),
        ("f(x: int) {\n  y = x;\n  @log(#off);\n  y\n}\n", "3:3"),
        (
            "f(x: int) {\n  if x > 0 {\n    @log(#off);\n    1\n  } else {\n    2\n  }\n}\n",
            "3:5",
        ),
    ] {
        assert_eq!(resolved(text).err(), Some(vec![want(at)]), "{text:?}");
    }
}
