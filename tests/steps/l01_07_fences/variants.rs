//! Item VARIANT-sync: a variant fixture agrees with its fence when it is the fence with one
//! commented ✗ line made live and no other difference but the changes the test names.

use zed_tests::fences::{Change, DocFence, Variant, disagreements};

fn fence(at: &str, text: &str) -> DocFence {
    DocFence {
        key: at.into(),
        at: at.into(),
        layer: 1,
        ring: 1,
        notation: false,
        text: text.into(),
    }
}

fn variant(name: &str, text: &str) -> Variant {
    Variant {
        name: name.into(),
        of: text
            .lines()
            .next()
            .and_then(|l| l.strip_prefix("// variant: "))
            .expect("a `// variant:` line")
            .into(),
        text: text.into(),
    }
}

const FENCE: &str = "a = 1;\n// b = a + x;   // ✗ no x\nc = 2;";
const HEAD: &str = "// variant: // b = a + x;   // ✗ no x\n";

fn check(fixture: &str, changes: &[Change]) -> Vec<String> {
    disagreements(
        &[fence("DESIGN.md:10", FENCE)],
        &[variant("v", &format!("{HEAD}{fixture}"))],
        changes,
    )
}

#[test]
fn the_fence_with_its_line_made_live_agrees() {
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x\nc = 2;\n", &[]),
        [""; 0]
    );
    // The live line is compared with runs of white space as one space, and it may keep the
    // indentation of the commented line.
    assert_eq!(
        check("a = 1;\n  b = a +  x; // ✗ no x\nc = 2;", &[]),
        [""; 0]
    );
}

#[test]
fn any_other_line_must_be_the_fences_as_written() {
    assert_eq!(
        check("a  = 1;\nb = a + x;   // ✗ no x\nc = 2;", &[]),
        ["v.zed:2: `a  = 1;` where the fence's line 1 is: `a = 1;`; its fence is at DESIGN.md:10"]
    );
}

#[test]
fn a_fixture_whose_fence_changed_disagrees() {
    // The fence's other line was edited, the fence gained a line, the fixture has a line the
    // fence lacks, and the live line differs from the commented one.
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x\nc = 3;", &[]),
        ["v.zed:4: `c = 3;` where the fence's line 3 is: `c = 2;`; its fence is at DESIGN.md:10"]
    );
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x", &[]),
        [
            "v.zed:4: the file ends where the fence's line 3 is: `c = 2;`; its fence is at \
          DESIGN.md:10"
        ]
    );
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x\nc = 2;\nd = 4;", &[]),
        ["v.zed:5: `d = 4;` after the fence's last line; its fence is at DESIGN.md:10"]
    );
    assert_eq!(
        check("a = 1;\nb = a + y;   // ✗ no x\nc = 2;", &[]),
        [
            "v.zed:3: the fence's line 2 made live belongs here: b = a + x;   // ✗ no x; its \
          fence is at DESIGN.md:10"
        ]
    );
}

#[test]
fn the_live_line_takes_the_place_of_the_commented_one() {
    assert_eq!(
        check("a = 1;\nc = 2;\nb = a + x;   // ✗ no x", &[]),
        [
            "v.zed:3: the fence's line 2 made live belongs here: b = a + x;   // ✗ no x; its \
          fence is at DESIGN.md:10"
        ]
    );
}

#[test]
fn a_fixture_leaves_out_only_the_lines_the_test_names() {
    let omits = [Change::Omits {
        fixture: "v",
        line: "a = 1;",
    }];
    assert_eq!(check("b = a + x;   // ✗ no x\nc = 2;", &omits), [""; 0]);
    assert_eq!(
        check("b = a + x;   // ✗ no x\nc = 2;", &[]),
        [
            "v.zed:2: `b = a + x;   // ✗ no x` where the fence's line 1 is: `a = 1;`; its fence \
             is at DESIGN.md:10"
        ]
    );
    // A change the fixture does not use is named, and so is one for another fixture.
    let unused = format!("v.zed does not use the change {:?}", omits[0]);
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x\nc = 2;", &omits),
        [unused]
    );
    let elsewhere = [Change::Omits {
        fixture: "w",
        line: "a = 1;",
    }];
    let none = format!("no fixture has the change {:?}", elsewhere[0]);
    assert_eq!(
        check("a = 1;\nb = a + x;   // ✗ no x\nc = 2;", &elsewhere),
        [none]
    );
}

#[test]
fn a_line_that_stands_for_another_may_make_the_variant() {
    // The commented line names an edit of the declaration above it: the fixture makes that
    // edit live and keeps the commented line.
    let fence_text = "s = { n: int | #none };\n// n: int   // ✗ #none is missing\nt = 1;";
    let fixture = "// variant: // n: int   // ✗ #none is missing\n\
                   s = { n: int };   // ✗ #none is missing\n// n: int   // ✗ #none is missing\n\
                   t = 1;\n";
    let stands = [Change::Stands {
        fixture: "v",
        line: "s = { n: int };   // ✗ #none is missing",
        stands_for: "s = { n: int | #none };",
    }];
    let run = |changes: &[Change]| {
        disagreements(
            &[fence("DESIGN.md:5", fence_text)],
            &[variant("v", fixture)],
            changes,
        )
    };
    assert_eq!(run(&stands), [""; 0]);
    assert_eq!(
        run(&[]),
        [
            "v.zed:2: `s = { n: int };   // ✗ #none is missing` where the fence's line 1 is: \
             `s = { n: int | #none };`; its fence is at DESIGN.md:5"
        ]
    );
}

#[test]
fn two_fences_with_one_commented_line_need_a_fixture_each() {
    let fences = [
        fence("DESIGN.md:10", FENCE),
        fence("EXAMPLES.md:20", "// b = a + x;   // ✗ no x\nd = 4;"),
    ];
    let of_design = variant(
        "v1",
        &format!("{HEAD}a = 1;\nb = a + x;   // ✗ no x\nc = 2;"),
    );
    let of_examples = variant("v2", &format!("{HEAD}b = a + x;   // ✗ no x\nd = 4;"));
    let copy = variant(
        "v2",
        &format!("{HEAD}a = 1;\nb = a + x;   // ✗ no x\nc = 2;"),
    );
    assert_eq!(
        disagreements(&fences, &[of_design.clone(), of_examples], &[]),
        [""; 0]
    );
    assert_eq!(
        disagreements(&fences, &[of_design, copy], &[]),
        [
            "EXAMPLES.md:20: no fixture agrees with the fence's commented ✗ line 1: // b = a + x;   \
          // ✗ no x"
        ]
    );
}

#[test]
fn a_fixture_must_name_one_commented_line_and_make_one_line_live() {
    let fences = [fence("DESIGN.md:10", FENCE)];
    let other = variant(
        "w",
        "// variant: // b = a + y;   // ✗ no y\nb = a + y;   // ✗ no y\n",
    );
    let two = variant(
        "v",
        &format!("{HEAD}a = 1;   // ✗ also\nb = a + x;   // ✗ no x\nc = 2;"),
    );
    assert_eq!(
        disagreements(&fences, &[other, two], &[]),
        [
            "v.zed has 2 live ✗ lines, not one",
            "w.zed: its `// variant:` line is the commented ✗ line of no fence: // b = a + y;   \
             // ✗ no y",
        ]
    );
}
