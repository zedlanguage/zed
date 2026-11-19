use super::check;
use zedc::query::Db;
use zedc::rejection::Row;

#[test]
fn a_push_sends_the_whole_value_to_its_port() {
    check(&[(
        "main(m: MainArgs) { n = count(m.stdin); m.stdout <- n; }",
        "(def main ((m.stdin: Lines)) (-> (m.stdout: Lines)) \
         (block (= (n) (call count m.stdin)) (<- m.stdout n)))",
    )]);
}

/// `main`'s body `body`, one statement per line, indented, followed by a push to `m.stdout`
/// so that the program has an output.
fn main_with(body: &str) -> String {
    format!("main(m: MainArgs) {{\n  {body}\n  m.stdout <- \"b\";\n}}\n")
}

/// What the front end makes of `src`: `accepted`, `later` when the first diagnostic says the
/// form is not compiled yet, or the first diagnostic's row, place, headline and first repair.
fn front(src: &str) -> String {
    match &*Db::new().front(src) {
        Ok(_) => "accepted".into(),
        Err(ds) => {
            let d = &ds[0];
            if d.message.ends_with(zed_tests::not_yet!("")) && d.row.is_none() {
                return "later".into();
            }
            let repair = d.steps.iter().find_map(|s| s.text.strip_prefix("repair: "));
            format!(
                "{} {}:{}: {} | {}",
                d.row.map_or("no row", Row::name),
                d.line,
                d.col,
                d.message,
                repair.unwrap_or("none")
            )
        }
    }
}

#[track_caller]
fn fronts(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(src, want)| {
            let got = front(src);
            (got != want).then(|| format!("{src}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The targets that take a push (DESIGN.md sec:ports, "What a push may name"): the outputs of
/// `main`, a parameter declared `Lines`, and the forms not compiled yet, which are refused as
/// such and never under a row: a view that takes a push, a keyed push into an accumulator, a
/// generation push in the body of a loop or of a method. These are the negative controls of
/// the refusals below, each one edit from one of them.
#[test]
fn a_push_to_a_port_an_accumulator_or_a_next_generation_is_not_refused() {
    fronts(&[
        (&main_with("m.stdout <- \"a\";"), "accepted"),
        (&main_with("m.stderr <- \"a\";"), "accepted"),
        (
            "say(positional s, out: Lines) { out <- s; }\n\
             main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n",
            "accepted",
        ),
        (&main_with("m.stdout::bytes <- \"a\";"), "later"),
        (&main_with("hist[1] <- 1;"), "later"),
        (
            "f(n: int) = loop { initial x = 0; x' <- x + 1; until x' >= n; }.x;\n",
            "later",
        ),
        // In a lambda or a `for` inside a loop's body, the push is a push of the loop
        // (sec:generations, "The body of a `for` runs once for each key").
        (
            "f(n: int) = loop { initial x = 0 with carryForward; g = () -> { x' <- x + 1; 0 }; \
             until x >= n; }.x;\n",
            "later",
        ),
        (
            "f(n: int) = loop { initial x = 0 with carryForward; _ = for i in 0..<1 { x' <- x + \
             1; 0 }; until x >= n; }.x;\n",
            "later",
        ),
        // A method writes its receiver's next value through primed fields.
        (
            "struct Counter { n: int }\nCounter.tick() { n' <- n + 1; }\n",
            "later",
        ),
    ]);
}

/// A name that is no port: a binding, a prelude word.
#[test]
fn a_push_to_a_name_that_is_not_a_port_is_refused() {
    fronts(&[
        (
            &main_with("x = \"a\";\n  x <- \"b\";"),
            "Push to a name that is not a port 3:3: Invalid push to `x`, a binding: a push goes \
             to a port or a declared accumulator. | `m.stdout <- …;` in `main`, or a parameter \
             declared `Lines` that `main` passes `m.stdout` to",
        ),
        (
            &main_with("len <- \"b\";"),
            "Push to a name that is not a port 2:3: Invalid push to `len`, a prelude word: a \
             push goes to a port or a declared accumulator. | `m.stdout <- …;` in `main`",
        ),
        (
            "say(positional s, out) { out <- s; }\n\
             main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n",
            "Push to a name that is not a port 1:26: Invalid push to `out`, a parameter of `say` \
             not declared `Lines`. Try `out: Lines` instead. | `out: Lines`",
        ),
    ]);
}

/// An input of the program, with or without a view.
#[test]
fn a_push_to_an_input_is_refused() {
    let input = |t: &str| {
        format!(
            "Push to an input or a read view 2:3: Invalid push to `{t}`: `m.{}` is an input of \
             the program, which `main` reads and never writes. | `m.stdout <- \"a\";`",
            t.trim_start_matches("m.").split("::").next().unwrap()
        )
    };
    fronts(&[
        (&main_with("m.stdin <- \"a\";"), &input("m.stdin")),
        (&main_with("m.args <- \"a\";"), &input("m.args")),
        (&main_with("m.env <- \"a\";"), &input("m.env")),
        (
            &main_with("m.stdin::bytes <- \"a\";"),
            &input("m.stdin::bytes"),
        ),
    ]);
}

/// A view other than `::bytes`, the one view that takes a push.
#[test]
fn a_push_through_a_view_that_takes_no_push_is_refused() {
    let view = |t: &str, repair: &str| {
        format!(
            "Push to a view that takes no push 2:3: Invalid push to `{t}`: of the views, only \
             `::bytes` takes a push. | {repair}"
        )
    };
    fronts(&[
        (
            &main_with("m.stdout::len <- \"a\";"),
            &view("m.stdout::len", "`m.stdout <- \"a\";`"),
        ),
        (
            &main_with("m.stderr::frames <- \"a\";"),
            &view("m.stderr::frames", "`m.stderr <- \"a\";`"),
        ),
        (
            &main_with("m::stdout <- \"a\";"),
            &view("m::stdout", "`m.stdout <- \"a\";`"),
        ),
        (&main_with("m::len <- \"a\";"), &view("m::len", "none")),
        // A view that only reads is refused whatever it is a view of.
        (
            &main_with("x = 1;\n  x::len <- \"a\";"),
            "Push to a view that takes no push 3:3: Invalid push to `x::len`: of the views, only \
             `::bytes` takes a push. | none",
        ),
    ]);
}

/// A field `main`'s argument does not have.
#[test]
fn a_push_to_a_field_that_is_not_a_port_is_refused() {
    fronts(&[
        (
            &main_with("m.lines <- \"a\";"),
            "Push to a field that is not a port 2:3: Invalid push to `m.lines`: `m`, of type \
             `MainArgs`, has no field `lines`; its outputs are `m.stdout` and `m.stderr`. | \
             `m.stdout <- \"a\";`",
        ),
        (
            &main_with("m.lines::bytes <- \"a\";"),
            "Push to a field that is not a port 2:3: Invalid push to `m.lines::bytes`: `m`, of \
             type `MainArgs`, has no field `lines`; its outputs are `m.stdout` and `m.stderr`. | \
             `m.stdout <- \"a\";`",
        ),
        // A push to a field of another value is not compiled yet, so a field whose type is no
        // port is not refused yet either: plan row PORT-process refuses it with this row.
        (&main_with("r = { total: 1 };\n  r.total <- 1;"), "later"),
    ]);
}

/// `x' <- e` with no loop and no method around it, also in a lambda or a `for` outside a loop.
#[test]
fn a_generation_push_outside_a_loop_is_refused() {
    let outside = |at: &str, value: &str| {
        format!(
            "Generation push outside a loop {at}: Invalid push to `x'` outside a loop: only the \
             body of a `loop`, or of a method for a field of its receiver, writes a next \
             generation. | `x = {value};`"
        )
    };
    fronts(&[
        (&main_with("x' <- \"a\";"), &outside("2:3", "\"a\"")),
        (
            "f(n: int) {\n  x' <- n + 1;\n}\nmain(m: MainArgs) {\n  m.stdout <- \"b\";\n}\n",
            &outside("2:3", "n + 1"),
        ),
        (
            &main_with("g = () -> { x' <- 1; 0 };"),
            &outside("2:15", "1"),
        ),
        (
            &main_with("_ = for i in 0..<1 { x' <- 1; 0 };"),
            &outside("2:24", "1"),
        ),
    ]);
}

/// The first diagnostic of `src` under a row, as [`front`] writes it, or what [`front`] gives
/// when none has a row: a method is not compiled yet, so a refusal in its body comes after the
/// method's own "not yet".
fn front_row(src: &str) -> String {
    let Err(ds) = &*Db::new().front(src) else {
        return "accepted".into();
    };
    let Some(d) = ds.iter().find(|d| d.row.is_some()) else {
        return front(src);
    };
    let repair = d.steps.iter().find_map(|s| s.text.strip_prefix("repair: "));
    format!(
        "{} {}:{}: {} | {}",
        d.row.map_or("no row", Row::name),
        d.line,
        d.col,
        d.message,
        repair.unwrap_or("none")
    )
}

/// `x' <- e` in a method's body for an `x` that is no field of the receiver: a struct of the
/// unit that has no field `x`, or a prelude type with no fields (DESIGN.md sec:ports, "What a
/// push may name"). The controls, each one edit from a refused case, are not refused: a push
/// to a field of the receiver, a push to `x'` in a `loop` that declares `x` inside the method,
/// and a receiver whose fields this step does not know, a struct that imports another's fields.
#[test]
fn a_generation_push_in_a_method_to_a_name_that_is_not_a_field_is_refused() {
    let refused = |at: &str, method: &str, why: &str, value: &str| {
        format!(
            "Generation push to a name that is not a field of the receiver {at}: Invalid push to \
             `x'` in the method `{method}`: {why}; a method writes the next generation of its \
             receiver's fields only. | `x = {value};`"
        )
    };
    let counter = "struct Counter { n: int, hi: int, step: int }\n";
    let cases = [
        (
            format!("{counter}Counter.tick() {{\n  x' <- n + 1;\n}}\n"),
            refused(
                "3:3",
                "Counter.tick",
                "`x` is not a field of `Counter`, whose fields are `n`, `hi` and `step`",
                "n + 1",
            ),
        ),
        (
            "struct One { n: int }\nOne.tick() {\n  x' <- n + 1;\n}\n".into(),
            refused(
                "3:3",
                "One.tick",
                "`x` is not a field of `One`, whose one field is `n`",
                "n + 1",
            ),
        ),
        // In a lambda in the method's body the push is still the method's.
        (
            format!("{counter}Counter.tick() {{\n  g = () -> {{ x' <- 1; 0 }};\n}}\n"),
            refused(
                "3:15",
                "Counter.tick",
                "`x` is not a field of `Counter`, whose fields are `n`, `hi` and `step`",
                "1",
            ),
        ),
        (
            "String.f(positional s) {\n  x' <- s;\n}\n".into(),
            refused("2:3", "String.f", "`String` has no fields", "s"),
        ),
        (
            "int.f() {\n  x' <- this + 1;\n}\n".into(),
            refused("2:3", "int.f", "`int` has no fields", "this + 1"),
        ),
        // The controls.
        (
            format!("{counter}Counter.tick() {{\n  n' <- n + 1;\n}}\n"),
            "later".into(),
        ),
        (
            format!(
                "{counter}Counter.tick() {{\n  r = loop {{ initial x = 0; x' <- x + 1; until \
                 x' >= 3; }}.x;\n}}\n"
            ),
            "later".into(),
        ),
        (
            "struct Base { n: int }\nstruct Wide { import Base, w: int }\nWide.tick() {\n  x' <- \
             n + 1;\n}\n"
                .into(),
            "later".into(),
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(src, want)| {
            let got = front_row(src);
            (&got != want).then(|| format!("{src}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A target the grammar does not allow stops the parse at the `<-`; the headline states the
/// shape of a target, a view and then keys (author P304).
#[test]
fn a_target_of_the_wrong_shape_names_the_shape() {
    let shape = |t: &str, at: &str| {
        format!(
            "Push to a target that cannot be pushed to {at}: Invalid push target `{t}`: a target \
             is a name and its fields, then at most one view, then its keys, as \
             `m.stdout::bytes <- b;` or `hist[k] <- 1;`. | none"
        )
    };
    fronts(&[
        (
            &main_with("m.stdout::bytes::len <- \"a\";"),
            &shape("m.stdout::bytes::len", "2:24"),
        ),
        (
            &main_with("m::stdout.bytes <- \"a\";"),
            &shape("m::stdout.bytes", "2:19"),
        ),
        // Keys after the view are in the shape: the keyed push is not compiled yet.
        (&main_with("fs::bytes[\"out\"] <- \"a\";"), "later"),
    ]);
}
