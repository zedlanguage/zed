//! 20 taint demo, the fixed program: sanitize assumed to HTML-escape & < > " ' (as &amp; &lt;
//! &gt; &quot; &#39;), the corpus's stated assumption.

fn sanitize(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for l in lines {
        say!(out, "<li>{}</li>", sanitize(l));
    }
    Ok(())
}
