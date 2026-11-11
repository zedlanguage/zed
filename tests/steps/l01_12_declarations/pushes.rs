use super::check;

#[test]
fn a_push_sends_the_whole_value_to_its_port() {
    check(&[(
        "main(m: MainArgs) { n = count(m.stdin); m.stdout <- n; }",
        "(def main ((m.stdin: Lines)) (-> (m.stdout: Lines)) \
         (block (= (n) (call count m.stdin)) (<- m.stdout n)))",
    )]);
}
