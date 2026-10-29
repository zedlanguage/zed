use super::check;

#[test]
fn a_push_sends_the_whole_value_to_its_port() {
    check(&[(
        "main(stdin: Lines) -> (stdout: Lines) { n = count(stdin); stdout <- n; }",
        "(def main ((stdin: Lines)) (-> (stdout: Lines)) \
         (block (= (n) (call count stdin)) (<- stdout n)))",
    )]);
}
