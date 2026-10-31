/// A push sends the whole value to its port.
library;

import 'package:test/test.dart';

import 'sx.dart';

void main() {
  test('a push sends the whole value to its port', () {
    check([
      (
        'main(stdin: Lines) -> (stdout: Lines) { n = count(stdin); stdout <- n; }',
        '(def main ((stdin: Lines)) (-> (stdout: Lines)) '
            '(block (= (n) (call count stdin)) (<- stdout n)))',
      ),
    ]);
  });
}
