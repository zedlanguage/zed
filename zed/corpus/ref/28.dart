/// 28 precedence climbing (shunting-yard with the same pop rule) modulo 65536. Zed rule used:
/// mod is Euclidean, which for a positive modulus is Dart's %.
library;

import 'zedrt.dart';

const m = 65536;
const prec = {'+': 1, '-': 1, '*': 2, '^': 3};

int apply(String o, int a, int b) => switch (o) {
  '+' => (a + b) % m,
  '-' => (a - b) % m,
  '*' => (a * b) % m,
  _ => b > 0 ? a.modPow(b, m) : 1,
};

int ev(String l) {
  final vals = <int>[], ops = <String>[];
  void red() {
    final b = vals.removeLast(), a = vals.removeLast();
    vals.add(apply(ops.removeLast(), a, b));
  }

  for (final tok in l.split(' ')) {
    if (prec[tok] case final p?) {
      while (ops.isNotEmpty && (prec[ops.last]! > p || (prec[ops.last] == p && tok != '^'))) {
        red();
      }
      ops.add(tok);
    } else {
      vals.add((parseInt(tok) % BigInt.from(m)).toInt());
    }
  }
  while (ops.isNotEmpty) {
    red();
  }
  return vals[0];
}

void main(List<String> args) {
  for (final l in readLines(args[0])) {
    print('$l = ${ev(l)}');
  }
}
