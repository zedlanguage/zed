/// 25 autocorrelation over the valid range i in 0..<n - l, lags 0..=3.
library;

import 'zedrt.dart';

void main(List<String> args) {
  final xs = [for (final x in readLines(args[0])[0].split(' ')) parseInt(x)];
  final n = xs.length;
  for (var l = 0; l < 4; l++) {
    var sum = BigInt.zero;
    for (var i = 0; i < n - l; i++) {
      sum += xs[i] * xs[i + l];
    }
    print('$l $sum');
  }
}
