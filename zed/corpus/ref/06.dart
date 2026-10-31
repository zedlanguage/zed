/// 06 matrix multiply. Zed rules used: each product x * y is one IEEE multiplication; the `+`
/// reduction over a float family is the exact sum rounded once (fsum); floats print by
/// zedrt.fmt. Every line, the header "n m p" included, must read as floats; the row ranges
/// are taken as Python slices (clamped, negative bounds counted from the end).
library;

import 'zedrt.dart';

List<T> slice<T>(List<T> xs, BigInt start, BigInt stop) {
  final len = BigInt.from(xs.length);
  int bound(BigInt i) {
    final j = i.isNegative ? i + len : i;
    return j.isNegative ? 0 : (j > len ? len : j).toInt();
  }

  final (a, b) = (bound(start), bound(stop));
  return a < b ? xs.sublist(a, b) : [];
}

void main(List<String> args) {
  final lines = readLines(args[0]);
  final rows = [
    for (final l in lines) [for (final t in l.split(' ')) parseFloat(t)],
  ];
  final [n, m, p] = [for (final t in lines[0].split(' ')) parseInt(t)];
  final a = slice(rows, BigInt.one, BigInt.one + n);
  final b = slice(rows, BigInt.one + n, BigInt.one + n + m);
  final (mi, pi) = (m.toInt(), p.toInt());
  for (final row in a) {
    print(
      [
        for (var k = 0; k < pi; k++) fmt(fsum([for (var c = 0; c < mi; c++) row[c] * b[c][k]])),
      ].join(' '),
    );
  }
}
