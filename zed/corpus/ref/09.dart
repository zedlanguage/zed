/// 09 equality against a canonical form: lower-case, then remove '-' and ' '.
library;

import 'zedrt.dart';

String canon(String s) => lower(s).replaceAll('-', '').replaceAll(' ', '');

void main(List<String> args) {
  for (final line in readLines(args[0])) {
    final parts = line.split(' | ');
    final a = parts[0];
    final b = parts.length > 1 ? parts[1] : '';
    print('${canon(a) == canon(b) ? 'same: ' : 'different: '}$a | $b');
  }
}
