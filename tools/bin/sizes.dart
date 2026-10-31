/// Rewrites the "Code size per file" table of RUST_VS_ZED.md: the bytes of every tracked Rust
/// file and, once ported, of the Dart files tools/dart_map.txt pairs with it.
///
/// dart_map.txt has one line per Dart file: `<dart path> <rust path>`, both relative to
/// zed-impl. Several Dart files may port one Rust file; their sizes add up in its row.
///
/// Usage: dart tools/bin/sizes.dart
library;

import 'dart:io';

void main() {
  final impl = File.fromUri(Platform.script).parent.parent.parent.path;
  final ls = Process.runSync('git', ['ls-files', '*.rs'], workingDirectory: impl);
  if (ls.exitCode != 0) throw StateError('git ls-files: ${ls.stderr}');
  final rust = (ls.stdout as String).split(RegExp(r'\s+')).where((s) => s.isNotEmpty).toList()
    ..sort();
  final known = rust.toSet();
  final dart = <String, List<String>>{};
  for (final line in File('$impl/tools/dart_map.txt').readAsLinesSync()) {
    if (line.trim().isEmpty || line.startsWith('#')) continue;
    final [d, r] = line.trim().split(RegExp(r'\s+'));
    if (!known.contains(r)) {
      stderr.writeln('dart_map.txt: no Rust file $r');
      exit(1);
    }
    (dart[r] ??= []).add(d);
  }

  int size(String p) => File('$impl/$p').lengthSync();
  final rows = <String>[];
  var rTotal = 0, dTotal = 0, rPorted = 0;
  for (final r in rust) {
    final rb = size(r);
    rTotal += rb;
    final ds = dart[r] ?? const [];
    if (ds.isEmpty) {
      rows.add('| `$r` | ${_grouped(rb)} | | | |');
      continue;
    }
    final db = ds.map(size).reduce((a, b) => a + b);
    dTotal += db;
    rPorted += rb;
    final names = ds.map((d) => '`${d.replaceFirst(RegExp('^dart/'), '')}`').join('<br>');
    rows.add('| `$r` | ${_grouped(rb)} | $names | ${_grouped(db)} | ${_ratio(db, rb)} |');
  }

  final ratio = rPorted > 0 ? _ratio(dTotal, rPorted) : '';
  final table = [
    '| Rust file | bytes | Dart files | bytes | Dart / Rust |',
    '|---|---:|---|---:|---:|',
    ...rows,
    '| **all ${rust.length} Rust files** | **${_grouped(rTotal)}** | | | |',
    '| **the Rust files ported so far** | **${_grouped(rPorted)}** | | '
        '**${_grouped(dTotal)}** | **$ratio** |',
  ].join('\n');
  final doc = File('$impl/RUST_VS_ZED.md');
  final block = RegExp(r'(<!-- sizes -->\n)(?:.*?\n)?(<!-- /sizes -->)', dotAll: true);
  final text = doc.readAsStringSync();
  if (block.allMatches(text).length != 1) {
    stderr.writeln('RUST_VS_ZED.md: no <!-- sizes --> block');
    exit(1);
  }
  doc.writeAsStringSync(text.replaceFirstMapped(block, (m) => '${m[1]}$table\n${m[2]}'));
  print(
    '${rust.length} Rust files, ${_grouped(rTotal)} bytes; '
    'ported ${_grouped(rPorted)} -> Dart ${_grouped(dTotal)}',
  );
}

/// `n` with commas between groups of three digits.
String _grouped(int n) => n.toString().replaceAllMapped(RegExp(r'\B(?=(\d{3})+$)'), (_) => ',');

/// `a / b` to two decimals, rounded half to even.
String _ratio(int a, int b) {
  var q = a * 100 ~/ b;
  final twice = 2 * (a * 100 % b);
  if (twice > b || (twice == b && q.isOdd)) q++;
  return '${q ~/ 100}.${(q % 100).toString().padLeft(2, '0')}';
}
