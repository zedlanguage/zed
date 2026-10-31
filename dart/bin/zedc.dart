/// The `zedc` command: `zedc fmt <file>` writes the file in the formatter's layout to standard
/// output; `zedc run` and `zedc replay` run a program (`command` of `package:zed/run.dart`);
/// with no arguments it prints its version.
library;

import 'dart:io';
import 'dart:typed_data';

import 'package:zed/format.dart';
import 'package:zed/run.dart';

Future<void> main(List<String> args) async {
  switch (args) {
    case []:
      print('zedc 0.0.0');
    case ['fmt', final file]:
      try {
        stdout.write(formatSource(File(file).readAsBytesSync()));
      } on Exception catch (e) {
        stderr.writeln('$file:${e is FileSystemException ? e.message : e}');
        exitCode = 1;
      }
    case ['run' || 'replay', ...]:
      exitCode = await command(
        args,
        () => stdin.fold(BytesBuilder(copy: false), (b, d) => b..add(d)).then((b) => b.takeBytes()),
        stdout.add,
        stderr.add,
      );
    default:
      stderr.writeln('usage: zedc [fmt <file> | run <file> … | replay <file> <record> …]');
      exitCode = 2;
  }
}
