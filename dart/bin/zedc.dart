/// The `zedc` command: `zedc fmt <file>` writes the file in the formatter's layout to standard
/// output; with no arguments it prints its version.
library;

import 'dart:io';

import 'package:zed/format.dart';

void main(List<String> args) {
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
    default:
      stderr.writeln('usage: zedc [fmt <file>]');
      exitCode = 2;
  }
}
