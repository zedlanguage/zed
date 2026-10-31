/// Step L1.19: whole-file ports. `main`'s header names the ports; each input is read once,
/// whole, each output written once when the wave ends, and a record of the inputs replays the
/// wave without the world.
library;

import 'dart:convert';
import 'dart:io';
import 'dart:typed_data';

import 'package:zed/run.dart';

import '../../support/support.dart';

/// A directory of its own for test `name`, under the package's build directory; files in it
/// are overwritten by each run, never deleted.
Directory dir(String name) =>
    Directory('${packageDir.path}/build/test_tmp/l01_19/$name')..createSync(recursive: true);

/// The outcome of a `zedc` command line: its status, standard output and standard error.
typedef Outcome = ({int status, String stdout, String stderr});

/// Runs `zedc <args>` with `stdin` as standard input.
Future<Outcome> zedc(List<String> args, String stdin) async {
  final out = BytesBuilder(), err = BytesBuilder();
  final status = await command(args, () async => utf8.encode(stdin), out.add, err.add);
  return (
    status: status,
    stdout: utf8.decode(out.takeBytes()),
    stderr: utf8.decode(err.takeBytes()),
  );
}

/// Writes program `src` as `prog.zed` in test directory `name` and runs it with `stdin` and
/// the extra arguments `more`.
Future<Outcome> run(String name, String src, String stdin, [List<String> more = const []]) {
  final prog = File('${dir(name).path}/prog.zed')..writeAsStringSync(src);
  return zedc(['run', prog.path, ...more], stdin);
}
