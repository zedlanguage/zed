/// Runs the Dart tests, each file in its own VM under a 60 s cap, several at a time, and prints
/// a line for each failure or timeout when it happens and the counts at the end.
///
/// `dart test` runs the build hooks in every process it starts, and the hooks rewrite
/// dart/.dart_tool/lib/libicu4x.so in place. A test process started beside another one can map
/// the library while it is being rewritten, and then dies of SIGBUS or fails to load icu4x.
/// This tool runs the hooks once and copies the library to
/// `build/dart-tests/<hash of its bytes>/`, writes a package config there whose native-asset
/// mapping names that copy, and runs each test file directly on the VM with it. No test process
/// runs the hooks or reads the shared library, and a copy is never rewritten, since its name is
/// its content.
///
/// Usage, from zed-impl/dart:
///   dart run ../tools/bin/tests.dart [-j N] [file or directory ...]
/// The default is every *_test.dart under test/, eight at a time. Logs go to
/// build/dart-tests/logs/. Run it under `systemd-run --user --scope -p MemoryMax=64G` to cap
/// the memory of all the tests together.
library;

import 'dart:async';
import 'dart:convert';
import 'dart:io';

const cap = Duration(seconds: 60);

Future<void> main(List<String> args) async {
  var jobs = 8;
  final targets = <String>[];
  for (var i = 0; i < args.length; i++) {
    if (args[i] == '-j') {
      jobs = int.parse(args[++i]);
    } else {
      targets.add(args[i]);
    }
  }
  final dart = Directory.current.path;
  if (!File('$dart/pubspec.yaml').readAsStringSync().contains('name: zed\n')) {
    stderr.writeln('run this from zed-impl/dart');
    exit(2);
  }
  // `dart test` runs the hooks of this package before it reads its arguments; there is no
  // command that runs them alone.
  final bin = File(Platform.resolvedExecutable).parent.path;
  final hooks = Process.runSync('$bin/dart', ['test', '--help']);
  if (hooks.exitCode != 0) {
    stderr.writeln('the build hooks failed:\n${hooks.stdout}${hooks.stderr}');
    exit(2);
  }
  final config = _freeze(dart, '${File(dart).parent.path}/build/dart-tests');
  final logs = Directory('${File(dart).parent.path}/build/dart-tests/logs')
    ..createSync(recursive: true);
  final files = [
    for (final t in targets.isEmpty ? ['test'] : targets) ..._tests(t),
  ]..sort();
  final vm = '$bin/dartvm';

  var passed = 0, failed = 0, timedOut = 0, next = 0;
  Future<void> worker() async {
    while (next < files.length) {
      final file = files[next++];
      final log = File('${logs.path}/${file.replaceAll('/', '_')}.log');
      final clock = Stopwatch()..start();
      final p = await Process.start(vm, ['--packages=$config', file]);
      final out = StringBuffer();
      final done = Future.wait([
        p.stdout.transform(utf8.decoder).forEach(out.write),
        p.stderr.transform(utf8.decoder).forEach(out.write),
      ]);
      final code = await p.exitCode.timeout(
        cap,
        onTimeout: () {
          p.kill(ProcessSignal.sigkill);
          return -1;
        },
      );
      await done;
      log.writeAsStringSync(out.toString());
      final s = (clock.elapsedMilliseconds / 1000).toStringAsFixed(1);
      if (code == 0) {
        passed++;
      } else if (code == -1) {
        timedOut++;
        print('TIMEOUT ${cap.inSeconds} s $file');
      } else {
        failed++;
        final lines = out.toString().split('\n');
        final at = lines.indexWhere((l) => l.contains('[E]'));
        final why = at < 0
            ? lines.lastWhere((l) => l.trim().isNotEmpty, orElse: () => '')
            : [
                for (final l in lines.skip(at + 1))
                  if (l.trim().isNotEmpty) l.trim(),
              ].firstOrNull;
        print('FAIL $s s $file: ${why ?? ''}');
      }
    }
  }

  await Future.wait([for (var i = 0; i < jobs; i++) worker()]);
  print('$passed passed, $failed failed, $timedOut timed out, of ${files.length} files');
  exit(failed + timedOut == 0 ? 0 : 1);
}

/// The test files `target` names: itself, or every *_test.dart under it.
List<String> _tests(String target) => !FileSystemEntity.isDirectorySync(target)
    ? [target]
    : [
        for (final f in Directory(target).listSync(recursive: true))
          if (f is File && f.path.endsWith('_test.dart')) f.path,
      ];

/// Copies the icu4x library the hooks built into `root`, under the hash of its bytes, with a
/// package config and a native-asset mapping beside it; the path of the package config.
String _freeze(String dart, String root) {
  final yaml = File('$dart/.dart_tool/native_assets.yaml').readAsStringSync();
  final lib = RegExp(r'"(/[^"]*libicu4x\.so)"').firstMatch(yaml)![1]!;
  final bytes = File(lib).readAsBytesSync();
  // FNV-1a, 64 bits.
  var h = 0xcbf29ce484222325;
  for (final b in bytes) {
    h = (h ^ b) * 0x100000001b3;
  }
  final dir = '$root/${h.toUnsigned(64).toRadixString(16).padLeft(16, '0')}';
  final config = '$dir/.dart_tool/package_config.json';
  if (File(config).existsSync()) return config;
  Directory('$dir/.dart_tool').createSync(recursive: true);
  // Each file is written beside its final name and renamed onto it, so a second run at the
  // same time never reads one half written.
  void put(String path, List<int> data) {
    final tmp = File('$path.$pid')..writeAsBytesSync(data);
    tmp.renameSync(path);
  }

  put('$dir/libicu4x.so', bytes);
  put('$dir/.dart_tool/native_assets.yaml', utf8.encode(yaml.replaceAll(lib, '$dir/libicu4x.so')));
  // The package config of zed itself names its root relative to .dart_tool; here it is absolute.
  final packages = File('$dart/.dart_tool/package_config.json').readAsStringSync();
  put(
    config,
    utf8.encode(packages.replaceAll('"rootUri": "../"', '"rootUri": "${Uri.directory(dart)}"')),
  );
  return config;
}
