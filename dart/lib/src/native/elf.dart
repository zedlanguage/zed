/// The object writer (step L1.36): the generated code as a relocatable ELF file for x86-64,
/// `zed_root` exported and each runtime hook an undefined symbol, its address in the code
/// left to the linker.
library;

import 'dart:convert';
import 'dart:typed_data';

import 'codegen.dart';

/// The ELF object file of [code].
Uint8List elf(Code code) {
  final strtab = _Strings();
  final shstrtab = _Strings();
  // The symbols: the null symbol, the local functions, then the globals, the exported
  // functions and the hooks.
  final syms = BytesBuilder(copy: false)..add(Uint8List(24));
  void sym(String name, int info, int section, int value, int size) {
    final b = ByteData(24)
      ..setUint32(0, strtab.add(name), Endian.little)
      ..setUint8(4, info)
      ..setUint16(6, section, Endian.little)
      ..setUint64(8, value, Endian.little)
      ..setUint64(16, size, Endian.little);
    syms.add(b.buffer.asUint8List());
  }

  const func = 2, global = 1 << 4;
  var count = 1;
  for (final s in code.symbols.where((s) => !s.global)) {
    sym(s.name, func, 1, s.offset, s.size);
    count++;
  }
  final firstGlobal = count;
  for (final s in code.symbols.where((s) => s.global)) {
    sym(s.name, global | func, 1, s.offset, s.size);
    count++;
  }
  final hookSym = count;
  for (final h in Hook.values) {
    sym(h.symbol, global, 0, 0, 0);
  }
  final rela = BytesBuilder(copy: false);
  for (final (:offset, :hook) in code.hooks) {
    final b = ByteData(24)
      ..setUint64(0, offset, Endian.little)
      // R_X86_64_64: the symbol's address, 64 bits.
      ..setUint64(8, (hookSym + hook) << 32 | 1, Endian.little)
      ..setInt64(16, 0, Endian.little);
    rela.add(b.buffer.asUint8List());
  }

  final sections = <_Section>[
    _Section(0, 0, 0, Uint8List(0), 0, 0, 0, 0),
    _Section(shstrtab.add('.text'), 1, 6, code.bytes, 0, 0, 16, 0),
    _Section(shstrtab.add('.rela.text'), 4, 0x40, rela.toBytes(), 3, 1, 8, 24),
    _Section(shstrtab.add('.symtab'), 2, 0, syms.toBytes(), 4, firstGlobal, 8, 24),
    _Section(shstrtab.add('.strtab'), 3, 0, strtab.bytes, 0, 0, 1, 0),
    _Section(shstrtab.add('.note.GNU-stack'), 1, 0, Uint8List(0), 0, 0, 1, 0),
  ];
  final shstrndx = sections.length;
  sections.add(_Section(shstrtab.add('.shstrtab'), 3, 0, shstrtab.bytes, 0, 0, 1, 0));

  final out = BytesBuilder(copy: false)..add(Uint8List(64));
  final offsets = <int>[];
  for (final s in sections) {
    while (out.length % 16 != 0) {
      out.addByte(0);
    }
    offsets.add(out.length);
    out.add(s.data);
  }
  while (out.length % 16 != 0) {
    out.addByte(0);
  }
  final shoff = out.length;
  for (var i = 0; i < sections.length; i++) {
    final s = sections[i];
    final b = ByteData(64)
      ..setUint32(0, s.name, Endian.little)
      ..setUint32(4, s.type, Endian.little)
      ..setUint64(8, s.flags, Endian.little)
      ..setUint64(24, i == 0 ? 0 : offsets[i], Endian.little)
      ..setUint64(32, s.data.length, Endian.little)
      ..setUint32(40, s.link, Endian.little)
      ..setUint32(44, s.info, Endian.little)
      ..setUint64(48, s.align, Endian.little)
      ..setUint64(56, s.entsize, Endian.little);
    out.add(b.buffer.asUint8List());
  }
  final bytes = out.toBytes();
  ByteData.sublistView(bytes)
    ..setUint32(0, 0x464c457f, Endian.little)
    ..setUint8(4, 2) // 64-bit
    ..setUint8(5, 1) // little-endian
    ..setUint8(6, 1) // version 1
    ..setUint16(16, 1, Endian.little) // relocatable
    ..setUint16(18, 62, Endian.little) // x86-64
    ..setUint32(20, 1, Endian.little)
    ..setUint64(40, shoff, Endian.little)
    ..setUint16(52, 64, Endian.little)
    ..setUint16(58, 64, Endian.little)
    ..setUint16(60, sections.length, Endian.little)
    ..setUint16(62, shstrndx, Endian.little);
  return bytes;
}

final class _Section {
  final int name, type, flags;
  final Uint8List data;
  final int link, info, align, entsize;

  const _Section(
    this.name,
    this.type,
    this.flags,
    this.data,
    this.link,
    this.info,
    this.align,
    this.entsize,
  );
}

/// A string table: each name once, after a leading 0.
final class _Strings {
  final _b = BytesBuilder(copy: false)..addByte(0);

  /// Adds [s]; returns its offset.
  int add(String s) {
    final at = _b.length;
    _b
      ..add(utf8.encode(s))
      ..addByte(0);
    return at;
  }

  Uint8List get bytes => _b.toBytes();
}
