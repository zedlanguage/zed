/// BLAKE3-256, the hash of content addresses (DESIGN.md sec:ir, "Identity"), after the
/// reference implementation of the BLAKE3 specification (O'Connor, Aumasson, Neves and
/// Wilcox-O'Hearn, 2020): unkeyed, 32 bytes of output.
library;

import 'dart:typed_data';

const _iv = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, //
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

const _permutation = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

const _chunkStart = 1, _chunkEnd = 2, _parent = 4, _root = 8;

const _blockLen = 64, _chunkLen = 1024;

int _rotr(int x, int n) => (x >>> n | x << (32 - n)) & 0xffffffff;

/// The compression function: the 16 words of state from chaining value `cv`, the 16 message
/// words `m`, the 64-bit `counter`, the block's length and the flags.
Uint32List _compress(List<int> cv, List<int> m, int counter, int len, int flags) {
  final s = Uint32List(16)
    ..setAll(0, cv)
    ..setAll(8, _iv.take(4))
    ..[12] = counter
    ..[13] = counter >>> 32
    ..[14] = len
    ..[15] = flags;
  var w = Uint32List.fromList(m);
  void g(int a, int b, int c, int d, int x, int y) {
    s[a] = s[a] + s[b] + x;
    s[d] = _rotr(s[d] ^ s[a], 16);
    s[c] = s[c] + s[d];
    s[b] = _rotr(s[b] ^ s[c], 12);
    s[a] = s[a] + s[b] + y;
    s[d] = _rotr(s[d] ^ s[a], 8);
    s[c] = s[c] + s[d];
    s[b] = _rotr(s[b] ^ s[c], 7);
  }

  for (var round = 0; round < 7; round++) {
    g(0, 4, 8, 12, w[0], w[1]);
    g(1, 5, 9, 13, w[2], w[3]);
    g(2, 6, 10, 14, w[4], w[5]);
    g(3, 7, 11, 15, w[6], w[7]);
    g(0, 5, 10, 15, w[8], w[9]);
    g(1, 6, 11, 12, w[10], w[11]);
    g(2, 7, 8, 13, w[12], w[13]);
    g(3, 4, 9, 14, w[14], w[15]);
    w = Uint32List.fromList([for (final i in _permutation) w[i]]);
  }
  for (var i = 0; i < 8; i++) {
    s[i] ^= s[i + 8];
    s[i + 8] ^= cv[i];
  }
  return s;
}

/// A compression not yet run, whose output is a chaining value or, with the root flag, the
/// hash.
typedef _Output = ({List<int> cv, List<int> block, int counter, int len, int flags});

List<int> _chain(_Output o) => _compress(o.cv, o.block, o.counter, o.len, o.flags).sublist(0, 8);

/// The message words of the block of `input` from `start`, zero-padded to 64 bytes.
List<int> _words(Uint8List input, int start, int len) {
  final block = Uint8List(_blockLen)..setRange(0, len, input, start);
  final data = ByteData.sublistView(block);
  return [for (var i = 0; i < 16; i++) data.getUint32(4 * i, Endian.little)];
}

/// The chunk of `input` numbered `index`: every block but the last compressed into the
/// chaining value, the last left as the output.
_Output _chunk(Uint8List input, int index) {
  final start = index * _chunkLen;
  final end = start + _chunkLen < input.length ? start + _chunkLen : input.length;
  List<int> cv = _iv;
  var at = start;
  // A chunk has at least one block, an empty input's one block empty.
  while (true) {
    final len = end - at < _blockLen ? end - at : _blockLen;
    final flags = (at == start ? _chunkStart : 0) | (at + len == end ? _chunkEnd : 0);
    final block = _words(input, at, len);
    if (at + len == end) return (cv: cv, block: block, counter: index, len: len, flags: flags);
    cv = _compress(cv, block, index, len, flags).sublist(0, 8);
    at += len;
  }
}

_Output _parentOf(List<int> left, List<int> right) =>
    (cv: _iv, block: [...left, ...right], counter: 0, len: _blockLen, flags: _parent);

/// The BLAKE3-256 hash of `input`.
Uint8List blake3(Uint8List input) {
  final chunks = input.isEmpty ? 1 : (input.length + _chunkLen - 1) ~/ _chunkLen;
  // The chaining values of the complete subtrees so far, largest first: after chunk `i` the
  // stack holds one subtree per bit set in `i + 1`.
  final stack = <List<int>>[];
  for (var i = 0; i < chunks - 1; i++) {
    var cv = _chain(_chunk(input, i));
    for (var total = i + 1; total & 1 == 0; total >>= 1) {
      cv = _chain(_parentOf(stack.removeLast(), cv));
    }
    stack.add(cv);
  }
  var out = _chunk(input, chunks - 1);
  while (stack.isNotEmpty) {
    out = _parentOf(stack.removeLast(), _chain(out));
  }
  final s = _compress(out.cv, out.block, out.counter, out.len, out.flags | _root);
  final bytes = ByteData(32);
  for (var i = 0; i < 8; i++) {
    bytes.setUint32(4 * i, s[i], Endian.little);
  }
  return bytes.buffer.asUint8List();
}
