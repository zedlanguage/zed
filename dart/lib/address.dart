/// Content addresses (DESIGN.md sec:keypaths and step M0.7): the BLAKE3-256 hash of a
/// definition's canonical ZIR serialization, printed as 64 lowercase hex digits. Addresses are
/// ordered by their bytes, which is the content-address order every tie-break uses.
library;

import 'dart:typed_data';

/// A 256-bit content address.
final class ContentAddress implements Comparable<ContentAddress> {
  /// The 32 bytes.
  final Uint8List bytes;

  ContentAddress(this.bytes) : assert(bytes.length == 32);

  /// The address printed as hex, parsed back; null unless `hex` is exactly 64 lowercase hex
  /// digits.
  static ContentAddress? parse(String hex) {
    if (hex.length != 64 || !RegExp(r'^[0-9a-f]*$').hasMatch(hex)) return null;
    return ContentAddress(
      Uint8List.fromList([
        for (var i = 0; i < 64; i += 2) int.parse(hex.substring(i, i + 2), radix: 16),
      ]),
    );
  }

  @override
  int compareTo(ContentAddress other) {
    for (var i = 0; i < 32; i++) {
      if (bytes[i] != other.bytes[i]) return bytes[i] - other.bytes[i];
    }
    return 0;
  }

  @override
  bool operator ==(Object other) => other is ContentAddress && compareTo(other) == 0;

  @override
  int get hashCode => Object.hashAll(bytes);

  @override
  String toString() => bytes.map((b) => b.toRadixString(16).padLeft(2, '0')).join();
}
