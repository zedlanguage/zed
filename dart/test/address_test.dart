import 'dart:typed_data';

import 'package:test/test.dart';
import 'package:zed/address.dart';

void main() {
  test('hex round-trips and rejects other spellings', () {
    final bytes = Uint8List(32)
      ..[0] = 0xab
      ..[31] = 0x07;
    final a = ContentAddress(bytes);
    final hex = a.toString();
    expect(hex.length, 64);
    expect(hex.startsWith('ab00') && hex.endsWith('0007'), isTrue);
    expect(ContentAddress.parse(hex), a);
    expect(ContentAddress.parse(hex.toUpperCase()), isNull);
    expect(ContentAddress.parse(hex.substring(1)), isNull);
  });

  test('the order is byte order', () {
    final lo = Uint8List(32)..[31] = 0xff;
    final hi = Uint8List(32)..[0] = 0x01;
    expect(ContentAddress(lo).compareTo(ContentAddress(hi)), lessThan(0));
  });
}
