import 'dart:io';
import 'dart:math' as math;

import 'package:test/test.dart';

import 'scaling.dart';
import 'support.dart';

/// Work of order `n^power`: a sleep of `n^power` units of `unit` nanoseconds. A sleep takes no
/// processor time and overruns by little, so it tests the limits, not the clock.
void work(int n, int power, int unit) =>
    sleep(Duration(microseconds: math.pow(n, power).toInt() * unit ~/ 1000));

void main() {
  test('accepts the three stage kinds', () {
    for (final ok in [
      'm0_01_scaffolding',
      'l01_07_fences',
      'l29_03_lowering_in_zed',
      's_01_stage1',
    ]) {
      expect(isStepName(ok), isTrue, reason: ok);
    }
  });

  test('rejects malformed names', () {
    for (final bad in [
      'm0_1_scaffolding', // step not two digits
      'l1_07_fences', // layer not two digits
      'l30_01_beyond', // no layer 30
      'l00_01_zero', // no layer 0
      'l01_00_zero', // steps count from 1
      'l01_07', // no description
      'l01_07_', // empty description
      'l01_07_Fences', // uppercase
      'x01_07_fences', // unknown stage
    ]) {
      expect(isStepName(bad), isFalse, reason: '$bad was accepted');
    }
  });

  test('work of the order given passes', () {
    check('linear work', 1000, (n) => work(n, 1, 1000));
    checkOrder('quadratic work', 100, 2, (n) => work(n, 2, 100));
  });

  test('work a power of n above the order given fails', () {
    expect(() => check('quadratic work', 100, (n) => work(n, 2, 100)), throwsStateError);
    expect(() => checkOrder('cubic work', 10, 2, (n) => work(n, 3, 200)), throwsStateError);
  });
}
