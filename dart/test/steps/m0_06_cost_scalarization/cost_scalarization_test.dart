/// Step M0.6: the cost scalarization (DESIGN.md sec:runtime). Plans for a log-processing
/// pipeline (parse each line, keep the errors, count them by service) placed on a CPU alone or
/// split with a GPU, compared by the scalar cost and by content address.
library;

import 'dart:typed_data';

import 'package:test/test.dart';
import 'package:zed/address.dart';
import 'package:zed/cost.dart';

import '../../support/instances.dart';
import '../../support/scaling.dart' as scaling;

/// The address whose last byte is `n` and whose other bytes are zero.
ContentAddress addr(int n) => ContentAddress(Uint8List(32)..[31] = n);

/// A workstation: 8 CPU cores and a GPU of 1,024 lanes, each lane four times slower than a
/// core, with 4 GiB of GPU memory; a transfer costs 5,000 units plus 2 per 64-byte block.
const workstation = Target(
  [
    Device('cpu', cores: 8, opTime: 1, capacity: 1 << 34),
    Device('gpu', cores: 1024, opTime: 4, capacity: 1 << 32),
  ],
  transferLatency: 5000,
  transferPerBlock: 2,
  nominalSize: 1 << 20,
);

const defaultProfile = Target.defaultProfile();

const lines = 1 << 20;

/// Parsing 2^20 log lines: 40 operations a line, every line independent.
Region parse(int device) => (device: device, work: 40 * lines, depth: 40, footprint: 64 * lines);

/// Counting errors by service: a tree reduction, depth logarithmic in the lines.
Region count(int device) => (device: device, work: 2 * lines, depth: 2 * 20, footprint: 8 * lines);

Plan plan(int address, List<Region> regions, [List<int> cutEdges = const []]) =>
    Plan(addr(address), regions, cutEdges);

Region region(int work, int depth, int footprint) =>
    (device: 0, work: work, depth: depth, footprint: footprint);

Plan randomPlan(Rng rng, int devices) {
  final regions = [
    for (var i = 1 + rng.below(4); i > 0; i--)
      if (rng.below(10000) case final work)
        (
          device: rng.below(devices),
          work: work,
          depth: rng.below(work + 1),
          footprint: rng.below(1 << 20),
        ),
  ];
  final cutEdges = [for (var i = rng.below(3); i > 0; i--) rng.below(1 << 16)];
  return plan(rng.below(256), regions, cutEdges);
}

/// `p` with its region `i` replaced by `f` of it.
Plan withRegion(Plan p, int i, Region Function(Region) f) =>
    Plan(p.address, [...p.regions]..[i] = f(p.regions[i]), p.cutEdges);

void main() {
  test('plans of equal cost are ordered by content address', () {
    // The same two regions listed in either order are two plans with different addresses and
    // the same cost; the lower address wins, whatever order the plans arrive in.
    final a = plan(9, [parse(0), count(0)]);
    final b = plan(3, [count(0), parse(0)]);
    expect(scalarize(a, defaultProfile), scalarize(b, defaultProfile));
    expect(pick([a, b], defaultProfile)!.address, addr(3));
    expect(pick([b, a], defaultProfile)!.address, addr(3));
  });

  test('a plan that cuts one more edge costs one more transfer', () {
    // Parse on the GPU and count on the CPU cuts the edge carrying the parsed records (8 bytes
    // a line); also sending the counts back to the GPU for a final step cuts one more.
    const t = workstation;
    final split = plan(1, [parse(1), count(0)], [8 * lines]);
    final more = plan(2, [parse(1), count(0)], [8 * lines, 4096]);
    expect(scalarize(more, t) - scalarize(split, t), t.transfer(4096));
    expect(t.transfer(4096), 5000 + 64 * 2);
    // A transfer of a partial block costs the whole block.
    expect(t.transfer(1), 5002);
    expect(t.transfer(0), 5000);
  });

  test('the default profile runs everything on eight cores', () {
    const t = defaultProfile;
    expect(t.devices.length, 1);
    expect((t.devices[0].cores, t.devices[0].opTime), (8, 1));
    expect(t.devices[0].capacity, 16 << 30);
    expect(t.size(), 1 << 20);
    expect(t.size(100), 100);
    // Parsing: the 40-operation critical path plus the rest of the work shared by 8 cores.
    expect(scalarize(plan(0, [parse(0)]), t), (40 * lines - 40) ~/ 8 + 40);
  });

  test('the GPU wins when the work is large enough to pay for the transfer', () {
    const t = workstation;
    final cpu = plan(1, [parse(0), count(0)]);
    final gpu = plan(2, [parse(1), count(0)], [8 * lines]);
    expect(scalarize(gpu, t), lessThan(scalarize(cpu, t)));
    expect(pick([cpu, gpu], t)!.address, addr(2));
    // On a small input the transfer dominates and the CPU plan wins.
    Region small(Region r) =>
        (device: r.device, work: r.work ~/ 4096, depth: r.depth, footprint: r.footprint ~/ 4096);
    final cpuSmall = plan(1, [small(parse(0)), small(count(0))]);
    final gpuSmall = plan(2, [small(parse(1)), small(count(0))], [8 * lines ~/ 4096]);
    expect(pick([cpuSmall, gpuSmall], t)!.address, addr(1));
  });

  test('a plan over a device capacity is not picked', () {
    // Keeping 2^27 lines on the GPU needs 8 GiB, more than its 4 GiB.
    const t = workstation;
    Region big(Region r) =>
        (device: r.device, work: r.work * 128, depth: r.depth, footprint: r.footprint * 128);
    final gpu = plan(1, [big(parse(1)), big(count(0))], [8 * lines * 128]);
    final cpu = plan(2, [big(parse(0)), big(count(0))]);
    expect(feasible(gpu, t), isFalse);
    expect(scalarize(gpu, t), lessThan(scalarize(cpu, t)));
    expect(pick([gpu, cpu], t)!.address, addr(2));
    // With no feasible plan, nothing is picked and the solver falls back to its list schedule.
    expect(pick([gpu], t), isNull);
    // A plan naming a device the target lacks is infeasible.
    expect(feasible(plan(3, [parse(2)]), t), isFalse);
  });

  test('the frontier keeps incomparable plans and drops dominated ones', () {
    // Fused: less work, deeper. Split: more work, shallower. Wasteful: worse than split in
    // every quantity.
    final fused = plan(5, [region(100, 50, 10)]);
    final split = plan(4, [region(120, 10, 10)]);
    final waste = plan(6, [region(130, 10, 20)]);
    final twin = plan(1, [region(120, 10, 10)]);
    final kept = frontier([fused, split, waste, twin], defaultProfile);
    expect([for (final p in kept) p.address], [addr(1), addr(4), addr(5)]);
  });

  test('the scalar is monotone in work, depth and cut edges', () {
    const t = workstation;
    final rng = Rng(0x6c05);
    for (var n = 0; n < randomInstances; n++) {
      final p = randomPlan(rng, 2);
      final base = scalarize(p, t);
      final i = rng.below(p.regions.length);
      final extra = 1 + rng.below(100);
      final moreWork = withRegion(
        p,
        i,
        (r) => (device: r.device, work: r.work + extra, depth: r.depth, footprint: r.footprint),
      );
      expect(scalarize(moreWork, t), greaterThanOrEqualTo(base));
      final deeper = withRegion(
        p,
        i,
        (r) => (
          device: r.device,
          work: r.work,
          depth: r.depth + 1 < r.work ? r.depth + 1 : r.work,
          footprint: r.footprint,
        ),
      );
      expect(scalarize(deeper, t), greaterThanOrEqualTo(base));
      final bytes = rng.below(1 << 16);
      final cut = Plan(p.address, p.regions, [...p.cutEdges, bytes]);
      expect(scalarize(cut, t), base + t.transfer(bytes));
    }
  });

  test('the pick is the same in every arrival order and minimal over every feasible plan', () {
    const t = workstation;
    final rng = Rng(0xf00d);
    var pruned = 0;
    for (var n = 0; n < randomInstances; n++) {
      final plans = [for (var i = 2 + rng.below(6); i > 0; i--) randomPlan(rng, 2)];
      final first = pick(plans, t);
      for (var k = 0; k < 4; k++) {
        final (i, j) = (rng.below(plans.length), rng.below(plans.length));
        final q = plans[i];
        plans[i] = plans[j];
        plans[j] = q;
        expect(pick(plans, t), first);
      }
      // Pruning to the frontier loses nothing: the pick has the least scalar of every
      // feasible plan, and a plan the frontier drops is never cheaper than one it keeps.
      final feasiblePlans = [
        for (final q in plans)
          if (feasible(q, t)) q,
      ];
      final kept = frontier(plans, t);
      pruned += feasiblePlans.length - kept.length;
      if (first == null) {
        expect(feasiblePlans, isEmpty);
        continue;
      }
      for (final q in feasiblePlans) {
        expect(scalarize(q, t), greaterThanOrEqualTo(scalarize(first, t)));
        if (!kept.contains(q)) {
          expect(
            kept.any(
              (k) => dominates(vector(k, 2), vector(q, 2)) && scalarize(k, t) <= scalarize(q, t),
            ),
            isTrue,
          );
        }
      }
    }
    expect(pruned, greaterThan(randomInstances ~/ 2), reason: 'the frontier pruned only $pruned');
    expect(brent(0, 0, 8), 0);
  });

  test('the frontier takes time linear in the plans when it stays small', () {
    // Each plan is a fused or a split variant scaled by its distance from the end of the list,
    // so the frontier holds the last two, and every other plan is compared with those only.
    // The input lists them last, where a scan of the plans in arrival order meets them last.
    List<Plan> plans(int n) => [
      for (var i = 0; i < n; i++)
        if (n - i case final k)
          plan(i % 256, [
            k.isEven ? region(100 + k, 50 + k, 10 + k) : region(120 + k, 10 + k, 10 + k),
          ]),
    ];
    scaling.check('the Pareto frontier of plans', 2000, (n) => pick(plans(n), workstation));
  });
}
