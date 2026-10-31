/// The cost scalarization (DESIGN.md sec:runtime, "Cost model, two tiers", written by step
/// M0.6).
///
/// The symbolic tier gives each alternative plan a work, a depth and a peak live footprint per
/// placed region, and the bytes crossing each cut edge between devices. Plans are held as a
/// Pareto frontier over those quantities until the scalarization picks one: it turns a plan
/// into one integer, an estimate of its running time in the target's time unit, and breaks a
/// tie by content address, so extraction is reproducible. The placement solver of step L24.5
/// uses the same function, so placement and extraction agree on what a plan costs.
///
/// All quantities are nonnegative integers, and the arithmetic saturates at the largest
/// `int`, 2^63 - 1, so the result is the same on every host.
library;

import 'address.dart';

const _max = 0x7fffffffffffffff;

int _add(int a, int b) => a > _max - b ? _max : a + b;

int _mul(int a, int b) => b != 0 && a > _max ~/ b ? _max : a * b;

int _divCeil(int a, int b) => a ~/ b + (a % b == 0 ? 0 : 1);

/// One device of a target: CPU cores, a GPU, a remote node.
final class Device {
  /// The device's name in `target(…)`, such as `cpu` or `gpu`.
  final String name;

  /// Processors the device runs in parallel.
  final int cores;

  /// Time units per unit of work on one core.
  final int opTime;

  /// The largest live footprint, in bytes, a plan may place on the device.
  final int capacity;

  const Device(this.name, {required this.cores, required this.opTime, required this.capacity});
}

/// A target profile: its devices and the cost of moving data between them.
final class Target {
  /// The devices, the first being the one unplaced code runs on.
  final List<Device> devices;

  /// Time units for each transfer over a cut edge, whatever its size.
  final int transferLatency;

  /// Time units per 64 bytes transferred, rounded up to whole blocks.
  final int transferPerBlock;

  /// The size the scalarization assumes for a cardinality the domains leave unbounded.
  final int nominalSize;

  const Target(
    this.devices, {
    required this.transferLatency,
    required this.transferPerBlock,
    required this.nominalSize,
  });

  /// The default target profile: one CPU of 8 cores, one time unit (read as a nanosecond)
  /// per unit of work, 16 GiB of memory. With one device no edge is cut. Unbounded
  /// cardinalities are taken as 2^20.
  const Target.defaultProfile()
    : devices = const [Device('cpu', cores: 8, opTime: 1, capacity: 1 << 34)],
      transferLatency = 0,
      transferPerBlock = 0,
      nominalSize = 1 << 20;

  /// The size a cost is evaluated at for a cardinality with upper bound `bound`.
  int size([int? bound]) => bound ?? nominalSize;

  /// The cost of one transfer of `bytes` over a cut edge.
  int transfer(int bytes) => _add(transferLatency, _mul(_divCeil(bytes, 64), transferPerBlock));
}

/// The symbolic cost of one region placed on one device, evaluated at the target's sizes:
/// the index of the device in [Target.devices]; the work, operations summed over the region's
/// graph, shared nodes once; the depth, the operations on its critical path; and the
/// footprint, the largest live set the static plan admits, in bytes.
typedef Region = ({int device, int work, int depth, int footprint});

/// One alternative plan: its content address, the tie-break; its placed regions; and the bytes
/// crossing each edge whose ends lie on different devices.
final class Plan {
  final ContentAddress address;
  final List<Region> regions;
  final List<int> cutEdges;

  const Plan(this.address, this.regions, this.cutEdges);

  @override
  bool operator ==(Object other) =>
      other is Plan &&
      other.address == address &&
      _same(other.regions, regions) &&
      _same(other.cutEdges, cutEdges);

  @override
  int get hashCode => Object.hash(address, Object.hashAll(regions), Object.hashAll(cutEdges));

  @override
  String toString() => 'Plan($address, $regions, $cutEdges)';
}

bool _same<T>(List<T> a, List<T> b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// The time bound for `work` and `depth` on `cores` processors, by Brent's theorem: the
/// critical path, plus the rest of the work shared among the cores, rounded up. Zero cores
/// are read as one, and a depth above the work as the work.
int brent(int work, int depth, int cores) {
  final d = depth < work ? depth : work;
  return _add(_divCeil(work - d, cores < 1 ? 1 : cores), d);
}

/// Whether the plan respects every device's capacity: the footprints placed on a device sum to
/// at most its capacity. A plan that names a device the target lacks is infeasible.
bool feasible(Plan plan, Target target) {
  final n = target.devices.length;
  if (plan.regions.any((r) => r.device >= n)) return false;
  final placed = _perDevice(plan, n);
  for (var d = 0; d < n; d++) {
    if (placed[d].footprint > target.devices[d].capacity) return false;
  }
  return true;
}

/// The work, depth and footprint a plan places on each device, in device order: the regions
/// on one device run one after another, so their work, depth and footprint add.
List<({int work, int depth, int footprint})> _perDevice(Plan plan, int devices) {
  final out = List.filled(devices, (work: 0, depth: 0, footprint: 0));
  for (final r in plan.regions) {
    final d = out[r.device];
    out[r.device] = (
      work: _add(d.work, r.work),
      depth: _add(d.depth, r.depth),
      footprint: _add(d.footprint, r.footprint),
    );
  }
  return out;
}

/// The scalar cost of a feasible plan on a target: for each device, the Brent bound of the
/// work and depth placed on it, times the device's time per operation, plus one transfer per
/// cut edge. Devices are summed as if they ran one after another, an upper bound on the
/// plan's running time that is monotone in every component of [vector].
int scalarize(Plan plan, Target target) {
  final placed = _perDevice(plan, target.devices.length);
  var s = 0;
  for (var d = 0; d < placed.length; d++) {
    final device = target.devices[d];
    s = _add(s, _mul(brent(placed[d].work, placed[d].depth, device.cores), device.opTime));
  }
  for (final bytes in plan.cutEdges) {
    s = _add(s, target.transfer(bytes));
  }
  return s;
}

/// The plan's cost vector on a target with `devices` devices, the quantities the frontier
/// compares: the work, depth and footprint on each device, then the number of cut edges and
/// the 64-byte blocks they carry. The scalar is monotone in each component, and feasibility
/// is antitone in each, so the frontier never drops the plan [pick] would choose.
List<int> vector(Plan plan, int devices) => [
  for (final d in _perDevice(plan, devices)) ...[d.work, d.depth, d.footprint],
  plan.cutEdges.length,
  plan.cutEdges.fold(0, (s, b) => _add(s, _divCeil(b, 64))),
];

/// Whether `a` dominates `b`: no worse in every quantity and better in one.
bool dominates(List<int> a, List<int> b) {
  var better = false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] > b[i]) return false;
    if (a[i] < b[i]) better = true;
  }
  return better;
}

int _lex(List<int> a, List<int> b) {
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return a[i] - b[i] < 0 ? -1 : 1;
  }
  return 0;
}

/// The Pareto frontier of the feasible `plans` on `target`: the feasible plans no other
/// feasible plan dominates, in content-address order. Plans with equal cost vectors are all
/// kept.
///
/// A plan's dominators all precede it in the lexicographic order of the vectors, and a
/// dominated dominator is itself dominated by a plan of the frontier, so each plan is compared
/// only with the frontier found before it: `O(P log P + P·F·devices)` for `F` plans on the
/// frontier. No known algorithm finds a Pareto frontier of more than three quantities in
/// `O(P log P)`, and this vector has `3·devices + 2`.
List<Plan> frontier(List<Plan> plans, Target target) {
  final n = target.devices.length;
  final live = [
    for (final p in plans)
      if (feasible(p, target)) (plan: p, v: vector(p, n)),
  ]..sort((a, b) => _lex(a.v, b.v));
  final kept = <({Plan plan, List<int> v})>[];
  for (final p in live) {
    if (!kept.any((k) => dominates(k.v, p.v))) kept.add(p);
  }
  return [for (final k in kept) k.plan]..sort((a, b) => a.address.compareTo(b.address));
}

/// The plan the scalarization picks: on the frontier, the least scalar cost, then the least
/// content address. Null when no plan is feasible, where the placement solver falls back to
/// its list schedule (sec:runtime).
Plan? pick(List<Plan> plans, Target target) {
  Plan? best;
  int? bestCost;
  for (final p in frontier(plans, target)) {
    final c = scalarize(p, target);
    // The frontier is in address order, so the first of the least cost has the least address.
    if (bestCost == null || c < bestCost) (best, bestCost) = (p, c);
  }
  return best;
}
