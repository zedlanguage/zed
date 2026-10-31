/// The reference evaluator (step M0.9): it runs a kernel term directly, with the failure rules
/// of sec:failure, the collision rule, exact float reduction and both `fix` kinds.
///
/// It is a machine with an explicit stack of frames, so the depth of a computation is bounded
/// by [maxDepth] and by memory, never by the Dart call stack. Every step either evaluates a
/// term or returns a value to the frame on top; a frame that waits for another value pushes
/// itself again. A failure unwinds the frames until one handles it.
library;

import 'dart:collection';
import 'dart:math' as math;

import 'error.dart';
import 'exact.dart';
import 'pmap.dart';
import 'term.dart';
import 'text.dart';
import 'value.dart';
import 'words.dart';

/// The fewest steps a run must be able to take before it may report [OutOfFuelError].
const minSteps = 10000000;

/// The fewest bytes of memory a run must be able to use. The reference evaluator sets no
/// memory limit of its own, so it is bounded only by the machine.
const minMemory = 1 << 30;

/// The fewest nested calls a run must follow before it may report [TooDeepError].
const minNestedCalls = 20000;

/// The most nested calls the evaluator follows.
const maxDepth = 20000;

/// The order in which a definedness `fix` defines its entries: all of them do so in the same
/// result, which the finite-model harness checks (step M0.10).
sealed class Schedule {
  const Schedule();
}

/// Round by round, each entry seeing only the entries defined in earlier rounds.
final class Rounds extends Schedule {
  const Rounds();
}

/// In a random order drawn from `seed`, each entry seeing every entry defined so far.
final class Chaotic extends Schedule {
  final int seed;

  const Chaotic(this.seed);
}

/// On demand: a read of an undefined entry defines it first.
final class Pull extends Schedule {
  const Pull();
}

/// An output port's log of pushed values, and its capacity if it has one.
final class Output {
  final List<Value> log = [];
  final int? capacity;

  Output([this.capacity]);
}

/// A lookup port: a source whose values are read one key at a time. [get] throws a
/// [PortFailure] when it cannot answer.
abstract interface class Lookup {
  Value get(Value key);
}

/// Why a lookup port could not answer a read.
final class PortFailure implements Exception {
  final String why;

  const PortFailure(this.why);
}

/// The ports a program runs against: input values, lookup sources, and output logs.
final class World {
  final Map<String, Value> inputs = {};
  final Map<String, Output> outputs = {};
  final Map<String, Lookup> sources = {};

  /// Every value read from each source, so a key read twice reads the same value.
  final Map<String, SplayTreeMap<Value, Value>> reads = {};

  World input(String name, Value value) {
    inputs[name] = value;
    return this;
  }

  World source(String name, Lookup port) {
    sources[name] = port;
    return this;
  }

  World output(String name, [int? capacity]) {
    outputs[name] = Output(capacity);
    return this;
  }

  List<Value> log(String name) => outputs[name]!.log;
}

/// The value of `term` in an empty world.
Value eval(Term term) => Evaluator(World()).run(term);

typedef _Env = PMap<String, Object>;

int _byName(String a, String b) => a.compareTo(b);

/// A function value.
final class _Closure {
  final List<String> params;
  final Term body;
  final _Env env;

  _Closure(this.params, this.body, this.env);
}

/// The family a definedness `fix` is defining, as its body reads it in one round: an entry
/// defined in an earlier round is visible.
final class _Partial {
  final _Fix fix;
  final int round;

  _Partial(this.fix, this.round);
}

/// A lookup port, read with `[]`.
final class _Source {
  final String port;

  _Source(this.port);
}

/// The round an entry sees when it sees every entry defined so far.
const _always = 0x7fffffffffffffff;

/// A definedness `fix` being evaluated.
final class _Fix {
  final int id;
  final SplayTreeSet<Value> domain;
  final Term body;
  final String self, key;
  final _Env env;

  /// Each defined entry with the round that defined it.
  final defined = SplayTreeMap<Value, (Value, int)>();
  final busy = SplayTreeSet<Value>();
  final stalled = SplayTreeSet<Value>();

  _Fix(this.id, this.domain, this.body, this.self, this.key, this.env);
}

/// A read of an entry of definedness `fix` number [fix] that is not yet defined. The entry
/// reading it stops; the schedule tries it again later.
final class _Undefined implements Exception {
  final int fix;
  final Value key;

  _Undefined(this.fix, this.key);
}

/// A computation waiting for a value. [undo] runs when a failure unwinds past it; [handle]
/// returns true when it takes over from the failure.
final class _Frame {
  final void Function(Object v) resume;
  final void Function()? undo;
  final bool Function(Object stop)? handle;

  _Frame(this.resume, [this.undo, this.handle]);
}

final class _SplitMix {
  int _s;

  _SplitMix(this._s);

  int next() {
    _s += 0x9e3779b97f4a7c15;
    var z = _s;
    z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9;
    z = (z ^ (z >>> 27)) * 0x94d049bb133111eb;
    return z ^ (z >>> 31);
  }

  /// `next() % m` with `next()` read as unsigned.
  int below(int m) {
    final u = next();
    return ((u >>> 1) % m * 2 + (u & 1)) % m;
  }

  void shuffle<T>(List<T> xs) {
    for (var i = xs.length - 1; i >= 1; i--) {
      final j = below(i + 1);
      final t = xs[i];
      xs[i] = xs[j];
      xs[j] = t;
    }
  }
}

/// Runs kernel terms against a [World].
final class Evaluator {
  final World world;
  final Schedule schedule;

  /// The steps left; null for no limit.
  int? fuel;

  int _depth = 0, _pure = 0, _fixes = 0;
  final _stack = <_Frame>[];
  Term? _next;
  _Env _env = const PMap.empty(_byName);
  Object? _value;

  Evaluator(this.world, {this.schedule = const Rounds(), this.fuel});

  /// The value of `term`. Throws a [KernelError] when the evaluation stops without one.
  Value run(Term term) {
    _depth = 0;
    _pure = 0;
    _stack.clear();
    _go(term, const PMap.empty(_byName));
    Object? stop;
    while (true) {
      KernelError? escaped;
      try {
        final s = stop;
        final next = _next;
        if (s != null) {
          stop = null;
          if (!_unwind(s)) {
            if (s is KernelError) {
              escaped = s;
            } else {
              throw StateError('only a definedness fix binds a partial family');
            }
          }
        } else if (next != null) {
          _next = null;
          _step(next, _env);
        } else if (_stack.isEmpty) {
          final v = _value;
          if (v is! Value) throw const KernelTypeError("the program's result is a function");
          return v;
        } else {
          _stack.removeLast().resume(_value!);
        }
      } on KernelError catch (e) {
        _next = null;
        stop = e;
      } on _Undefined catch (u) {
        _next = null;
        stop = u;
      }
      if (escaped != null) throw escaped;
    }
  }

  /// Pops frames until one handles `stop`; false when none does.
  bool _unwind(Object stop) {
    while (_stack.isNotEmpty) {
      final f = _stack.removeLast();
      if (f.handle?.call(stop) ?? false) return true;
      f.undo?.call();
    }
    return false;
  }

  void _go(Term t, _Env env) {
    _next = t;
    _env = env;
  }

  void _ret(Object v) => _value = v;

  void _then(void Function(Object v) k) => _stack.add(_Frame(k));

  void _ev(Term t, _Env env, void Function(Object v) k) {
    _then(k);
    _go(t, env);
  }

  void _data(Term t, _Env env, void Function(Value v) k) => _ev(t, env, (v) => k(_asData(v)));

  void _family(Term t, _Env env, void Function(Family f) k) => _data(t, env, (v) {
    if (v is! Family) throw KernelTypeError('expected a family, found $v');
    k(v);
  });

  /// The values of `ts` in order.
  void _all(List<Term> ts, _Env env, void Function(List<Object> vs) k) {
    if (ts.isEmpty) return k(const []);
    final out = <Object>[];
    void next(Object v) {
      out.add(v);
      if (out.length < ts.length) {
        _ev(ts[out.length], env, next);
      } else {
        k(out);
      }
    }

    _ev(ts[0], env, next);
  }

  void _burn() {
    final f = fuel;
    if (f == null) return;
    if (f == 0) throw const OutOfFuelError();
    fuel = f - 1;
  }

  void _step(Term term, _Env env) {
    switch (term) {
      case Lit(:final value):
        _ret(value);
      case Var(:final name):
        _ret(env[name] ?? (throw KernelTypeError('unbound variable `$name`')));
      case Lam(:final params, :final body):
        _ret(_Closure(params, body, env));
      case PrimFn(:final prim):
        _ret(prim);
      case App(:final f, :final args):
        _all([f, ...args], env, (vs) => _apply(vs[0], vs.sublist(1)));
      case PrimApp(:final prim, :final args):
        _all(args, env, (vs) => _prim(prim, vs));
      case Let(:final name, :final value, :final body):
        _ev(value, env, (v) => _go(body, env.put(name, v)));
      case If(:final cond, :final then, :final orElse):
        _data(cond, env, (c) {
          switch (c) {
            case Bool(value: true):
              _go(then, env);
            case Bool(value: false):
              _go(orElse, env);
            case Atom():
              _ret(c);
            default:
              throw KernelTypeError('`if` on $c');
          }
        });
      case Match(:final scrutinee, :final arms):
        _ev(scrutinee, env, (v) {
          for (final (pat, body) in arms) {
            final hit = v is Value
                ? _match(pat, v, env)
                : switch (pat) {
                    WildP() => env,
                    BindP(:final name) => env.put(name, v),
                    _ => null,
                  };
            if (hit != null) return _go(body, hit);
          }
          throw KernelTypeError(v is Value ? 'no arm matches $v' : 'no arm matches the function');
        });
      case Fam(:final domain, :final variable, :final body):
        _family(domain, env, (d) {
          _pure++;
          final keys = d.keys.toList(), out = <(Keypath, Value)>[];
          void next(int i) {
            if (i == keys.length) {
              _pure--;
              return _ret(Family.fromLeaves(out));
            }
            _data(body, env.put(variable, keys[i]), (v) {
              out.add(([keys[i]], v));
              next(i + 1);
            });
          }

          next(0);
        });
      case Reindex(:final family, :final kf, :final vf):
        _family(family, env, (f) {
          _ev(kf, env, (kf) {
            _ev(vf, env, (vf) {
              _pure++;
              _reindex(f, kf, vf, (out) {
                _pure--;
                _ret(out);
              });
            });
          });
        });
      case Discard(:final family, :final sel):
        _family(family, env, (f) {
          _ev(sel, env, (sel) {
            _pure++;
            _discard(f, sel, [], (out) {
              _pure--;
              _ret(out);
            });
          });
        });
      case Fold(:final family, :final op, :final identity, :final depth):
        _family(family, env, (f) {
          _ev(op, env, (op) {
            void fold(Value? identity) {
              _pure++;
              _fold(f, op, identity, depth, (out) {
                _pure--;
                _ret(out);
              });
            }

            if (identity == null) return fold(null);
            _data(identity, env, fold);
          });
        });
      case Fix(:final init, :final step, :final self, :final key, :final kind):
        _pure++;
        void done(Value out) {
          _pure--;
          _ret(out);
        }

        switch (kind) {
          case Lattice(:final join):
            _fixLattice(init, step, join, env, done);
          case Definedness():
            _fixDefinedness(init, step, self, key, env, done);
        }
      case Gen(:final init, :final step, :final guard, :final pos):
        _data(init, env, (init) {
          _ev(step, env, (step) {
            _ev(guard, env, (guard) => _generations(init, step, guard, pos));
          });
        });
      case Read(:final port):
        _checkImpure(port);
        final v = world.inputs[port];
        if (v != null) return _ret(v);
        if (world.sources.containsKey(port)) return _ret(_Source(port));
        throw UnknownPortError(port);
      case Push(:final port, :final value):
        _data(value, env, (v) {
          _checkImpure(port);
          final out = world.outputs[port] ?? (throw UnknownPortError(port));
          final cap = out.capacity;
          if (cap != null && out.log.length >= cap) return _ret(const Atom('full'));
          out.log.add(v);
          _ret(const Atom('ok'));
        });
    }
  }

  void _checkImpure(String port) {
    if (_pure > 0) throw KernelTypeError('port `$port` used inside a pure region');
  }

  void _apply(Object f, List<Object> args) {
    _burn();
    switch (f) {
      case _Closure c:
        if (c.params.length != args.length) {
          throw KernelTypeError(
            'a function of ${c.params.length} parameters called with ${args.length} arguments',
          );
        }
        if (_depth >= maxDepth) throw const TooDeepError();
        var env = c.env;
        for (var i = 0; i < args.length; i++) {
          env = env.put(c.params[i], args[i]);
        }
        _depth++;
        _then((v) {
          _depth--;
          _ret(v);
        });
        _go(c.body, env);
      case Prim p:
        _prim(p, args);
      case _Source() || Family() when args.length == 1:
        _prim(Prim.get, [f, args[0]]);
      case _Partial() || _Source():
        throw const KernelTypeError('a family is read with `[]`, not called');
      case Atom():
        _ret(f);
      default:
        throw KernelTypeError('$f is not a function');
    }
  }

  /// `f(a, b)`, which must be data.
  void _call2(Object f, Value a, Value b, void Function(Value v) k) {
    _then((v) => k(_asData(v)));
    _apply(f, [a, b]);
  }

  void _applyThen(Object f, List<Object> args, void Function(Object v) k) {
    _then(k);
    _apply(f, args);
  }

  void _prim(Prim p, List<Object> args) {
    final n = p.arity;
    if (n != null && args.length != n) {
      throw KernelTypeError('$p takes $n arguments, given ${args.length}');
    }
    final f = p == Prim.get || p == Prim.tupleGet ? args[0] : null;
    if (p == Prim.get && f is _Partial) {
      final k = args[1];
      if (k is! Value) throw const KernelTypeError('a key must be data');
      if (k is Atom) return _ret(k);
      final fix = f.fix;
      final found = fix.defined[k];
      if (found != null && found.$2 < f.round) return _ret(found.$1);
      if (!fix.domain.contains(k)) return _ret(const Atom('notFound'));
      if (schedule is Pull &&
          _depth < maxDepth &&
          !fix.busy.contains(k) &&
          !fix.stalled.contains(k)) {
        return _demand(fix, k);
      }
      throw _Undefined(fix.id, k);
    }
    if (f is _Source) {
      _checkImpure(f.port);
      final k = args[1];
      if (k is! Value) throw const KernelTypeError('a key must be data');
      if (k is Atom) return _ret(k);
      final reads = world.reads.putIfAbsent(f.port, SplayTreeMap.new);
      final seen = reads[k];
      if (seen != null) return _ret(seen);
      final Value v;
      try {
        v = world.sources[f.port]!.get(k);
      } on PortFailure catch (e) {
        throw PortError(f.port, e.why);
      }
      reads[k] = v;
      return _ret(v);
    }
    final vals = <Value>[];
    for (final a in args) {
      if (a is Value) {
        vals.add(a);
      } else if (p == Prim.eq || p == Prim.ne) {
        throw const KernelTypeError(
          '`==` on functions compares them at every point of an enumerable domain, which '
          'their types give (step L1.22)',
        );
      } else {
        throw KernelTypeError('$p applied to a function');
      }
    }
    if (p != Prim.tuple && p != Prim.atom && p != Prim.eq && p != Prim.ne && vals.any(_isAtom)) {
      return _ret(Value.mergeFailures(vals.where(_isAtom)));
    }
    _ret(primData(p, vals));
  }

  void _reindex(Family family, Object kf, Object vf, void Function(Family out) k) {
    final leaves = family.leaves(), out = <(Keypath, Value)>[];
    void next(int i) {
      if (i == leaves.length) return k(Family.fromLeaves(out));
      final (path, v) = leaves[i];
      final p = Path(path);
      _call2(kf, p, v, (key) {
        _call2(vf, p, v, (value) {
          out.add((key is Path ? key.keys : [key], value));
          next(i + 1);
        });
      });
    }

    next(0);
  }

  void _discard(Family family, Object sel, Keypath prefix, void Function(Family out) k) {
    final entries = family.entries.toList(), out = <(Keypath, Value)>[];
    void next(int i) {
      if (i == entries.length) return k(Family.fromLeaves(out));
      final (key, v) = entries[i];
      final path = [...prefix, key];
      _call2(sel, Path(path), v, (verdict) {
        switch (verdict) {
          case Bool(value: true):
            if (v is Family) {
              return _discard(v, sel, path, (sub) {
                out.add(([key], sub));
                next(i + 1);
              });
            }
            out.add(([key], v));
          case Bool(value: false):
            break;
          case Atom(name: 'boundary', args: []):
            out.add(([key], key));
          default:
            throw KernelTypeError('a discard selector returned $verdict');
        }
        next(i + 1);
      });
    }

    next(0);
  }

  void _fold(Family family, Object op, Value? identity, int depth, void Function(Value) k) {
    final leaves = family.leaves();
    if (leaves.any((l) => l.$1.length != depth)) throw const MixedDepthError();
    if (depth == 1) return _reduce([for (final (_, v) in leaves) v], op, identity, k);
    // The leaves are in keypath order, so each group of one parent is a run of them.
    final groups = <(Keypath, List<Value>)>[];
    for (final (path, v) in leaves) {
      final parent = path.sublist(0, depth - 1);
      if (groups.isEmpty || !_samePath(groups.last.$1, parent)) groups.add((parent, []));
      groups.last.$2.add(v);
    }
    final out = <(Keypath, Value)>[];
    void next(int i) {
      if (i == groups.length) return k(Family.fromLeaves(out));
      _reduce(groups[i].$2, op, identity, (v) {
        out.add((groups[i].$1, v));
        next(i + 1);
      });
    }

    next(0);
  }

  void _reduce(List<Value> values, Object op, Value? identity, void Function(Value) k) {
    if (values.isEmpty) return k(identity ?? const Atom('empty'));
    if (op == Prim.add) {
      for (final v in values) {
        if (v is Atom) return k(v);
      }
      if (values.every((v) => v is Float)) {
        return k(Float(exactSum([for (final v in values) (v as Float).x])));
      }
    }
    final plan = canonicalPlan(values.length), stack = <Value>[];
    void next(int i) {
      while (i < plan.length && plan[i] >= 0) {
        stack.add(values[plan[i++]]);
      }
      if (i == plan.length) return k(stack.single);
      final b = stack.removeLast(), a = stack.removeLast();
      _call2(op, a, b, (v) {
        stack.add(v);
        next(i + 1);
      });
    }

    next(0);
  }

  void _fixLattice(Term init, Term step, Term join, _Env env, void Function(Value) k) {
    _data(init, env, (x0) {
      _ev(step, env, (step) {
        _ev(join, env, (join) {
          void iterate(Value x) {
            _burn();
            _applyThen(step, [x], (next) {
              if (next is! Value) throw const KernelTypeError('a fix step returned a function');
              _call2(join, x, next, (joined) => joined == x ? k(x) : iterate(joined));
            });
          }

          iterate(x0);
        });
      });
    });
  }

  void _fixDefinedness(
    Term init,
    Term body,
    String self,
    String key,
    _Env env,
    void Function(Value) k,
  ) {
    _family(init, env, (d) {
      final fix = _Fix(++_fixes, SplayTreeSet.of(d.keys), body, self, key, env);
      void done(List<Value> stalled) {
        if (stalled.isNotEmpty) throw StalledError(stalled);
        k(
          Family.fromLeaves([
            for (final MapEntry(:key, :value) in fix.defined.entries) ([key], value.$1),
          ]),
        );
      }

      switch (schedule) {
        case Rounds():
          _inRounds(fix, null, done);
        case Chaotic(:final seed):
          _inRounds(fix, _SplitMix(seed), done);
        case Pull():
          _onDemand(fix, done);
      }
    });
  }

  /// Evaluates the entry of `fix` at `k` as round `round` sees the fix: `ok` gets its value,
  /// or `blocked` the key of an undefined entry it read. [undo] runs if another failure
  /// unwinds past the entry.
  void _entry(
    _Fix fix,
    int round,
    Value k,
    void Function(Value v) ok,
    void Function(Value read) blocked, [
    void Function()? undo,
  ]) {
    final env = fix.env.put(fix.self, _Partial(fix, round)).put(fix.key, k);
    final pure = _pure, depth = _depth;
    _stack.add(
      _Frame(
        (v) {
          if (v is! Value) throw const KernelTypeError('a fix entry is a function');
          ok(v);
        },
        undo,
        (stop) {
          if (stop is! _Undefined || stop.fix != fix.id) return false;
          _pure = pure;
          _depth = depth;
          blocked(stop.key);
          return true;
        },
      ),
    );
    _go(fix.body, env);
  }

  /// Defines the entries of `fix` round by round, or in a random order when `rng` is given,
  /// and passes on the keys left undefined.
  void _inRounds(_Fix fix, _SplitMix? rng, void Function(List<Value> stalled) done) {
    final waiting = SplayTreeMap<Value, List<Value>>();
    var ready = fix.domain.toList();
    void finish() => done([
      for (final k in fix.domain)
        if (!fix.defined.containsKey(k)) k,
    ]);
    void round(int r) {
      _burn();
      if (ready.isEmpty) return finish();
      rng?.shuffle(ready);
      final sees = rng != null ? _always : r;
      final batch = ready, defined = <Value>[];
      ready = [];
      void next(int i) {
        if (i == batch.length) {
          if (defined.isEmpty) return finish();
          for (final k in defined) {
            ready.addAll(waiting.remove(k) ?? const []);
          }
          ready.sort();
          return round(r + 1);
        }
        final k = batch[i];
        _entry(
          fix,
          sees,
          k,
          (v) {
            fix.defined[k] = (v, r);
            defined.add(k);
            next(i + 1);
          },
          (read) {
            waiting.putIfAbsent(read, () => []).add(k);
            next(i + 1);
          },
        );
      }

      next(0);
    }

    round(1);
  }

  /// Defines the entries of `fix` on demand: each entry first defines the entries it reads,
  /// and an entry that reads one being defined stalls with them.
  void _onDemand(_Fix fix, void Function(List<Value> stalled) done) {
    final keys = fix.domain.toList();
    void outer(int i) {
      while (i < keys.length &&
          (fix.defined.containsKey(keys[i]) || fix.stalled.contains(keys[i]))) {
        i++;
      }
      if (i == keys.length) {
        final stalled = fix.stalled.toList();
        fix.stalled.clear();
        return done(stalled);
      }
      final demanded = [keys[i]];
      fix.busy.add(keys[i]);
      void inner() {
        if (demanded.isEmpty) return outer(i + 1);
        _burn();
        final k = demanded.last;
        _entry(
          fix,
          _always,
          k,
          (v) {
            fix.defined[k] = (v, 0);
            fix.busy.remove(k);
            demanded.removeLast();
            inner();
          },
          (read) {
            if (fix.busy.contains(read) || fix.stalled.contains(read)) {
              for (final d in demanded) {
                fix.busy.remove(d);
                fix.stalled.add(d);
              }
              demanded.clear();
            } else {
              fix.busy.add(read);
              demanded.add(read);
            }
            inner();
          },
        );
      }

      inner();
    }

    outer(0);
  }

  /// Defines entry `k` of `fix` for a read of it, under [Pull].
  void _demand(_Fix fix, Value k) {
    _burn();
    fix.busy.add(k);
    _depth++;
    _entry(
      fix,
      _always,
      k,
      (v) {
        _depth--;
        fix.busy.remove(k);
        fix.defined[k] = (v, 0);
        _ret(v);
      },
      (read) {
        _depth--;
        fix.busy.remove(k);
        throw _Undefined(fix.id, read);
      },
      () => fix.busy.remove(k),
    );
  }

  void _generations(Value init, Object step, Object guard, GuardPos pos) {
    final frames = [init];
    void finish() => _ret(
      Family.fromLeaves([
        for (var t = 0; t < frames.length; t++) ([Int(t)], frames[t]),
      ]),
    );
    void goOn(void Function(bool) k) {
      _applyThen(guard, [frames.last], (verdict) {
        switch (verdict) {
          case Bool(:final value):
            k(value);
          case Atom():
            frames.add(verdict);
            k(false);
          case Value():
            throw KernelTypeError('a gen guard returned $verdict');
          default:
            throw const KernelTypeError('a gen guard returned a function');
        }
      });
    }

    late void Function() loop;
    void stepOnce() {
      _burn();
      _applyThen(step, [frames.last], (next) {
        if (next is! Value) throw const KernelTypeError('a gen step returned a function');
        frames.add(next);
        if (pos == GuardPos.after) {
          goOn((more) => more ? loop() : finish());
        } else {
          loop();
        }
      });
    }

    loop = () {
      if (pos == GuardPos.before) {
        goOn((more) => more ? stepOnce() : finish());
      } else {
        stepOnce();
      }
    };
    loop();
  }
}

Value _asData(Object v) =>
    v is Value ? v : throw const KernelTypeError('expected data, found a function');

bool _isAtom(Value v) => v is Atom;

bool _samePath(Keypath a, Keypath b) {
  if (a.length != b.length) return false;
  for (var i = 0; i < a.length; i++) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

/// `env` with the bindings `pat` makes when it matches `v`; null when it does not match.
_Env? _match(Pattern pat, Value v, _Env env) {
  _Env? all(List<Pattern> ps, List<Value> xs, _Env env) {
    if (ps.length != xs.length) return null;
    _Env? e = env;
    for (var i = 0; i < ps.length && e != null; i++) {
      e = _match(ps[i], xs[i], e);
    }
    return e;
  }

  switch ((pat, v)) {
    case (WildP(), _):
      return env;
    case (BindP(:final name), _):
      return env.put(name, v);
    case (LitP(:final value), _):
      return value == v ? env : null;
    case (AnyAtomP(), Atom()):
      return env;
    case (AtomP(:final name, :final args), Atom a):
      return a.name == name && a.fields.isEmpty ? all(args, a.args, env) : null;
    case (FieldsP(:final name, :final fields), Atom a):
      if (a.name != name || a.fields.isEmpty) return null;
      _Env? e = env;
      for (final (f, p) in fields) {
        final i = a.fields.indexOf(f);
        if (i < 0) return null;
        e = _match(p, a.args[i], e!);
        if (e == null) return null;
      }
      return e;
    case (TupleP(:final items), Tuple(items: final xs)):
      return all(items, xs, env);
    default:
      return null;
  }
}

/// `p` applied to data none of which is a failure atom, except where `p` takes atoms.
Value primData(Prim p, List<Value> vals) {
  Never ty() => throw KernelTypeError('$p applied to ${vals.join(', ')}');
  switch ((p, vals)) {
    case (
          Prim.add || Prim.sub || Prim.mul || Prim.intDiv || Prim.mod || Prim.pow,
          [final a, final b],
        )
        when a.numberKind == 0 && b.numberKind == 0:
      return _intBinary(p, a, b) ?? ty();
    case (Prim.neg, [Int(:final value)]):
      return value == _minInt ? sized(-BigInt.from(value)) : Int(-value);
    case (Prim.neg, [Big(:final value)]):
      return sized(-value);
    case (Prim.add || Prim.sub || Prim.mul || Prim.div, [Rat a, Rat b]):
      final Rat r;
      switch (p) {
        case Prim.add:
          r = a + b;
        case Prim.sub:
          r = a - b;
        case Prim.mul:
          r = a * b;
        default:
          final q = a.div(b);
          if (q == null) return const Atom('divByZero');
          r = q;
      }
      if (r.bits > maxBits) throw const OverflowError();
      return r;
    case (Prim.neg, [Rat a]):
      return -a;
    case (Prim.add, [Float(x: final a), Float(x: final b)]):
      return Float(a + b);
    case (Prim.sub, [Float(x: final a), Float(x: final b)]):
      return Float(a - b);
    case (Prim.mul, [Float(x: final a), Float(x: final b)]):
      return Float(a * b);
    case (Prim.div, [Float(x: final a), Float(x: final b)]):
      return Float(a / b);
    case (Prim.neg, [Float(x: final a)]):
      return Float(-a);
    case (Prim.concat, [Str(text: final a), Str(text: final b)]):
      return Str.text(Text.join(a, b));
    case (Prim.pow, [Float(x: final a), Float(x: final b)]):
      return Float(math.pow(a, b).toDouble());
    case (Prim.eq, [final a, final b]):
      return Bool(a.surfaceEq(b));
    case (Prim.ne, [final a, final b]):
      return Bool(!a.surfaceEq(b));
    case (Prim.lt || Prim.le || Prim.gt || Prim.ge, [Float(x: final a), Float(x: final b)]):
      return Bool(switch (p) {
        Prim.lt => a < b,
        Prim.le => a <= b,
        Prim.gt => a > b,
        _ => a >= b,
      });
    case (Prim.lt || Prim.le || Prim.gt || Prim.ge || Prim.min || Prim.max, [final a, final b]):
      final x = a.numberKind, y = b.numberKind;
      final same = x == null && y == null ? a.runtimeType == b.runtimeType : x == y;
      if (!same) ty();
      final o = a.surfaceCmp(b);
      return switch (p) {
        Prim.lt => Bool(o != null && o < 0),
        Prim.le => Bool(o != null && o <= 0),
        Prim.gt => Bool(o != null && o > 0),
        Prim.ge => Bool(o != null && o >= 0),
        Prim.min => a.compareTo(b) <= 0 ? a : b,
        _ => a.compareTo(b) <= 0 ? b : a,
      };
    case (Prim.and, [Bool(value: final a), Bool(value: final b)]):
      return Bool(a && b);
    case (Prim.or, [Bool(value: final a), Bool(value: final b)]):
      return Bool(a || b);
    case (Prim.not, [Bool(:final value)]):
      return Bool(!value);
    case (Prim.get || Prim.tupleGet, [Family f, final k]):
      return f[k] ?? const Atom('notFound');
    case (Prim.count, [Family f]):
      return Int(f.length);
    case (Prim.union, [Family a, Family b]):
      return a.union(b);
    case (Prim.path, _):
      return Path(List.of(vals));
    case (Prim.atom, [Str(text: final name), Tuple(items: final names), ...final args])
        when names.isEmpty:
      return Atom(name.text, args);
    case (Prim.atom, [Str(text: final name), Tuple(items: final names), ...final args])
        when names.length == args.length:
      final fields = <(String, Value)>[];
      for (var i = 0; i < names.length; i++) {
        final n = names[i];
        if (n is! Str) ty();
        fields.add((n.text.text, args[i]));
      }
      return Atom.named(name.text, fields) ?? ty();
    case (Prim.pathKey, [Path(:final keys), Int(value: final i)]):
      return i >= 0 && i < keys.length ? keys[i] : const Atom('notFound');
    case (Prim.pathLen, [Path(:final keys)]):
      return Int(keys.length);
    case (Prim.tuple, _):
      return Tuple(List.of(vals));
    case (Prim.tupleGet, [Tuple(:final items), Int(value: final i)]):
      return i >= 0 && i < items.length ? items[i] : ty();
    case (
      Prim.show ||
          Prim.castInt ||
          Prim.castRat ||
          Prim.castF64 ||
          Prim.abs ||
          Prim.len ||
          Prim.lower ||
          Prim.upper ||
          Prim.trim,
      [final x],
    ):
      return word(p, x);
    case (Prim.sum, [Tuple(:final items)]):
      if (items.any(_isAtom)) return Value.mergeFailures(items.where(_isAtom));
      if (items.isEmpty) return const Int(0);
      if (items.first.numberKind == null) ty();
      var total = items.first;
      for (final x in items.skip(1)) {
        total = primData(Prim.add, [total, x]);
      }
      return total;
    default:
      ty();
  }
}

const _minInt = -0x8000000000000000;

/// An integer operation; null when the operation has no integer result (a negative power).
Value? _intBinary(Prim p, Value a, Value b) {
  if ((a, b) case (Int(value: final x), Int(value: final y))) {
    switch (p) {
      case Prim.add:
        final r = x + y;
        if ((x ^ r) & (y ^ r) >= 0) return Int(r);
      case Prim.sub:
        final r = x - y;
        if ((x ^ y) & (x ^ r) >= 0) return Int(r);
      case Prim.mul:
        const half = 1 << 31;
        if (x > -half && x < half && y > -half && y < half) return Int(x * y);
      case Prim.intDiv when y != 0 && !(x == _minInt && y == -1):
        return Int((x - x % y) ~/ y);
      case Prim.mod when y != 0:
        return Int(x % y);
      default:
    }
  }
  final x = a.asBigInt!, y = b.asBigInt!;
  switch (p) {
    case Prim.add:
      return sized(x + y);
    case Prim.sub:
      return sized(x - y);
    case Prim.mul:
      return sized(x * y);
    case Prim.intDiv || Prim.mod when y == BigInt.zero:
      return const Atom('divByZero');
    case Prim.intDiv:
      return sized((x - x % y) ~/ y);
    case Prim.mod:
      return sized(x % y);
    default:
      if (y.isNegative) return null;
      if (x.abs() <= BigInt.one) {
        return y == BigInt.zero || (x.isNegative && y.isEven) ? const Int(1) : Value.integer(x);
      }
      if (!y.isValidInt || bitsOf(x) * y.toInt() > maxBits + 64) throw const OverflowError();
      return sized(x.pow(y.toInt()));
  }
}
