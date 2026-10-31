/// The canonical serialization. Every node is a tag byte followed by its fields; a sequence is
/// its length then its items, a string its length in bytes then its UTF-8, and lengths and
/// integers are little-endian 64-bit words. Each tag fixes the fields that follow, so the
/// encoding is self-delimiting and two different normal forms never share an encoding.
///
/// Binders are canonical by then, so a binder is written by its count alone (a lambda's
/// parameters, a pattern's bind), and a bound variable by its level.
library;

import 'dart:convert';
import 'dart:typed_data';

import '../../address.dart';
import '../kernel/term.dart';
import '../kernel/text.dart';
import '../kernel/value.dart';
import '../store/interval.dart';
import 'binders.dart';
import 'canon.dart';
import 'domain.dart';

/// How a free variable resolves: to the address of the definition it names, or to null.
typedef Refs = ContentAddress? Function(String name);

final class _Out {
  final bytes = BytesBuilder(copy: false);
  final Refs refs;
  final _word = ByteData(8);

  _Out(this.refs);

  void tag(int t) => bytes.addByte(t);

  void word(int n) {
    _word.setInt64(0, n, Endian.little);
    bytes.add(Uint8List.fromList(_word.buffer.asUint8List()));
  }

  void str(String s) {
    final b = utf8.encode(s);
    word(b.length);
    bytes.add(b);
  }

  void end(End e) {
    switch (e) {
      case NegInf():
        tag(0);
      case Fin(:final v):
        tag(1);
        word(v);
      case PosInf():
        tag(2);
    }
  }

  void domain(Domain d) {
    word(d.ints.pieces.length);
    for (final (lo, hi) in d.ints.pieces) {
      end(lo);
      end(hi);
    }
    switch (d.congruence.modulus) {
      case null:
        tag(0);
      case final m:
        tag(1);
        word(m);
        word(d.congruence.residue);
    }
  }

  void value(Value v) {
    switch (v) {
      case Bool(value: final b):
        tag(0);
        tag(b ? 1 : 0);
      case Int(value: final n):
        tag(1);
        word(n);
      case Float(:final x):
        tag(2);
        word((ByteData(8)..setFloat64(0, x)).getInt64(0));
      case Str(:final text):
        tag(3);
        str(text.text);
      case Atom(:final name, fields: [], :final args):
        tag(4);
        str(name);
        values(args);
      case Atom(:final name, :final fields, :final args):
        tag(10);
        str(name);
        word(fields.length);
        fields.forEach(str);
        values(args);
      case Big(value: final n):
        tag(8);
        str('$n');
      case Rat(:final num, :final den):
        tag(9);
        str('$num');
        str('$den');
      case Tuple(:final items):
        tag(5);
        values(items);
      case Path(:final keys):
        tag(6);
        values(keys);
      case Family f:
        tag(7);
        word(f.length);
        for (final (k, v) in f.entries) {
          value(k);
          value(v);
        }
    }
  }

  void values(List<Value> vs) {
    word(vs.length);
    vs.forEach(value);
  }

  void pattern(Pattern p) {
    switch (p) {
      case WildP():
        tag(0);
      case BindP():
        tag(1);
      case LitP(:final value):
        tag(2);
        this.value(value);
      case AtomP(:final name, :final args):
        tag(3);
        str(name);
        patterns(args);
      case TupleP(:final items):
        tag(4);
        patterns(items);
      case AnyAtomP():
        tag(5);
      case FieldsP(:final name, :final fields):
        tag(6);
        str(name);
        word(fields.length);
        for (final (f, p) in fields) {
          str(f);
          pattern(p);
        }
    }
  }

  void patterns(List<Pattern> ps) {
    word(ps.length);
    ps.forEach(pattern);
  }

  /// An evidence record, its properties in name order, each with its grade.
  void evidence(Evidence ev) {
    word(ev.length);
    for (final property in ev.keys.toList()..sort(compareUtf8)) {
      str(property);
      tag(ev[property]!.index);
    }
  }

  void terms(List<Term> ts) {
    word(ts.length);
    ts.forEach(term);
  }

  void term(Term t) {
    switch (t) {
      case Lit(:final value):
        tag(1);
        this.value(value);
      case Var(:final name):
        if (levelOf(name) case final level?) {
          tag(2);
          word(level);
        } else if (refs(name) case final a?) {
          tag(3);
          bytes.add(a.bytes);
        } else {
          tag(4);
          str(name);
        }
      case Lam(:final params, :final body):
        tag(5);
        word(params.length);
        term(body);
      case App(:final f, :final args):
        tag(6);
        term(f);
        terms(args);
      case PrimApp(:final prim, :final args):
        tag(7);
        str(prim.label);
        terms(args);
      case PrimFn(:final prim):
        tag(8);
        str(prim.label);
      case Let(:final value, :final body):
        tag(9);
        term(value);
        term(body);
      case If(:final cond, :final then, :final orElse):
        tag(10);
        term(cond);
        term(then);
        term(orElse);
      case Match(:final scrutinee, :final arms):
        tag(11);
        term(scrutinee);
        word(arms.length);
        for (final (p, arm) in arms) {
          pattern(p);
          term(arm);
        }
      case Fam(:final domain, :final body):
        tag(12);
        term(domain);
        term(body);
      case Reindex(:final family, :final kf, :final vf, :final witness):
        tag(13);
        term(family);
        term(kf);
        term(vf);
        switch (witness) {
          case Residue():
            tag(0);
          case Catalog(:final law):
            tag(1);
            str(law);
        }
      case Discard(:final family, :final sel):
        tag(14);
        term(family);
        term(sel);
      case Fold(:final family, :final op, :final identity, :final depth, :final ev):
        tag(15);
        term(family);
        term(op);
        if (identity == null) {
          tag(0);
        } else {
          tag(1);
          term(identity);
        }
        word(depth);
        evidence(ev);
      case Fix(:final init, :final step, :final kind, :final ev):
        tag(16);
        term(init);
        term(step);
        switch (kind) {
          case Lattice(:final join):
            tag(0);
            term(join);
          case Definedness():
            tag(1);
        }
        evidence(ev);
      case Gen(:final init, :final step, :final guard, :final pos):
        tag(17);
        term(init);
        term(step);
        term(guard);
        tag(pos.index);
      case Read(:final port):
        tag(18);
        str(port);
      case Push(:final port, :final value):
        tag(19);
        str(port);
        term(value);
    }
  }
}

/// The serialization of a definition in normal form.
Uint8List serializeDef(Def d, Refs refs) {
  final out = _Out(refs)..str(d.name);
  if (d.domain case final dom?) {
    out
      ..tag(1)
      ..domain(dom);
  } else {
    out.tag(0);
  }
  out.word(d.facets.length);
  for (final f in d.facets) {
    out
      ..tag(f.hint ? 1 : 0)
      ..str(f.kind)
      ..value(f.value);
  }
  out.term(d.body);
  return out.bytes.takeBytes();
}
