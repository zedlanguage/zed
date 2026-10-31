/// Step M0.7: the canonicalizer (DESIGN.md sec:ir, "Identity"). Definitions from ordinary
/// programs (an invoice total, a running balance, a status-code check) written with different
/// local names, facets in different orders, and domains spelled differently, and the content
/// addresses they get.
library;

import 'package:zed/address.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';

/// No definition resolves: every free variable is hashed by name.
ContentAddress? none(String _) => null;

/// The definition `name = body` with no domain and no facets.
Def def(String name, Term body) => Def(name, body);

/// A facet that is not a hint.
Facet facet(String kind, Object value) => Facet(kind, valueOf(value));

ContentAddress addr(Def d) => address(d, none);
