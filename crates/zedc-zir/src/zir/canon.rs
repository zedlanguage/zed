//! The canonicalizer on ZIR (step L1.32): the four rules of step M0.7 ([`crate::canon`]),
//! moved onto the graph unchanged, and the content address taken over the normal form.
//!
//! A graph has no local names but one kind: a match pattern's binders, whose written names a
//! region reads by position, never by name. So the *binders* rule renames the first written
//! pattern binder in preorder to its level, its index among the binders of its pattern, which
//! is the number of the arm region's arguments before the one it binds; its written name
//! becomes a hint facet `binder (index, name)` on that argument's edge. The *hints*, *facets*
//! and *domain* rules are [`crate::canon::RULES`] themselves, applied to one edge at a time,
//! the edges taken in preorder: a region's arguments, then each node's outputs and then its
//! regions, in order. Each rule applies at the first place it applies, in priority order,
//! until none applies; the ranks are the sums of the per-edge ranks, and the tuple of them
//! decreases lexicographically at every step, as it does on kernel terms.
//!
//! The address is the BLAKE3-256 hash of `zed-zir\0` and the binary form ([`super::binary`])
//! of the normal form, each string held as one block. Two graphs
//! that differ only in binder names, hints, facet order or repeats, the spelling of one set of
//! integers, or the trees that hold equal strings, share it.
//!
//! Every rule acts on one edge, or on one pattern, alone, and the binder rule's hint is
//! removed by the hints rule. So [`canonicalize`] normalizes each edge and each pattern in one
//! pass and reaches the normal form that [`step`] reaches: each edge's facets are sorted once,
//! `O(F log F)` comparisons for an edge of `F` facets, so `O(n log n)` for all the facets of a
//! graph of size `n`, and each edge's integer facts are put in normal form once; and
//! [`key`] hashes a node from the keys of its regions, so the lowering keys each new node
//! without walking the regions below it again.

use std::collections::{HashMap, hash_map};
use std::sync::Arc;

use zed_kernel::num::TooLarge;
use zed_kernel::term::{Pattern, Term};
use zed_kernel::text::Text;
use zed_kernel::text::names::{Name, Names};
use zed_kernel::value::{Atom, Family, Value};

use super::binary::Held;
use super::{Edge, Node, Op, Region, RegionKind, Src, binary};
use crate::canon::binders::{level_name, level_of};
use crate::canon::{Def, Facet, RULES};
use zedc_base::address::ContentAddress;

/// The ranks of the four rules on `g`, in rule order.
pub fn ranks(g: &Region) -> [u64; 4] {
    let mut r = [written(g), 0, 0, 0];
    each_edge(g, &mut |e| {
        if let Edge::Value(v) = e {
            let d = def(v);
            for (k, rule) in RULES.iter().enumerate().skip(1) {
                r[k] += (rule.rank)(&d);
            }
        }
    });
    r
}

/// One rewrite: the first rule that applies anywhere, applied at the first place it applies.
/// Returns the rule's name, or `None` when `g` is in normal form.
pub fn step(g: &mut Region) -> Option<&'static str> {
    if rename_first(g) {
        return Some(RULES[0].name);
    }
    for rule in &RULES[1..] {
        let mut done = false;
        each_edge_mut(g, &mut |e| {
            if let (false, Edge::Value(v)) = (done, &mut *e) {
                let mut d = def(v);
                if (rule.apply)(&mut d) {
                    v.domain = d.domain.expect("an edge has a domain");
                    v.facets = d.facets;
                    done = true;
                }
            }
        });
        if done {
            return Some(rule.name);
        }
    }
    None
}

/// The normal form of `g`: the graph [`step`] reaches, in one pass.
// Complexity tradeoff: the naive normalizer applies one rule step at a time (`step`) and
// restarts from the top after each rewrite, O(k) steps of O(k) each for k edges and patterns,
// O(k²) (COMPLEXITY.md Z3). Here every rule acts on one edge or one pattern alone, so each is
// put in normal form once, in one pass, O(k) plus `normal_edge`'s O(F log F) per edge of F
// facets (Z18). Precondition: no rule reads more than one edge or pattern; a rule that did
// would need the restart again. Nothing is refused. Test
// `l01_32_canonical_zir::fuzz::the_one_pass_normal_form_is_the_one_the_steps_reach`.
pub fn canonicalize(g: &Region) -> Region {
    let mut g = g.clone();
    normalize(&mut g);
    g
}

/// Puts each edge and pattern of `g` in normal form, from a stack of the regions left to do:
/// each is normalized alone, so the order does not matter.
fn normalize(g: &mut Region) {
    let mut todo = vec![g];
    while let Some(r) = todo.pop() {
        r.args.iter_mut().for_each(normal_edge);
        for n in &mut r.nodes {
            normal_shell(n);
            todo.extend(n.regions.iter_mut().map(Arc::make_mut));
        }
    }
}

/// A node's operation and outputs in normal form; its regions are left alone.
fn normal_shell(n: &mut Node) {
    n.outputs.iter_mut().for_each(normal_edge);
    if let Op::Match(ps) = &mut n.op {
        for p in ps {
            rename_all(p, &mut 0);
        }
    }
}

/// An edge in normal form, the one the rules after the binder rule reach (DESIGN M0.7): its
/// hints dropped, its facets sorted once and each run of equal ones kept once, and its integer
/// facts normal. `O(F log F)` comparisons for `F` facets. The facets end in the one order with
/// no adjacent pair out of order or equal, since a facet's [`Ord`] is total and its ties are
/// exactly `==`; so which of two equal facets the unstable sort puts first does not matter.
fn normal_edge(e: &mut Edge) {
    if let Edge::Value(v) = e {
        v.facets.retain(|f| !f.hint);
        zed_collections::sorted::sort_dedup(&mut v.facets);
        v.domain = v.domain.normal();
    }
}

/// Whether the binder `name` at preorder position `index` among its pattern's binders is in
/// normal form: spelled as the level `index` itself. A binder spelled as another level, such as
/// `$$5` read from the text form in the first place, counts as written and is renamed, since an
/// arm reads its binders by position and the name must not change the address.
fn canonical_at(name: &str, index: usize) -> bool {
    level_of(name) == Some(index)
}

/// Each written binder of `p` renamed to its level, the number of binders before it.
fn rename_all(p: &mut Pattern, index: &mut usize) {
    p.rename_binders(|name| {
        if !canonical_at(name, *index) {
            *name = level_name(*index);
        }
        *index += 1;
    });
}

/// The bytes [`node_key`] hashes for `n` besides its regions' keys: the binary form of the
/// one-node region holding `n`'s operation, inputs and outputs in normal form, each string
/// written as its length and hash ([`binary::encode_keyed`]), with those strings in order; or
/// [`TooLarge`] when the system refuses the memory to write one of its exact numbers.
fn shell_bytes(n: &Node) -> Result<(Vec<u8>, Vec<Held>), TooLarge> {
    let mut shell = Node {
        op: n.op.clone(),
        inputs: n.inputs.clone(),
        outputs: n.outputs.clone(),
        regions: Vec::new(),
    };
    normal_shell(&mut shell);
    binary::encode_keyed(&Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: vec![shell],
        results: Vec::new(),
    })
}

/// The bytes [`region_key`] hashes for `r` besides its nodes' keys: the binary form of its
/// kind, its arguments in normal form and its results, written as at [`shell_bytes`], with the
/// strings written; or [`TooLarge`] as there.
fn region_bytes(r: &Region) -> Result<(Vec<u8>, Vec<Held>), TooLarge> {
    let mut shell = Region {
        kind: r.kind,
        args: r.args.clone(),
        nodes: Vec::new(),
        results: r.results.clone(),
    };
    shell.args.iter_mut().for_each(normal_edge);
    binary::encode_keyed(&shell)
}

/// The key of node `n` whose regions have the keys `regions`: equal keys mean equal normal
/// forms of the one-node regions holding the nodes (up to the hashes, of the bytes and of the
/// strings; [`Shape`] decides it without them), or [`TooLarge`] as at `shell_bytes`. A string
/// counts by its text, not by the tree it is held in.
pub fn node_key(n: &Node, regions: &[ContentAddress]) -> Result<ContentAddress, TooLarge> {
    Ok(key_of(&shell_bytes(n)?.0, regions))
}

/// The key of a node whose [`shell_bytes`] are `shell` and whose regions have the keys
/// `regions`.
fn key_of(shell: &[u8], regions: &[ContentAddress]) -> ContentAddress {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir-node\0");
    h.update(shell);
    h.update(&(regions.len() as u64).to_le_bytes());
    for r in regions {
        h.update(&r.0);
    }
    ContentAddress::hashed(&h)
}

/// The key of region `r` whose nodes' regions have the keys `inner`, one list per node, or
/// [`TooLarge`] as at `shell_bytes`.
pub fn region_key(r: &Region, inner: &[Vec<ContentAddress>]) -> Result<ContentAddress, TooLarge> {
    let mut h = region_hasher(&region_bytes(r)?.0, r.nodes.len());
    for (n, keys) in r.nodes.iter().zip(inner) {
        h.update(&node_key(n, keys)?.0);
    }
    Ok(ContentAddress::hashed(&h))
}

/// The hasher of a region's key, given its [`region_bytes`] and its number of nodes, before
/// its nodes' keys.
fn region_hasher(bytes: &[u8], nodes: usize) -> blake3::Hasher {
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir-region\0");
    h.update(bytes);
    h.update(&(nodes as u64).to_le_bytes());
    h
}

/// The regions a lowering has finished, each distinct normal form numbered once, in the order
/// first met. A region is held by its `Contents`, so two regions have one number exactly when
/// they have equal normal forms, by induction on their depth, and a [`Shape`] holds its regions
/// by their numbers.
// Complexity tradeoff: the contents of every distinct region are held until the lowering ends,
// as many bytes as the graph's binary form, wide constants included. Why: a shape compared by
// its regions' numbers costs the bytes of its own operation, inputs and outputs, and builds
// nothing, so the order asks no memory and cannot be refused; the order it replaces wrote the
// regions' constants again at each comparison, two at once, and a refusal there could only
// stop the compiler. Trigger: a lowering of wide constants inside lambdas or arms, which holds
// them twice, once in the graph and once here. Test:
// `l01_33_lowering::asks` (refused at two widths, one node when memory is given) and
// `l01_37a_short_addresses::scaling`. A complete solution would hold each node's bytes once,
// shared by its shape and by its region's contents, which needs them written after the
// region's arguments are renumbered, before the node is entered.
#[derive(Default)]
pub struct Regions {
    contents: HashMap<Contents, usize>,
    /// The strings of the regions and of the nodes' shapes.
    strings: Strings,
}

/// What decides a region's normal form, given its regions' numbers: the bytes [`region_key`]
/// hashes for it besides its nodes' keys, then for each node the bytes [`node_key`] hashes for
/// it besides its regions' keys, with the numbers of its regions; and the numbers
/// ([`Strings`]) of the strings those bytes write by their hashes, in order. The bytes give
/// where each string stands, and the numbers which text it is.
#[derive(PartialEq, Eq, Hash)]
struct Contents {
    region: Vec<u8>,
    nodes: Vec<(Vec<u8>, Vec<usize>)>,
    strings: Vec<u64>,
}

/// The strings of a lowering's keyed bytes ([`binary::encode_keyed`]), each distinct text
/// numbered once in the order first met: two strings get one number exactly when their texts
/// are equal, however each is held, so a [`Shape`] or a region's contents compared with the
/// numbers decides equal normal forms exactly, as with the strings written out.
///
/// No two different texts share a number: a number is given once, to the first text of its
/// length and hash, and given again to a text only when (1) it is that text's node, and a node
/// never changes; (2) both are held as one block and their bytes are equal; or (3) its
/// canonical name in `names` ([`Names`]) is the name of a text with that number. A name stands for
/// one rule of the dictionary and a rule for one text, the rules a name's rule expands to being
/// fixed when it is made, so equal names are equal texts. Texts of different lengths or hashes
/// are different and get numbers apart. Equal texts have one length and hash, so they meet in
/// one bucket; there they get one number by (1) or (2), or by (3) since equal texts get one
/// canonical name (Mehlhorn, Sundar and Uhrig, "Maintaining dynamic sequences under equality
/// tests in polylogarithmic time", Algorithmica 17(2), 183-198, 1997,
/// doi:10.1007/BF02522825). Were that to fail, two equal constants would be two nodes, a
/// missed merge, never a wrong one.
// The paper gives each sequence a signature by repeated rounds of two steps: runs of one
// symbol become one symbol, then the sequence is cut into short blocks by deterministic coin
// tossing, each cut decided by a few neighbors only, and each distinct run or block gets the
// next number from one shared table. Because every choice is local and the table maps equal
// contents to one number, equal sequences get one signature however they were built, and
// different ones different signatures. `Names` (in zed-kernel `text::names`) implements it;
// this module uses only that property. Checked 2026-11-20: the DOI, volume, issue and pages
// on Crossref; the paper not read (no free copy found), the method from memory. In the step
// tests `l01_32_canonical_zir::string_trees`,
// `equal_strings_in_different_trees_share_the_zir_address` checks that one 900-byte text held
// in three trees gets one address, which catches a name that depends on the tree, and
// `different_strings_get_different_zir_addresses` and
// `different_constants_in_one_shape_stay_two_nodes` check that four texts of one length and
// shape stay apart. They cover a few shapes, not every way a parse could go wrong.

// Complexity tradeoff: the naive key writes each string's bytes, O(N) for N bytes, and a
// string doubled k times is 2^k bytes in O(k) nodes, so a build holding a doubled string as a
// constant writes 2^62 bytes (BUILD-doubling-60s); the form that replaced it wrote the tree,
// O(m) for m nodes, but equal texts in different trees were then different constants and two
// `++` nodes over them were never merged (ZIR-string-cse-tree). A byte comparison on equal
// hashes is exact but O(N) on two equal texts built apart, so the doubled string again.
// Here a string costs its `Text::poly_hash`, O(m) plus the bytes of its distinct blocks, and
// one hash lookup; a second text of the same length and hash costs one node comparison, or
// one byte comparison of two blocks whose bytes the hash has just read; only two texts held
// in different trees, or a collision of the hash, are named, `Names::name`'s O(n log N) for n
// nodes not named before plus a parse of their blocks' bytes, each node once per lowering.
// Tradeoff: the names, with the texts they keep alive, are held until the lowering ends.
// Nothing is refused. Tests `l01_32_canonical_zir::string_trees` and the scaling test
// `l01_32_canonical_zir::bench::string_trees::equal_strings_in_doubled_trees_are_merged_in_linear_time`.
#[derive(Default)]
pub struct Strings {
    /// The distinct texts of each length and hash.
    buckets: HashMap<(u64, u64), Bucket>,
    /// The canonical names of the texts compared by name.
    names: Names,
    /// The numbers given.
    count: u64,
}

/// The texts of one length and hash: the first met and its number, and once a text that is
/// neither its node nor a block equal to it is met, every text met by its canonical name.
struct Bucket {
    first: Text,
    number: u64,
    named: Option<HashMap<Name, u64>>,
}

impl Strings {
    /// The number of the string `(len, hash, text)`, given now if no equal text has one.
    pub fn number(&mut self, (len, hash, t): &Held) -> u64 {
        let Strings {
            buckets,
            names,
            count,
        } = self;
        let mut fresh = || {
            *count += 1;
            *count - 1
        };
        let b = match buckets.entry((*len, *hash)) {
            hash_map::Entry::Vacant(e) => {
                let number = fresh();
                e.insert(Bucket {
                    first: t.clone(),
                    number,
                    named: None,
                });
                return number;
            }
            hash_map::Entry::Occupied(e) => e.into_mut(),
        };
        let same_node = b.first.node_id() == t.node_id();
        if same_node || (b.first.is_flat() && t.is_flat() && b.first == *t) {
            return b.number;
        }
        let named = b
            .named
            .get_or_insert_with(|| HashMap::from([(names.name(&b.first), b.number)]));
        *named.entry(names.name(t)).or_insert_with(fresh)
    }
}

impl Regions {
    /// The key of region `r` (what [`region_key`] gives) and its number. `keys` and `numbers`
    /// are the keys and the numbers of each node's regions, one list per node. [`TooLarge`]
    /// as at `shell_bytes`, or when the system refuses the memory to list the nodes.
    pub fn enter(
        &mut self,
        r: &Region,
        keys: &[Vec<ContentAddress>],
        numbers: Vec<Vec<usize>>,
    ) -> Result<(ContentAddress, usize), TooLarge> {
        let (region, held) = region_bytes(r)?;
        let mut strings: Vec<u64> = held.iter().map(|s| self.strings.number(s)).collect();
        let mut h = region_hasher(&region, r.nodes.len());
        let mut nodes = Vec::new();
        nodes
            .try_reserve_exact(r.nodes.len())
            .map_err(|_| TooLarge::of_bytes(r.nodes.len() * size_of::<(Vec<u8>, Vec<usize>)>()))?;
        for ((n, keys), numbers) in r.nodes.iter().zip(keys).zip(numbers) {
            let (shell, held) = shell_bytes(n)?;
            strings.extend(held.iter().map(|s| self.strings.number(s)));
            h.update(&key_of(&shell, keys).0);
            nodes.push((shell, numbers));
        }
        let next = self.contents.len();
        let contents = Contents {
            region,
            nodes,
            strings,
        };
        let number = *self.contents.entry(contents).or_insert(next);
        Ok((ContentAddress::hashed(&h), number))
    }
}

/// A node's normal form as an ordered key: the bytes [`node_key`] hashes for its operation,
/// inputs and outputs, then the numbers of its regions among the regions the lowering has
/// finished ([`Regions`]), then the numbers of the strings those bytes write by their hashes
/// ([`Strings`]). Two shapes are equal exactly when the nodes have equal normal forms,
/// so equal shapes have equal keys, and a key never decides equality alone (DESIGN.md
/// sec:theories, the trusted base; step L1.37a). The lowering keeps the nodes of one key in a
/// map ordered by shape, so keys that collide cost `O(log k)` comparisons for `k` nodes of the
/// key, each at most the bytes of the smaller node's own operation, inputs and outputs; a
/// comparison builds nothing.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Shape {
    shell: Vec<u8>,
    regions: Vec<usize>,
    strings: Vec<u64>,
}

impl Shape {
    /// The shape of `n`, whose regions have the numbers `regions` in `finished`, its strings
    /// numbered there. [`TooLarge`] as at `shell_bytes`.
    pub fn of(n: &Node, regions: Vec<usize>, finished: &mut Regions) -> Result<Shape, TooLarge> {
        let (shell, held) = shell_bytes(n)?;
        Ok(Shape {
            shell,
            regions,
            strings: held.iter().map(|s| finished.strings.number(s)).collect(),
        })
    }

    /// The key of the node of this shape whose regions have the keys `regions`: what
    /// [`node_key`] gives, without encoding the node again.
    pub fn key(&self, regions: &[ContentAddress]) -> ContentAddress {
        key_of(&self.shell, regions)
    }
}

/// The key of `g` from the bottom up: what [`region_key`] gives with every region's key, or
/// [`TooLarge`] as at `shell_bytes`.
pub fn key(g: &Region) -> Result<ContentAddress, TooLarge> {
    // Each open region with the keys of its nodes' regions found so far, one list per node
    // begun.
    let mut open: Vec<(&Region, Vec<Vec<ContentAddress>>)> = vec![(g, Vec::new())];
    loop {
        let (r, inner) = open
            .last_mut()
            .expect("the loop returns when the root ends");
        let r = *r;
        if let Some(keys) = inner.last()
            && let Some(sub) = r.nodes[inner.len() - 1].regions.get(keys.len())
        {
            open.push((sub, Vec::new()));
        } else if inner.len() < r.nodes.len() {
            inner.push(Vec::new());
        } else {
            let k = region_key(r, inner)?;
            open.pop();
            match open.last_mut() {
                Some((_, up)) => up.last_mut().expect("a node is begun").push(k),
                None => return Ok(k),
            }
        }
    }
}

/// The content address of `g`: the hash of the binary form of its normal form, each string
/// held as one block (`flat_strings`). [`TooLarge`] as at `shell_bytes`, or when the system
/// refuses the memory to write a string held in parts into one block.
pub fn address(g: &Region) -> Result<ContentAddress, TooLarge> {
    let mut normal = canonicalize(g);
    flat_strings(&mut normal)?;
    let mut h = blake3::Hasher::new();
    h.update(b"zed-zir\0");
    h.update(&binary::encode(&normal)?);
    Ok(ContentAddress::hashed(&h))
}

/// Holds each string of `g`'s constants and matched literals as one block, its text unchanged,
/// so that equal strings are written alike by the binary form, which writes a string as the
/// tree it is held in (`binary::W::text`). Folding `++` of constants joins two texts and keeps
/// both parts (`Text::join`), so `("a"*300 ++ "b"*300) ++ "c"*300`, its mirror and the literal
/// of the same 900 bytes are one string in three trees (item ZIR-string-tree-address, test
/// `l01_32_canonical_zir::string_trees`). Edges need nothing: the binary form writes an edge
/// as its text form, which prints a string's text. The address scheme's version number, since
/// removed, was left unchanged: a graph whose strings are each one block keeps its address, and any
/// other graph now gets the address the equal graph with its strings held as blocks always had, so
/// no address stands for two normal forms across this change (`normal_form_pins` hashes graphs read
/// from text, whose strings are blocks).
// Complexity tradeoff: the binary form writes each distinct node of a string's tree once, so a
// string doubled k times, 2^k bytes in k nodes, costs O(k) to write (BUILD-doubling-60s). Here
// the address writes a string held in parts as one block, O(N) time and memory for N bytes,
// so that doubled string costs 2^k, and is refused as [`TooLarge`] once the system refuses the
// memory, where before it was addressed in O(k). Why: a form of a string that depends only on
// its text and costs less than its bytes is the canonical parse (`zed_kernel::text::names`),
// whose cost and whose place under the address are open question A106; this item does not
// decide it. The address stays linear in the bytes of the graph's strings, and only tests take
// a ZIR address (the build keys nodes by `node_key`, which writes a string by its length and
// hash, and numbers it exactly in `Strings`, ZIR-string-cse-tree). A string held
// as one block is not copied. Nothing is refused but the memory. Test
// `l01_32_canonical_zir::string_trees`, and the scaling test
// `l01_32_canonical_zir::bench::string_trees`.
fn flat_strings(g: &mut Region) -> Result<(), TooLarge> {
    let mut todo = vec![g];
    while let Some(r) = todo.pop() {
        r.results.iter_mut().try_for_each(flat_src)?;
        for n in &mut r.nodes {
            n.inputs.iter_mut().try_for_each(flat_src)?;
            if let Op::Match(ps) = &mut n.op {
                ps.iter_mut().try_for_each(flat_pattern)?;
            }
            todo.extend(n.regions.iter_mut().map(Arc::make_mut));
        }
    }
    Ok(())
}

/// A constant source with its strings held as one block ([`flat_strings`]).
fn flat_src(s: &mut Src) -> Result<(), TooLarge> {
    if let Src::Const(v) = s
        && let Some(flat) = flat_value(v)?
    {
        *v = flat;
    }
    Ok(())
}

/// A pattern whose literals hold their strings as one block, from a stack of the patterns left
/// to do: patterns nest as deep as the program (step T2-mid).
fn flat_pattern(p: &mut Pattern) -> Result<(), TooLarge> {
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Lit(v) => {
                if let Some(flat) = flat_value(v)? {
                    *v = flat;
                }
            }
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter_mut()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter_mut().map(|(_, q)| q)),
            Pattern::Wild | Pattern::Bind(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    Ok(())
}

/// Whether some string inside `v` is held in parts, not as one block.
fn has_joined(v: &Value) -> bool {
    let mut todo = vec![v];
    while let Some(v) = todo.pop() {
        match v {
            Value::Str(t) if !t.is_flat() => return true,
            Value::Tuple(xs) | Value::Path(xs) => todo.extend(xs.iter()),
            Value::Atom(a) => todo.extend(a.args().iter()),
            Value::Family(f) => todo.extend(f.iter().flat_map(|(k, x)| [k, x])),
            _ => {}
        }
    }
    false
}

/// `v` with each string inside it held as one block, or `None` when each already is, built
/// from the bottom up with a stack, as values nest as deep as the program (step T2-mid). A
/// tuple, path, atom or family is rebuilt from its parts in order, and equals `v`: only the
/// way its strings are held changes. [`TooLarge`] when the system refuses the memory for a
/// block ([`Text::try_shared`]).
fn flat_value(v: &Value) -> Result<Option<Value>, TooLarge> {
    if !has_joined(v) {
        return Ok(None);
    }
    // Each value to enter, or to close once its parts, entered after it, are on `done`.
    let mut todo: Vec<(&Value, bool)> = vec![(v, false)];
    let mut done: Vec<Value> = Vec::new();
    while let Some((v, close)) = todo.pop() {
        if !close {
            match v {
                Value::Str(t) if !t.is_flat() => done.push(Value::Str(Text::from(t.try_shared()?))),
                Value::Tuple(xs) | Value::Path(xs) => {
                    todo.push((v, true));
                    todo.extend(xs.iter().rev().map(|x| (x, false)));
                }
                Value::Atom(a) => {
                    todo.push((v, true));
                    todo.extend(a.args().iter().rev().map(|x| (x, false)));
                }
                Value::Family(f) => {
                    todo.push((v, true));
                    let entries: Vec<_> = f.iter().collect();
                    for (k, x) in entries.into_iter().rev() {
                        todo.push((x, false));
                        todo.push((k, false));
                    }
                }
                _ => done.push(v.clone()),
            }
            continue;
        }
        let parts = |n: usize, done: &mut Vec<Value>| done.split_off(done.len() - n);
        let rebuilt = match v {
            Value::Tuple(xs) => Value::tuple(parts(xs.len(), &mut done)),
            Value::Path(xs) => Value::path(parts(xs.len(), &mut done)),
            Value::Atom(a) => {
                let args = parts(a.args().len(), &mut done);
                Value::Atom(Atom {
                    name: a.name.clone(),
                    fields: a.fields.clone(),
                    payload: a.payload.as_ref().map(|_| args.into()),
                })
            }
            Value::Family(f) => {
                let flat = parts(2 * f.len(), &mut done);
                let mut it = flat.into_iter();
                let mut leaves = Vec::with_capacity(f.len());
                while let (Some(k), Some(x)) = (it.next(), it.next()) {
                    leaves.push((vec![k], x));
                }
                // The keys are `f`'s, distinct, each equal to the one it replaces, so in the
                // same order and none repeated; `from_leaves` fails only on an empty keypath or
                // on two keypaths that collide (`Levels::insert`), and each here is one key.
                Value::Family(Family::from_leaves(leaves).expect("the keys of a family"))
            }
            _ => unreachable!("only a tuple, path, atom or family is closed"),
        };
        done.push(rebuilt);
    }
    Ok(done.pop())
}

/// An edge's facts as the M0.7 rules see a definition: no name and no body.
fn def(v: &super::ValueEdge) -> Def {
    Def {
        name: "".into(),
        domain: Some(v.domain.clone()),
        facets: v.facets.clone(),
        body: Term::Lit(Value::tuple(Vec::new())),
    }
}

/// The pattern binders of `g` that still carry their written names.
fn written(g: &Region) -> u64 {
    let mut n = 0;
    let mut todo = vec![g];
    while let Some(r) = todo.pop() {
        for node in &r.nodes {
            if let Op::Match(ps) = &node.op {
                for p in ps {
                    let mut index = 0;
                    p.binders(|name| {
                        n += u64::from(!canonical_at(name, index));
                        index += 1;
                    });
                }
            }
            todo.extend(node.regions.iter().map(|r| &**r));
        }
    }
    n
}

/// The binder rule: the first written pattern binder in preorder renamed to its level, its
/// written name a hint on the argument it binds. Only the regions on the way down to its node
/// are made unique.
fn rename_first(g: &mut Region) -> bool {
    let Some((steps, k)) = first_written(g) else {
        return false;
    };
    let mut r = g;
    for (k, j) in steps {
        r = Arc::make_mut(&mut r.nodes[k].regions[j]);
    }
    let node = &mut r.nodes[k];
    let Op::Match(ps) = &mut node.op else {
        unreachable!("first_written finds a match node")
    };
    for (arm, p) in ps.iter_mut().enumerate() {
        let mut index = 0;
        if let Some(name) = rename_in(p, &mut index) {
            if let Edge::Value(v) = &mut Arc::make_mut(&mut node.regions[arm]).args[index] {
                v.facets.push(Facet {
                    hint: true,
                    kind: "binder".into(),
                    value: Value::tuple(vec![Value::Int(index as i64), Value::Str(name.into())]),
                });
            }
            return true;
        }
    }
    unreachable!("first_written finds a written binder")
}

/// The place of the first node of `g`, in preorder, whose patterns hold a written binder: the
/// node and region indices down to its region, and its index there.
fn first_written(g: &Region) -> Option<(Vec<(usize, usize)>, usize)> {
    let has_written = |p: &Pattern| {
        let mut found = false;
        let mut index = 0;
        p.binders(|name| {
            found |= !canonical_at(name, index);
            index += 1;
        });
        found
    };
    /// A region being searched: node `k` is next, or is being searched, its patterns already
    /// read when `read` and its regions before `j` already searched.
    struct Frame<'a> {
        r: &'a Region,
        k: usize,
        j: usize,
        read: bool,
    }
    let mut frames = vec![Frame {
        r: g,
        k: 0,
        j: 0,
        read: false,
    }];
    while let Some(top) = frames.last_mut() {
        let Some(node) = top.r.nodes.get(top.k) else {
            frames.pop();
            if let Some(up) = frames.last_mut() {
                up.j += 1;
            }
            continue;
        };
        if !top.read {
            top.read = true;
            if let Op::Match(ps) = &node.op
                && ps.iter().any(has_written)
            {
                let k = top.k;
                let steps = frames[..frames.len() - 1].iter().map(|f| (f.k, f.j));
                return Some((steps.collect(), k));
            }
        }
        if let Some(sub) = node.regions.get(top.j) {
            frames.push(Frame {
                r: sub,
                k: 0,
                j: 0,
                read: false,
            });
        } else {
            top.k += 1;
            top.j = 0;
            top.read = false;
        }
    }
    None
}

/// Renames the first written binder of `p`, counting in `index` the binders before it, and
/// returns its written name.
// The binders after the first written one are still visited, each doing nothing; stopping at
// it would save at most the rest of one pattern, which the search for it (`first_written`)
// has already read.
fn rename_in(p: &mut Pattern, index: &mut usize) -> Option<std::sync::Arc<str>> {
    let mut written = None;
    p.rename_binders(|name| match written {
        Some(_) => {}
        None if canonical_at(name, *index) => *index += 1,
        None => {
            written = Some(name.clone());
            *name = level_name(*index);
        }
    });
    written
}

/// What is left of a walk over the edges in preorder: a region, whose arguments come first,
/// or a node, whose outputs come before its regions.
enum Part<R, N> {
    Region(R),
    Node(N),
}

/// Calls `f` on each edge of `g`, in preorder.
fn each_edge(g: &Region, f: &mut dyn FnMut(&Edge)) {
    let mut todo = vec![Part::Region(g)];
    while let Some(part) = todo.pop() {
        match part {
            Part::Region(r) => {
                r.args.iter().for_each(&mut *f);
                todo.extend(r.nodes.iter().rev().map(Part::Node));
            }
            Part::Node(n) => {
                n.outputs.iter().for_each(&mut *f);
                todo.extend(n.regions.iter().rev().map(|r| Part::Region(&**r)));
            }
        }
    }
}

/// Calls `f` on each edge of `g`, in preorder, mutably.
fn each_edge_mut(g: &mut Region, f: &mut dyn FnMut(&mut Edge)) {
    let mut todo = vec![Part::Region(g)];
    while let Some(part) = todo.pop() {
        match part {
            Part::Region(r) => {
                r.args.iter_mut().for_each(&mut *f);
                todo.extend(r.nodes.iter_mut().rev().map(Part::Node));
            }
            Part::Node(n) => {
                n.outputs.iter_mut().for_each(&mut *f);
                let subs = n.regions.iter_mut().rev();
                todo.extend(subs.map(|r| Part::Region(Arc::make_mut(r))));
            }
        }
    }
}
