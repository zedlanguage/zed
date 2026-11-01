/// A small x86-64 assembler (step L1.36): the few instructions the code generator emits,
/// with labels for jumps, calls and addresses inside the code, and a record of each 64-bit
/// address of a runtime hook, which the JIT fills in and the object file leaves to the
/// linker.
library;

import 'dart:typed_data';

/// A general register, by its number in the encoding.
enum Reg {
  rax,
  rcx,
  rdx,
  rbx,
  rsp,
  rbp,
  rsi,
  rdi,
  r8,
  r9,
  r10,
  r11;

  int get low => index & 7;

  /// The REX bit this register adds in the field it is encoded in.
  int get high => index >> 3;
}

/// The condition of a conditional jump or `set`, by its number in the encoding.
enum Cond {
  o(0x0),
  b(0x2),
  ae(0x3),
  e(0x4),
  ne(0x5),
  a(0x7),
  p(0x0a),
  np(0x0b),
  l(0x0c),
  ge(0x0d),
  le(0x0e),
  g(0x0f);

  final int code;

  const Cond(this.code);
}

/// A place in the code, bound once; a jump to it before it is bound is patched when it is.
final class Label {
  int? at;
  final _uses = <int>[];
}

/// A 64-bit hook address in the code: its offset and the hook's number.
typedef HookUse = ({int offset, int hook});

/// The code being written.
final class Asm {
  final _code = BytesBuilder(copy: false);
  final _patches = <(int, int)>[];

  /// Each hook address the code holds, in the order written.
  final hooks = <HookUse>[];

  /// The offset of the next byte.
  int get here => _code.length;

  /// The code; every label used must be bound.
  Uint8List finish() {
    final out = _code.toBytes();
    final view = ByteData.sublistView(out);
    for (final (at, value) in _patches) {
      view.setInt32(at, value, Endian.little);
    }
    return out;
  }

  void _b(int x) => _code.addByte(x & 0xff);

  void _d32(int x) {
    final b = ByteData(4)..setInt32(0, x, Endian.little);
    _code.add(b.buffer.asUint8List());
  }

  void _d64(int x) {
    final b = ByteData(8)..setInt64(0, x, Endian.little);
    _code.add(b.buffer.asUint8List());
  }

  /// REX.W with the bits of [reg] (the ModRM reg field) and [rm] (the ModRM rm field).
  void _rex(Reg reg, Reg rm) => _b(0x48 | reg.high << 2 | rm.high);

  void _modrm(int mod, int reg, int rm) => _b(mod << 6 | (reg & 7) << 3 | rm & 7);

  /// An operand `[base + disp]`, disp 32 bits; [base] is neither `rsp` nor `r12`.
  void _mem(int reg, Reg base, int disp) {
    _modrm(2, reg, base.low);
    _d32(disp);
  }

  /// Binds [l] here and patches every jump to it.
  void bind(Label l) {
    l.at = here;
    for (final u in l._uses) {
      _patches.add((u, here - (u + 4)));
    }
    l._uses.clear();
  }

  /// A 32-bit displacement to [l] from the end of the instruction, which ends here.
  void _rel(Label l) {
    if (l.at case final at?) {
      _d32(at - (here + 4));
    } else {
      l._uses.add(here);
      _d32(0);
    }
  }

  /// `mov dst, [base + disp]`.
  void load(Reg dst, Reg base, int disp) {
    _rex(dst, base);
    _b(0x8b);
    _mem(dst.index, base, disp);
  }

  /// `mov [base + disp], src`.
  void store(Reg base, int disp, Reg src) {
    _rex(src, base);
    _b(0x89);
    _mem(src.index, base, disp);
  }

  /// `mov qword [base + disp], imm`, [imm] fitting in 32 bits signed.
  void storeImm(Reg base, int disp, int imm) {
    _rex(Reg.rax, base);
    _b(0xc7);
    _mem(0, base, disp);
    _d32(imm);
  }

  /// `mov dst, src`.
  void mov(Reg dst, Reg src) {
    _rex(src, dst);
    _b(0x89);
    _modrm(3, src.index, dst.index);
  }

  /// `mov dst, imm`, in the shortest form.
  void movImm(Reg dst, int imm) {
    if (fits32(imm)) {
      _rex(Reg.rax, dst);
      _b(0xc7);
      _modrm(3, 0, dst.index);
      _d32(imm);
    } else {
      _rex(Reg.rax, dst);
      _b(0xb8 + dst.low);
      _d64(imm);
    }
  }

  /// `lea dst, [base + disp]`.
  void lea(Reg dst, Reg base, int disp) {
    _rex(dst, base);
    _b(0x8d);
    _mem(dst.index, base, disp);
  }

  /// `lea dst, [rip + l]`: the address of [l].
  void leaLabel(Reg dst, Label l) {
    _rex(dst, Reg.rax);
    _b(0x8d);
    _modrm(0, dst.index, 5);
    _rel(l);
  }

  /// `cmp r, imm`, [imm] fitting in 32 bits signed.
  void cmpImm(Reg r, int imm) {
    _rex(Reg.rax, r);
    _b(0x81);
    _modrm(3, 7, r.index);
    _d32(imm);
  }

  /// `cmp a, b`.
  void cmp(Reg a, Reg b) => _op(0x39, a, b);

  /// `test a, a`.
  void test(Reg a) => _op(0x85, a, a);

  /// `add a, b`.
  void add(Reg a, Reg b) => _op(0x01, a, b);

  /// `sub a, b`.
  void sub(Reg a, Reg b) => _op(0x29, a, b);

  /// `and a, b`.
  void and(Reg a, Reg b) => _op(0x21, a, b);

  /// `or a, b`.
  void or(Reg a, Reg b) => _op(0x09, a, b);

  /// `xor a, b`.
  void xor(Reg a, Reg b) => _op(0x31, a, b);

  /// The instruction [op] `a, b`, `a` in the ModRM rm field.
  void _op(int op, Reg a, Reg b) {
    _rex(b, a);
    _b(op);
    _modrm(3, b.index, a.index);
  }

  /// `imul a, b`.
  void imul(Reg a, Reg b) {
    _rex(a, b);
    _b(0x0f);
    _b(0xaf);
    _modrm(3, a.index, b.index);
  }

  /// `neg a`.
  void neg(Reg a) {
    _rex(Reg.rax, a);
    _b(0xf7);
    _modrm(3, 3, a.index);
  }

  /// `xor a, imm`, [imm] fitting in 8 bits signed.
  void xorImm8(Reg a, int imm) {
    _rex(Reg.rax, a);
    _b(0x83);
    _modrm(3, 6, a.index);
    _b(imm);
  }

  /// `set<c> al; movzx eax, al`: `rax` is 1 when [c] holds, else 0.
  void setAl(Cond c) {
    _b(0x0f);
    _b(0x90 | c.code);
    _b(0xc0);
    _b(0x0f);
    _b(0xb6);
    _b(0xc0);
  }

  /// `movq xmm, r`.
  void toXmm(int xmm, Reg r) {
    _b(0x66);
    _rex(Reg.values[xmm], r);
    _b(0x0f);
    _b(0x6e);
    _modrm(3, xmm, r.index);
  }

  /// `movq r, xmm`.
  void fromXmm(Reg r, int xmm) {
    _b(0x66);
    _rex(Reg.values[xmm], r);
    _b(0x0f);
    _b(0x7e);
    _modrm(3, xmm, r.index);
  }

  /// The scalar double instruction [op] `xmm a, xmm b`: 0x58 add, 0x5c sub, 0x59 mul,
  /// 0x5e div.
  void sd(int op, int a, int b) {
    _b(0xf2);
    _b(0x0f);
    _b(op);
    _modrm(3, a, b);
  }

  /// `ucomisd xmm a, xmm b`.
  void ucomisd(int a, int b) {
    _b(0x66);
    _b(0x0f);
    _b(0x2e);
    _modrm(3, a, b);
  }

  /// `jmp l`.
  void jmp(Label l) {
    _b(0xe9);
    _rel(l);
  }

  /// `j<c> l`.
  void jcc(Cond c, Label l) {
    _b(0x0f);
    _b(0x80 | c.code);
    _rel(l);
  }

  /// `call l`.
  void call(Label l) {
    _b(0xe8);
    _rel(l);
  }

  /// `call r`.
  void callReg(Reg r) {
    if (r.high != 0) _b(0x41);
    _b(0xff);
    _modrm(3, 2, r.index);
  }

  /// `movabs r11, <hook>; call r11`: a call of hook number [hook], its address filled in
  /// later.
  void callHook(int hook) {
    _b(0x49);
    _b(0xbb);
    hooks.add((offset: here, hook: hook));
    _d64(0);
    callReg(Reg.r11);
  }

  /// `push rbp; mov rbp, rsp; sub rsp, <frame>`; returns where the frame size goes.
  int enter() {
    _b(0x55);
    mov(Reg.rbp, Reg.rsp);
    _rex(Reg.rax, Reg.rsp);
    _b(0x81);
    _modrm(3, 5, Reg.rsp.index);
    final at = here;
    _d32(0);
    return at;
  }

  /// Sets the frame size written at [at] by [enter].
  void frame(int at, int size) => _patches.add((at, size));

  /// `leave; ret`.
  void leave() {
    _b(0xc9);
    _b(0xc3);
  }
}

/// Whether [x] fits in 32 bits signed.
bool fits32(int x) => x >= -0x80000000 && x <= 0x7fffffff;
