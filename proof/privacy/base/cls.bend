# eukhe: lemmas shared by the proofs of area privacy, section ip: what the
# reader's symbol of a char says about the char (a decimal digit, a hex
# digit, exactly `:`, exactly `.`, or a char that does not go on with an
# address)

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ./chars.bend as LIp

# what a symbol y of the char c says about c
def pcl.C(c: Char, y: Ip.Sym) -> Type:
  Either<&1, &1, {y == Ip.Dig{c} : Ip.Sym} & {S.dec(c) == True{} : Bool}, Either<&1, &1, {y == Ip.Hx{c} : Ip.Sym} & {S.hex(c) == True{} : Bool}, Either<&1, &1, {y == Ip.Col{} : Ip.Sym} & {c == ':' : Char}, Either<&1, &1, {y == Ip.Dot{} : Ip.Sym} & {c == '.' : Char}, {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}>>>>

# the tail of Sym.of after each test
def pcl.r9(+x: U32) -> Ip.Sym:
  Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})

def pcl.r8(+x: U32) -> Ip.Sym:
  Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, pcl.r9(x))

def pcl.r7(+x: U32) -> Ip.Sym:
  Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, pcl.r8(x))

def pcl.r6(+x: U32) -> Ip.Sym:
  Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, pcl.r7(x))

def pcl.r5(+x: U32) -> Ip.Sym:
  Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, pcl.r6(x))

def pcl.r4(+x: U32) -> Ip.Sym:
  Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, pcl.r5(x))

def pcl.r3(+x: U32) -> Ip.Sym:
  Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, pcl.r4(x))

def pcl.r2(+x: U32) -> Ip.Sym:
  Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, pcl.r3(x))

def pcl.r1(+x: U32) -> Ip.Sym:
  Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, pcl.r2(x))

# a choice between two symbols that do not go on with an address
def pcl.sw(b: Bool, -y: Ip.Sym, -m: Ip.Sym, +hy: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}, +hm: {S.k_stop6(LIp.pip.kind(m)) == True{} : Bool}) -> {S.k_stop6(LIp.pip.kind(Ip.Sym.when(b, y, m))) == True{} : Bool}:
  match b:
    case True{}:
      hy
    case False{}:
      hm

def pcl.stop5(+x: U32) -> {S.k_stop6(LIp.pip.kind(pcl.r5(x))) == True{} : Bool}:
  pcl.sw(Cx.in(x, 103, 122), Ip.Let{}, pcl.r6(x), {==}, pcl.sw(Cx.in(x, 71, 90), Ip.Let{}, pcl.r7(x), {==}, pcl.sw(U32.is_eq(x, 95), Ip.Und{}, pcl.r8(x), {==}, pcl.sw(U32.is_eq(x, 170), Ip.Und{}, pcl.r9(x), {==}, pcl.sw(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}, {==}, {==})))))

def pcl.or_t2(a: Bool, -b: Bool) -> {Bool.or(a, Bool.or(True{}, b)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pcl.or_t3(a: Bool, b: Bool) -> {Bool.or(a, Bool.or(b, True{})) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def pcl.l4(b: Bool, +x: U32, +e: {U32.is_eq(x, 46) == b : Bool}) -> pcl.C(Chr{x}, Ip.Sym.when(b, Ip.Dot{}, pcl.r5(x))):
  match b:
    case True{}:
      Inr{Inr{Inr{Inl{({==}, Equal.cong(U32, Char, u => Chr{u}, x, 46, PWireBoolExact.wr_eq_sound(x, 46, e)))}}}}
    case False{}:
      Inr{Inr{Inr{Inr{pcl.stop5(x)}}}}

def pcl.l3(b: Bool, +x: U32, +e: {U32.is_eq(x, 58) == b : Bool}) -> pcl.C(Chr{x}, Ip.Sym.when(b, Ip.Col{}, pcl.r4(x))):
  match b:
    case True{}:
      Inr{Inr{Inl{({==}, Equal.cong(U32, Char, u => Chr{u}, x, 58, PWireBoolExact.wr_eq_sound(x, 58, e)))}}}
    case False{}:
      pcl.l4(U32.is_eq(x, 46), x, {==})

def pcl.hex_a(+x: U32, +e: {Cx.in(x, 97, 102) == True{} : Bool}) -> {S.hex(Chr{x}) == True{} : Bool}:
  %Equal.sym(Bool, Cx.in(x, 97, 102), True{}, e) : {Bool.or(S.in(x, 48, 57), Bool.or(_, S.in(x, 65, 70))) == True{} : Bool}
  pcl.or_t2(S.in(x, 48, 57), S.in(x, 65, 70))

def pcl.hex_b(+x: U32, +e: {Cx.in(x, 65, 70) == True{} : Bool}) -> {S.hex(Chr{x}) == True{} : Bool}:
  %Equal.sym(Bool, Cx.in(x, 65, 70), True{}, e) : {Bool.or(S.in(x, 48, 57), Bool.or(S.in(x, 97, 102), _)) == True{} : Bool}
  pcl.or_t3(S.in(x, 48, 57), S.in(x, 97, 102))

def pcl.l2(b: Bool, +x: U32, +e: {Cx.in(x, 65, 70) == b : Bool}) -> pcl.C(Chr{x}, Ip.Sym.when(b, Ip.Hx{Chr{x}}, pcl.r3(x))):
  match b:
    case True{}:
      Inr{Inl{({==}, pcl.hex_b(x, e))}}
    case False{}:
      pcl.l3(U32.is_eq(x, 58), x, {==})

def pcl.l1(b: Bool, +x: U32, +e: {Cx.in(x, 97, 102) == b : Bool}) -> pcl.C(Chr{x}, Ip.Sym.when(b, Ip.Hx{Chr{x}}, pcl.r2(x))):
  match b:
    case True{}:
      Inr{Inl{({==}, pcl.hex_a(x, e))}}
    case False{}:
      pcl.l2(Cx.in(x, 65, 70), x, {==})

def pcl.l0(b: Bool, +x: U32, +e: {Cx.in(x, 48, 57) == b : Bool}) -> pcl.C(Chr{x}, Ip.Sym.when(b, Ip.Dig{Chr{x}}, pcl.r1(x))):
  match b:
    case True{}:
      Inl{({==}, e)}
    case False{}:
      pcl.l1(Cx.in(x, 97, 102), x, {==})

# every char's symbol says what the char is
def pcl.of(c: Char) -> pcl.C(c, Ip.Sym.of(c)):
  match c:
    case Chr{+x}:
      pcl.l0(Cx.in(x, 48, 57), x, {==})
