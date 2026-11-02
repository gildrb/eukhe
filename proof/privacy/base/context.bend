# eukhe: lemmas of area privacy, section ip: the grammar's version
# context (bend/privacy/context.bend) is the spec's (S7,
# spec/harness/privacy_context.bend): each symbol of the reader stands for
# the spec's kind of its char, and each step over the line, read from its
# end, is the spec's step over those kinds

import Base
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy_context.bend as V

# Kinds
# -----

# the spec's kind of a symbol
def pcx.vk(y: Cx.VSym) -> V.VKind:
  match y:
    case Cx.Bl{}:
      V.VBlank{}
    case Cx.Eq{}:
      V.VSign{'='}
    case Cx.Gt{}:
      V.VSign{'>'}
    case Cx.Lt{}:
      V.VSign{'<'}
    case Cx.Ti{}:
      V.VSign{'~'}
    case Cx.Ba{}:
      V.VSign{'!'}
    case Cx.Ca{}:
      V.VSign{'^'}
    case Cx.Pu{}:
      V.VMark{}
    case Cx.Wc{c}:
      V.VWord{c}
    case Cx.Nl{}:
      V.VBreak{}
    case Cx.Ot{}:
      V.VOther{}

def pcx.vk_when(b: Bool, -y: Cx.VSym, -m: Cx.VSym) -> {pcx.vk(Cx.VSym.when(b, y, m)) == V.vwhen(b, pcx.vk(y), pcx.vk(m)) : V.VKind}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the tests of Cx.VSym.of and of V.vkind, from the k-th on
def pcx.cr18(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 95), Cx.Wc{Chr{x}}, Cx.Ot{})

def pcx.sr18(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 95), V.VWord{Chr{x}}, V.VOther{})

def pcx.cr17(+x: U32) -> Cx.VSym:
  Cx.VSym.when(Cx.in(x, 65, 90), Cx.Wc{Chr{(x + 32 : U32)}}, pcx.cr18(x))

def pcx.sr17(+x: U32) -> V.VKind:
  V.vwhen(V.vin(x, 65, 90), V.VWord{Chr{(x + 32 : U32)}}, pcx.sr18(x))

def pcx.cr16(+x: U32) -> Cx.VSym:
  Cx.VSym.when(Cx.in(x, 97, 122), Cx.Wc{Chr{x}}, pcx.cr17(x))

def pcx.sr16(+x: U32) -> V.VKind:
  V.vwhen(V.vin(x, 97, 122), V.VWord{Chr{x}}, pcx.sr17(x))

def pcx.cr15(+x: U32) -> Cx.VSym:
  Cx.VSym.when(Cx.in(x, 48, 57), Cx.Wc{Chr{x}}, pcx.cr16(x))

def pcx.sr15(+x: U32) -> V.VKind:
  V.vwhen(V.vin(x, 48, 57), V.VWord{Chr{x}}, pcx.sr16(x))

def pcx.cr14(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 10), Cx.Nl{}, pcx.cr15(x))

def pcx.sr14(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 10), V.VBreak{}, pcx.sr15(x))

def pcx.cr13(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 44), Cx.Pu{}, pcx.cr14(x))

def pcx.sr13(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 44), V.VMark{}, pcx.sr14(x))

def pcx.cr12(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 91), Cx.Pu{}, pcx.cr13(x))

def pcx.sr12(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 91), V.VMark{}, pcx.sr13(x))

def pcx.cr11(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 40), Cx.Pu{}, pcx.cr12(x))

def pcx.sr11(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 40), V.VMark{}, pcx.sr12(x))

def pcx.cr10(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 58), Cx.Pu{}, pcx.cr11(x))

def pcx.sr10(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 58), V.VMark{}, pcx.sr11(x))

def pcx.cr9(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 39), Cx.Pu{}, pcx.cr10(x))

def pcx.sr9(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 39), V.VMark{}, pcx.sr10(x))

def pcx.cr8(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 34), Cx.Pu{}, pcx.cr9(x))

def pcx.sr8(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 34), V.VMark{}, pcx.sr9(x))

def pcx.cr7(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 94), Cx.Ca{}, pcx.cr8(x))

def pcx.sr7(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 94), V.VSign{'^'}, pcx.sr8(x))

def pcx.cr6(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 33), Cx.Ba{}, pcx.cr7(x))

def pcx.sr6(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 33), V.VSign{'!'}, pcx.sr7(x))

def pcx.cr5(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 126), Cx.Ti{}, pcx.cr6(x))

def pcx.sr5(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 126), V.VSign{'~'}, pcx.sr6(x))

def pcx.cr4(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 60), Cx.Lt{}, pcx.cr5(x))

def pcx.sr4(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 60), V.VSign{'<'}, pcx.sr5(x))

def pcx.cr3(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 62), Cx.Gt{}, pcx.cr4(x))

def pcx.sr3(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 62), V.VSign{'>'}, pcx.sr4(x))

def pcx.cr2(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 61), Cx.Eq{}, pcx.cr3(x))

def pcx.sr2(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 61), V.VSign{'='}, pcx.sr3(x))

def pcx.cr1(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 9), Cx.Bl{}, pcx.cr2(x))

def pcx.sr1(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 9), V.VBlank{}, pcx.sr2(x))

def pcx.cr0(+x: U32) -> Cx.VSym:
  Cx.VSym.when(U32.is_eq(x, 32), Cx.Bl{}, pcx.cr1(x))

def pcx.sr0(+x: U32) -> V.VKind:
  V.vwhen(U32.is_eq(x, 32), V.VBlank{}, pcx.sr1(x))

def pcx.kd18(+x: U32) -> {pcx.vk(pcx.cr18(x)) == pcx.sr18(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr18(x)), V.vwhen(U32.is_eq(x, 95), pcx.vk(Cx.Wc{Chr{x}}), pcx.vk(Cx.Ot{})), pcx.sr18(x), pcx.vk_when(U32.is_eq(x, 95), Cx.Wc{Chr{x}}, Cx.Ot{}), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 95), V.VWord{Chr{x}}, z), pcx.vk(Cx.Ot{}), V.VOther{}, {==}))

def pcx.kd17(+x: U32) -> {pcx.vk(pcx.cr17(x)) == pcx.sr17(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr17(x)), V.vwhen(Cx.in(x, 65, 90), pcx.vk(Cx.Wc{Chr{(x + 32 : U32)}}), pcx.vk(pcx.cr18(x))), pcx.sr17(x), pcx.vk_when(Cx.in(x, 65, 90), Cx.Wc{Chr{(x + 32 : U32)}}, pcx.cr18(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(Cx.in(x, 65, 90), V.VWord{Chr{(x + 32 : U32)}}, z), pcx.vk(pcx.cr18(x)), pcx.sr18(x), pcx.kd18(x)))

def pcx.kd16(+x: U32) -> {pcx.vk(pcx.cr16(x)) == pcx.sr16(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr16(x)), V.vwhen(Cx.in(x, 97, 122), pcx.vk(Cx.Wc{Chr{x}}), pcx.vk(pcx.cr17(x))), pcx.sr16(x), pcx.vk_when(Cx.in(x, 97, 122), Cx.Wc{Chr{x}}, pcx.cr17(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(Cx.in(x, 97, 122), V.VWord{Chr{x}}, z), pcx.vk(pcx.cr17(x)), pcx.sr17(x), pcx.kd17(x)))

def pcx.kd15(+x: U32) -> {pcx.vk(pcx.cr15(x)) == pcx.sr15(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr15(x)), V.vwhen(Cx.in(x, 48, 57), pcx.vk(Cx.Wc{Chr{x}}), pcx.vk(pcx.cr16(x))), pcx.sr15(x), pcx.vk_when(Cx.in(x, 48, 57), Cx.Wc{Chr{x}}, pcx.cr16(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(Cx.in(x, 48, 57), V.VWord{Chr{x}}, z), pcx.vk(pcx.cr16(x)), pcx.sr16(x), pcx.kd16(x)))

def pcx.kd14(+x: U32) -> {pcx.vk(pcx.cr14(x)) == pcx.sr14(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr14(x)), V.vwhen(U32.is_eq(x, 10), pcx.vk(Cx.Nl{}), pcx.vk(pcx.cr15(x))), pcx.sr14(x), pcx.vk_when(U32.is_eq(x, 10), Cx.Nl{}, pcx.cr15(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 10), V.VBreak{}, z), pcx.vk(pcx.cr15(x)), pcx.sr15(x), pcx.kd15(x)))

def pcx.kd13(+x: U32) -> {pcx.vk(pcx.cr13(x)) == pcx.sr13(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr13(x)), V.vwhen(U32.is_eq(x, 44), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr14(x))), pcx.sr13(x), pcx.vk_when(U32.is_eq(x, 44), Cx.Pu{}, pcx.cr14(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 44), V.VMark{}, z), pcx.vk(pcx.cr14(x)), pcx.sr14(x), pcx.kd14(x)))

def pcx.kd12(+x: U32) -> {pcx.vk(pcx.cr12(x)) == pcx.sr12(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr12(x)), V.vwhen(U32.is_eq(x, 91), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr13(x))), pcx.sr12(x), pcx.vk_when(U32.is_eq(x, 91), Cx.Pu{}, pcx.cr13(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 91), V.VMark{}, z), pcx.vk(pcx.cr13(x)), pcx.sr13(x), pcx.kd13(x)))

def pcx.kd11(+x: U32) -> {pcx.vk(pcx.cr11(x)) == pcx.sr11(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr11(x)), V.vwhen(U32.is_eq(x, 40), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr12(x))), pcx.sr11(x), pcx.vk_when(U32.is_eq(x, 40), Cx.Pu{}, pcx.cr12(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 40), V.VMark{}, z), pcx.vk(pcx.cr12(x)), pcx.sr12(x), pcx.kd12(x)))

def pcx.kd10(+x: U32) -> {pcx.vk(pcx.cr10(x)) == pcx.sr10(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr10(x)), V.vwhen(U32.is_eq(x, 58), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr11(x))), pcx.sr10(x), pcx.vk_when(U32.is_eq(x, 58), Cx.Pu{}, pcx.cr11(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 58), V.VMark{}, z), pcx.vk(pcx.cr11(x)), pcx.sr11(x), pcx.kd11(x)))

def pcx.kd9(+x: U32) -> {pcx.vk(pcx.cr9(x)) == pcx.sr9(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr9(x)), V.vwhen(U32.is_eq(x, 39), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr10(x))), pcx.sr9(x), pcx.vk_when(U32.is_eq(x, 39), Cx.Pu{}, pcx.cr10(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 39), V.VMark{}, z), pcx.vk(pcx.cr10(x)), pcx.sr10(x), pcx.kd10(x)))

def pcx.kd8(+x: U32) -> {pcx.vk(pcx.cr8(x)) == pcx.sr8(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr8(x)), V.vwhen(U32.is_eq(x, 34), pcx.vk(Cx.Pu{}), pcx.vk(pcx.cr9(x))), pcx.sr8(x), pcx.vk_when(U32.is_eq(x, 34), Cx.Pu{}, pcx.cr9(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 34), V.VMark{}, z), pcx.vk(pcx.cr9(x)), pcx.sr9(x), pcx.kd9(x)))

def pcx.kd7(+x: U32) -> {pcx.vk(pcx.cr7(x)) == pcx.sr7(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr7(x)), V.vwhen(U32.is_eq(x, 94), pcx.vk(Cx.Ca{}), pcx.vk(pcx.cr8(x))), pcx.sr7(x), pcx.vk_when(U32.is_eq(x, 94), Cx.Ca{}, pcx.cr8(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 94), V.VSign{'^'}, z), pcx.vk(pcx.cr8(x)), pcx.sr8(x), pcx.kd8(x)))

def pcx.kd6(+x: U32) -> {pcx.vk(pcx.cr6(x)) == pcx.sr6(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr6(x)), V.vwhen(U32.is_eq(x, 33), pcx.vk(Cx.Ba{}), pcx.vk(pcx.cr7(x))), pcx.sr6(x), pcx.vk_when(U32.is_eq(x, 33), Cx.Ba{}, pcx.cr7(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 33), V.VSign{'!'}, z), pcx.vk(pcx.cr7(x)), pcx.sr7(x), pcx.kd7(x)))

def pcx.kd5(+x: U32) -> {pcx.vk(pcx.cr5(x)) == pcx.sr5(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr5(x)), V.vwhen(U32.is_eq(x, 126), pcx.vk(Cx.Ti{}), pcx.vk(pcx.cr6(x))), pcx.sr5(x), pcx.vk_when(U32.is_eq(x, 126), Cx.Ti{}, pcx.cr6(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 126), V.VSign{'~'}, z), pcx.vk(pcx.cr6(x)), pcx.sr6(x), pcx.kd6(x)))

def pcx.kd4(+x: U32) -> {pcx.vk(pcx.cr4(x)) == pcx.sr4(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr4(x)), V.vwhen(U32.is_eq(x, 60), pcx.vk(Cx.Lt{}), pcx.vk(pcx.cr5(x))), pcx.sr4(x), pcx.vk_when(U32.is_eq(x, 60), Cx.Lt{}, pcx.cr5(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 60), V.VSign{'<'}, z), pcx.vk(pcx.cr5(x)), pcx.sr5(x), pcx.kd5(x)))

def pcx.kd3(+x: U32) -> {pcx.vk(pcx.cr3(x)) == pcx.sr3(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr3(x)), V.vwhen(U32.is_eq(x, 62), pcx.vk(Cx.Gt{}), pcx.vk(pcx.cr4(x))), pcx.sr3(x), pcx.vk_when(U32.is_eq(x, 62), Cx.Gt{}, pcx.cr4(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 62), V.VSign{'>'}, z), pcx.vk(pcx.cr4(x)), pcx.sr4(x), pcx.kd4(x)))

def pcx.kd2(+x: U32) -> {pcx.vk(pcx.cr2(x)) == pcx.sr2(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr2(x)), V.vwhen(U32.is_eq(x, 61), pcx.vk(Cx.Eq{}), pcx.vk(pcx.cr3(x))), pcx.sr2(x), pcx.vk_when(U32.is_eq(x, 61), Cx.Eq{}, pcx.cr3(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 61), V.VSign{'='}, z), pcx.vk(pcx.cr3(x)), pcx.sr3(x), pcx.kd3(x)))

def pcx.kd1(+x: U32) -> {pcx.vk(pcx.cr1(x)) == pcx.sr1(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr1(x)), V.vwhen(U32.is_eq(x, 9), pcx.vk(Cx.Bl{}), pcx.vk(pcx.cr2(x))), pcx.sr1(x), pcx.vk_when(U32.is_eq(x, 9), Cx.Bl{}, pcx.cr2(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 9), V.VBlank{}, z), pcx.vk(pcx.cr2(x)), pcx.sr2(x), pcx.kd2(x)))

def pcx.kd0(+x: U32) -> {pcx.vk(pcx.cr0(x)) == pcx.sr0(x) : V.VKind}:
  Equal.trans(V.VKind, pcx.vk(pcx.cr0(x)), V.vwhen(U32.is_eq(x, 32), pcx.vk(Cx.Bl{}), pcx.vk(pcx.cr1(x))), pcx.sr0(x), pcx.vk_when(U32.is_eq(x, 32), Cx.Bl{}, pcx.cr1(x)), Equal.cong(V.VKind, V.VKind, z => V.vwhen(U32.is_eq(x, 32), V.VBlank{}, z), pcx.vk(pcx.cr1(x)), pcx.sr1(x), pcx.kd1(x)))

# the reader's symbol of a char has the spec's kind of the char
def pcx.kind_of(c: Char) -> {pcx.vk(Cx.VSym.of(c)) == V.vkind(c) : V.VKind}:
  match c:
    case Chr{+x}:
      pcx.kd0(x)

# the spec's kinds of symbols
def pcx.vks(vs: List<&2, Cx.VSym>) -> List<&2, V.VKind>:
  match vs:
    case Nil{}:
      Nil{}
    case y <> t:
      pcx.vk(y) <> pcx.vks(t)

def pcx.cons(-k: V.VKind, -a: List<&2, V.VKind>, -b: List<&2, V.VKind>, e: {a == b : List<&2, V.VKind>}) -> {k <> a == k <> b : List<&2, V.VKind>}:
  Equal.cong(List<&2, V.VKind>, List<&2, V.VKind>, z => k <> z, a, b, e)

# The line
# --------

# the symbols of a text are the kinds of its chars
def pcx.list(r: String) -> {pcx.vks(Cx.VSym.list(r)) == V.vkinds(r) : List<&2, V.VKind>}:
  match r:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(V.VKind, pcx.vk(Cx.VSym.of(c)), V.vkind(c), pcx.kind_of(c)) : {_ <> pcx.vks(Cx.VSym.list(t)) == V.vkind(c) <> V.vkinds(t) : List<&2, V.VKind>}
      pcx.cons(V.vkind(c), pcx.vks(Cx.VSym.list(t)), V.vkinds(t), pcx.list(t))

# the line is cut at the spec's newline
def pcx.line(vs: List<&2, Cx.VSym>) -> {pcx.vks(Cx.line(vs)) == V.vcut(pcx.vks(vs)) : List<&2, V.VKind>}:
  match vs:
    case Nil{}:
      {==}
    case y <> +t:
      match y:
        case Cx.Bl{}:
          pcx.cons(V.VBlank{}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Eq{}:
          pcx.cons(V.VSign{'='}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Gt{}:
          pcx.cons(V.VSign{'>'}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Lt{}:
          pcx.cons(V.VSign{'<'}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Ti{}:
          pcx.cons(V.VSign{'~'}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Ba{}:
          pcx.cons(V.VSign{'!'}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Ca{}:
          pcx.cons(V.VSign{'^'}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Pu{}:
          pcx.cons(V.VMark{}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Wc{c}:
          pcx.cons(V.VWord{c}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))
        case Cx.Nl{}:
          {==}
        case Cx.Ot{}:
          pcx.cons(V.VOther{}, pcx.vks(Cx.line(t)), V.vcut(pcx.vks(t)), pcx.line(t))

# trailing blanks dropped as the spec drops them
def pcx.blanks(vs: List<&2, Cx.VSym>) -> {pcx.vks(Cx.blanks(vs)) == V.vtrim(pcx.vks(vs)) : List<&2, V.VKind>}:
  match vs:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Cx.Bl{}:
          pcx.blanks(t)
        case Cx.Eq{}:
          {==}
        case Cx.Gt{}:
          {==}
        case Cx.Lt{}:
          {==}
        case Cx.Ti{}:
          {==}
        case Cx.Ba{}:
          {==}
        case Cx.Ca{}:
          {==}
        case Cx.Pu{}:
          {==}
        case Cx.Wc{c}:
          {==}
        case Cx.Nl{}:
          {==}
        case Cx.Ot{}:
          {==}

# punctuation dropped as the spec drops it
def pcx.punct(vs: List<&2, Cx.VSym>) -> {pcx.vks(Cx.punct(vs)) == V.vstrip(pcx.vks(vs)) : List<&2, V.VKind>}:
  match vs:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Cx.Bl{}:
          pcx.punct(t)
        case Cx.Eq{}:
          pcx.punct(t)
        case Cx.Gt{}:
          pcx.punct(t)
        case Cx.Lt{}:
          pcx.punct(t)
        case Cx.Ti{}:
          {==}
        case Cx.Ba{}:
          {==}
        case Cx.Ca{}:
          {==}
        case Cx.Pu{}:
          pcx.punct(t)
        case Cx.Wc{c}:
          {==}
        case Cx.Nl{}:
          {==}
        case Cx.Ot{}:
          {==}

# blanks dropped first change nothing the spec strips
def pcx.strip_trim(ks: List<&2, V.VKind>) -> {V.vstrip(V.vtrim(ks)) == V.vstrip(ks) : List<&2, V.VKind>}:
  match ks:
    case Nil{}:
      {==}
    case k <> t:
      match k:
        case V.VBlank{}:
          pcx.strip_trim(t)
        case V.VSign{c}:
          {==}
        case V.VMark{}:
          {==}
        case V.VWord{c}:
          {==}
        case V.VBreak{}:
          {==}
        case V.VOther{}:
          {==}

# Operators and words
# -------------------

# the line ends with a requirement operator exactly when the spec says
def pcx.op(vs: List<&2, Cx.VSym>) -> {Cx.op(vs) == V.vop(pcx.vks(vs)) : Bool}:
  match vs:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Cx.Bl{}:
          {==}
        case Cx.Eq{}:
          match t:
            case Nil{}:
              {==}
            case z <> t2:
              match z:
                case Cx.Bl{}:
                  {==}
                case Cx.Eq{}:
                  {==}
                case Cx.Gt{}:
                  {==}
                case Cx.Lt{}:
                  {==}
                case Cx.Ti{}:
                  {==}
                case Cx.Ba{}:
                  {==}
                case Cx.Ca{}:
                  {==}
                case Cx.Pu{}:
                  {==}
                case Cx.Wc{c}:
                  {==}
                case Cx.Nl{}:
                  {==}
                case Cx.Ot{}:
                  {==}
        case Cx.Gt{}:
          {==}
        case Cx.Lt{}:
          {==}
        case Cx.Ti{}:
          {==}
        case Cx.Ba{}:
          {==}
        case Cx.Ca{}:
          {==}
        case Cx.Pu{}:
          {==}
        case Cx.Wc{c}:
          {==}
        case Cx.Nl{}:
          {==}
        case Cx.Ot{}:
          {==}

# the last word is the spec's
def pcx.word(vs: List<&2, Cx.VSym>) -> {Cx.word(vs) == V.vword(pcx.vks(vs)) : String}:
  match vs:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Cx.Bl{}:
          {==}
        case Cx.Eq{}:
          {==}
        case Cx.Gt{}:
          {==}
        case Cx.Lt{}:
          {==}
        case Cx.Ti{}:
          {==}
        case Cx.Ba{}:
          {==}
        case Cx.Ca{}:
          {==}
        case Cx.Pu{}:
          {==}
        case Cx.Wc{+c}:
          Equal.cong(String, String, z => SCon{c, z}, Cx.word(t), V.vword(pcx.vks(t)), pcx.word(t))
        case Cx.Nl{}:
          {==}
        case Cx.Ot{}:
          {==}

def pcx.starts(k: String, w: String) -> {Cx.starts(k, w) == V.vpre(k, w) : Bool}:
  match k:
    case SNil{}:
      {==}
    case SCon{+a, kt}:
      match w:
        case SNil{}:
          {==}
        case SCon{+b, wt}:
          Equal.cong(Bool, Bool, z => Bool.and(Char.is_eq(a, b), z), Cx.starts(kt, wt), V.vpre(kt, wt), pcx.starts(kt, wt))

def pcx.holds(w: String, +k: String) -> {Cx.holds(w, k) == V.vhas(w, k) : Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Cx.starts(k, SCon{c, t}), V.vpre(k, SCon{c, t}), pcx.starts(k, SCon{c, t})) : {Bool.or(_, Cx.holds(t, k)) == Bool.or(V.vpre(k, SCon{c, t}), V.vhas(t, k)) : Bool}
      Equal.cong(Bool, Bool, z => Bool.or(V.vpre(k, SCon{c, t}), z), Cx.holds(t, k), V.vhas(t, k), pcx.holds(t, k))

# a version word exactly when the spec says
def pcx.name(+w: String) -> {Cx.vword(w) == V.vname(w) : Bool}:
  %Equal.sym(Bool, Cx.holds(w, "noisrev"), V.vhas(w, "noisrev"), pcx.holds(w, "noisrev")) : {Bool.or(_, Bool.or(String.eq(w, "rev"), Bool.or(String.eq(w, "v"), Bool.or(String.eq(w, "esaeler"), String.eq(w, "gat"))))) == V.vname(w) : Bool}
  {==}

# The context
# -----------

# the context of a line read from its end is the spec's
def pcx.go(+vs: List<&2, Cx.VSym>) -> {Cx.vctx.go(Cx.blanks(vs)) == V.vctx.of(pcx.vks(vs)) : Bool}:
  %Equal.sym(Bool, Cx.op(Cx.blanks(vs)), V.vop(pcx.vks(Cx.blanks(vs))), pcx.op(Cx.blanks(vs))) : {Bool.or(_, Cx.vword(Cx.word(Cx.punct(Cx.blanks(vs))))) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(List<&2, V.VKind>, pcx.vks(Cx.blanks(vs)), V.vtrim(pcx.vks(vs)), pcx.blanks(vs)) : {Bool.or(V.vop(_), Cx.vword(Cx.word(Cx.punct(Cx.blanks(vs))))) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(Bool, Cx.vword(Cx.word(Cx.punct(Cx.blanks(vs)))), V.vname(Cx.word(Cx.punct(Cx.blanks(vs)))), pcx.name(Cx.word(Cx.punct(Cx.blanks(vs))))) : {Bool.or(V.vop(V.vtrim(pcx.vks(vs))), _) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(String, Cx.word(Cx.punct(Cx.blanks(vs))), V.vword(pcx.vks(Cx.punct(Cx.blanks(vs)))), pcx.word(Cx.punct(Cx.blanks(vs)))) : {Bool.or(V.vop(V.vtrim(pcx.vks(vs))), V.vname(_)) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(List<&2, V.VKind>, pcx.vks(Cx.punct(Cx.blanks(vs))), V.vstrip(pcx.vks(Cx.blanks(vs))), pcx.punct(Cx.blanks(vs))) : {Bool.or(V.vop(V.vtrim(pcx.vks(vs))), V.vname(V.vword(_))) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(List<&2, V.VKind>, pcx.vks(Cx.blanks(vs)), V.vtrim(pcx.vks(vs)), pcx.blanks(vs)) : {Bool.or(V.vop(V.vtrim(pcx.vks(vs))), V.vname(V.vword(V.vstrip(_)))) == V.vctx.of(pcx.vks(vs)) : Bool}
  %Equal.sym(List<&2, V.VKind>, V.vstrip(V.vtrim(pcx.vks(vs))), V.vstrip(pcx.vks(vs)), pcx.strip_trim(pcx.vks(vs))) : {Bool.or(V.vop(V.vtrim(pcx.vks(vs))), V.vname(V.vword(_))) == V.vctx.of(pcx.vks(vs)) : Bool}
  {==}

# the line of a text before a position, as the spec reads it
def pcx.cut(+r: String) -> {pcx.vks(Cx.line(Cx.VSym.list(r))) == V.vcut(V.vkinds(r)) : List<&2, V.VKind>}:
  Equal.trans(List<&2, V.VKind>, pcx.vks(Cx.line(Cx.VSym.list(r))), V.vcut(pcx.vks(Cx.VSym.list(r))), V.vcut(V.vkinds(r)), pcx.line(Cx.VSym.list(r)), Equal.cong(List<&2, V.VKind>, List<&2, V.VKind>, z => V.vcut(z), pcx.vks(Cx.VSym.list(r)), V.vkinds(r), pcx.list(r)))

# S7: the grammar's version context of every text is the spec's
def pcx.vctx(+before: String) -> {Cx.vctx(before) == V.vctx(before) : Bool}:
  %pcx.cut(String.reverse(before)) : {Cx.vctx.go(Cx.blanks(Cx.line(Cx.VSym.list(String.reverse(before))))) == V.vctx.of(_) : Bool}
  pcx.go(Cx.line(Cx.VSym.list(String.reverse(before))))
