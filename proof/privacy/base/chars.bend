# eukhe: lemmas shared by the proofs of area privacy, section ip: the
# kind of a char (the reader's symbol and the spec's kind agree, char by
# char), the char before a position, and the logic the IP proofs use

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S

# Logic
# -----

def pip.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise False == True proves anything
def pip.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : pip.IfF(_, G)
  Unit{}

def pip.and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pip.absurd_ft({False{} == True{} : Bool}, h)

def pip.and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pip.absurd_ft({b == True{} : Bool}, h)

def pip.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pip.and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pip.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Kinds
# -----

# the spec's kind of a symbol
def pip.kind(y: Ip.Sym) -> S.CKind:
  match y:
    case Ip.Dig{c}:
      S.KDec{}
    case Ip.Hx{c}:
      S.KHex{}
    case Ip.Col{}:
      S.KCol{}
    case Ip.Dot{}:
      S.KDot{}
    case Ip.Let{}:
      S.KLet{}
    case Ip.Und{}:
      S.KUnd{}
    case Ip.Dash{}:
      S.KDash{}
    case Ip.Oth{}:
      S.KOth{}

def pip.kind_when(b: Bool, -y: Ip.Sym, -m: Ip.Sym) -> {pip.kind(Ip.Sym.when(b, y, m)) == S.when(b, pip.kind(y), pip.kind(m)) : S.CKind}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pip.kind_of.l10(+x: U32) -> {pip.kind(Ip.Oth{}) == S.KOth{} : S.CKind}:
  {==}

def pip.kind_of.l9(+x: U32) -> {pip.kind(Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})) == S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})), S.when(U32.is_eq(x, 45), pip.kind(Ip.Dash{}), pip.kind(Ip.Oth{})), S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}), pip.kind_when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}), Equal.cong(S.CKind, S.CKind, z => S.when(U32.is_eq(x, 45), S.KDash{}, z), pip.kind(Ip.Oth{}), S.KOth{}, pip.kind_of.l10(x)))

def pip.kind_of.l8(+x: U32) -> {pip.kind(Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))) == S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))), S.when(U32.is_eq(x, 170), pip.kind(Ip.Und{}), pip.kind(Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))), S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})), pip.kind_when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})), Equal.cong(S.CKind, S.CKind, z => S.when(U32.is_eq(x, 170), S.KUnd{}, z), pip.kind(Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})), S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}), pip.kind_of.l9(x)))

def pip.kind_of.l7(+x: U32) -> {pip.kind(Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))) == S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))), S.when(U32.is_eq(x, 95), pip.kind(Ip.Und{}), pip.kind(Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))), S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))), pip.kind_when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))), Equal.cong(S.CKind, S.CKind, z => S.when(U32.is_eq(x, 95), S.KUnd{}, z), pip.kind(Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))), S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})), pip.kind_of.l8(x)))

def pip.kind_of.l6(+x: U32) -> {pip.kind(Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))) == S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))), S.when(Cx.in(x, 71, 90), pip.kind(Ip.Let{}), pip.kind(Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))), S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))), pip.kind_when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))), Equal.cong(S.CKind, S.CKind, z => S.when(Cx.in(x, 71, 90), S.KLet{}, z), pip.kind(Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))), S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))), pip.kind_of.l7(x)))

def pip.kind_of.l5(+x: U32) -> {pip.kind(Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))) == S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))), S.when(Cx.in(x, 103, 122), pip.kind(Ip.Let{}), pip.kind(Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))), S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))), pip.kind_when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))), Equal.cong(S.CKind, S.CKind, z => S.when(Cx.in(x, 103, 122), S.KLet{}, z), pip.kind(Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))), S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))), pip.kind_of.l6(x)))

def pip.kind_of.l4(+x: U32) -> {pip.kind(Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))) == S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))), S.when(U32.is_eq(x, 46), pip.kind(Ip.Dot{}), pip.kind(Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))), S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))), pip.kind_when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))), Equal.cong(S.CKind, S.CKind, z => S.when(U32.is_eq(x, 46), S.KDot{}, z), pip.kind(Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))), S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))), pip.kind_of.l5(x)))

def pip.kind_of.l3(+x: U32) -> {pip.kind(Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))) == S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))), S.when(U32.is_eq(x, 58), pip.kind(Ip.Col{}), pip.kind(Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))), S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))), pip.kind_when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))), Equal.cong(S.CKind, S.CKind, z => S.when(U32.is_eq(x, 58), S.KCol{}, z), pip.kind(Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))), S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))), pip.kind_of.l4(x)))

def pip.kind_of.l2(+x: U32) -> {pip.kind(Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))) == S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))), S.when(Cx.in(x, 65, 70), pip.kind(Ip.Hx{Chr{x}}), pip.kind(Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))), S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))))), pip.kind_when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))), Equal.cong(S.CKind, S.CKind, z => S.when(Cx.in(x, 65, 70), S.KHex{}, z), pip.kind(Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))), S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))), pip.kind_of.l3(x)))

def pip.kind_of.l1(+x: U32) -> {pip.kind(Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))) == S.when(S.in(x, 97, 102), S.KHex{}, S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))), S.when(Cx.in(x, 97, 102), pip.kind(Ip.Hx{Chr{x}}), pip.kind(Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))), S.when(S.in(x, 97, 102), S.KHex{}, S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))))), pip.kind_when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))), Equal.cong(S.CKind, S.CKind, z => S.when(Cx.in(x, 97, 102), S.KHex{}, z), pip.kind(Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))), S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))))), pip.kind_of.l2(x)))

def pip.kind_of.l0(+x: U32) -> {pip.kind(Ip.Sym.when(Cx.in(x, 48, 57), Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))))) == S.when(S.in(x, 48, 57), S.KDec{}, S.when(S.in(x, 97, 102), S.KHex{}, S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))))))) : S.CKind}:
  Equal.trans(S.CKind, pip.kind(Ip.Sym.when(Cx.in(x, 48, 57), Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))))), S.when(Cx.in(x, 48, 57), pip.kind(Ip.Dig{Chr{x}}), pip.kind(Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))))), S.when(S.in(x, 48, 57), S.KDec{}, S.when(S.in(x, 97, 102), S.KHex{}, S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{})))))))))), pip.kind_when(Cx.in(x, 48, 57), Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))), Equal.cong(S.CKind, S.CKind, z => S.when(Cx.in(x, 48, 57), S.KDec{}, z), pip.kind(Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))), S.when(S.in(x, 97, 102), S.KHex{}, S.when(S.in(x, 65, 70), S.KHex{}, S.when(U32.is_eq(x, 58), S.KCol{}, S.when(U32.is_eq(x, 46), S.KDot{}, S.when(S.in(x, 103, 122), S.KLet{}, S.when(S.in(x, 71, 90), S.KLet{}, S.when(U32.is_eq(x, 95), S.KUnd{}, S.when(U32.is_eq(x, 170), S.KUnd{}, S.when(U32.is_eq(x, 45), S.KDash{}, S.KOth{}))))))))), pip.kind_of.l1(x)))

# the reader's symbol of a char has the spec's kind of the char
def pip.kind_of(c: Char) -> {pip.kind(Ip.Sym.of(c)) == S.kind(c) : S.CKind}:
  match c:
    case Chr{+x}:
      pip.kind_of.l0(x)

def pip.free(y: Ip.Sym) -> {Ip.Sym.free(y) == S.k_free(pip.kind(y)) : Bool}:
  match y:
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def pip.word(y: Ip.Sym) -> {Ip.Sym.word(y) == S.k_word(pip.kind(y)) : Bool}:
  match y:
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def pip.alnum(y: Ip.Sym) -> {Ip.Sym.alnum(y) == S.k_alnum(pip.kind(y)) : Bool}:
  match y:
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def pip.edge4(y: Ip.Sym) -> {Ip.Sym.edge4(y) == S.k_edge4(pip.kind(y)) : Bool}:
  match y:
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

# a char's symbol is free exactly when the spec says
def pip.free_of(+c: Char) -> {Ip.Sym.free(Ip.Sym.of(c)) == S.k_free(S.kind(c)) : Bool}:
  %pip.kind_of(c) : {Ip.Sym.free(Ip.Sym.of(c)) == S.k_free(_) : Bool}
  pip.free(Ip.Sym.of(c))

def pip.word_of(+c: Char) -> {Ip.Sym.word(Ip.Sym.of(c)) == S.k_word(S.kind(c)) : Bool}:
  %pip.kind_of(c) : {Ip.Sym.word(Ip.Sym.of(c)) == S.k_word(_) : Bool}
  pip.word(Ip.Sym.of(c))

def pip.alnum_of(+c: Char) -> {Ip.Sym.alnum(Ip.Sym.of(c)) == S.k_alnum(S.kind(c)) : Bool}:
  %pip.kind_of(c) : {Ip.Sym.alnum(Ip.Sym.of(c)) == S.k_alnum(_) : Bool}
  pip.alnum(Ip.Sym.of(c))

def pip.edge4_of(+c: Char) -> {Ip.Sym.edge4(Ip.Sym.of(c)) == S.k_edge4(S.kind(c)) : Bool}:
  %pip.kind_of(c) : {Ip.Sym.edge4(Ip.Sym.of(c)) == S.k_edge4(_) : Bool}
  pip.edge4(Ip.Sym.of(c))

# The chars before a position
# ---------------------------

# the last char of q's text, then s
def pip.lastm(s: String, q: Maybe<&2, Char>) -> Maybe<&2, Char>:
  match s:
    case SNil{}:
      q
    case SCon{d, t}:
      pip.lastm(t, Some{d})

# a text that ends with c: the last char is c
def pip.last2_snoc(s: String, -p: Maybe<&2, Char>, -q: Maybe<&2, Char>, -c: Char) -> {Ip.last2(String.append(s, SCon{c, SNil{}}), p, q) == (pip.lastm(s, q), Some{c}) : Maybe<&2, Char> & Maybe<&2, Char>}:
  match s:
    case SNil{}:
      {==}
    case SCon{d, t}:
      pip.last2_snoc(t, q, Some{d}, c)

def pip.word_not_free(k: S.CKind, h: {S.k_word(k) == True{} : Bool}) -> {S.k_free(k) == False{} : Bool}:
  match k:
    case S.KDec{}:
      {==}
    case S.KHex{}:
      {==}
    case S.KLet{}:
      {==}
    case S.KUnd{}:
      {==}
    case S.KCol{}:
      {==}
    case S.KDot{}:
      {==}
    case S.KDash{}:
      pip.absurd_ft({S.k_free(S.KDash{}) == False{} : Bool}, h)
    case S.KOth{}:
      pip.absurd_ft({S.k_free(S.KOth{}) == False{} : Bool}, h)

def pip.word_not_edge4(k: S.CKind, h: {S.k_word(k) == True{} : Bool}) -> {S.k_edge4(k) == False{} : Bool}:
  match k:
    case S.KDec{}:
      {==}
    case S.KHex{}:
      {==}
    case S.KLet{}:
      {==}
    case S.KUnd{}:
      {==}
    case S.KCol{}:
      pip.absurd_ft({S.k_edge4(S.KCol{}) == False{} : Bool}, h)
    case S.KDot{}:
      {==}
    case S.KDash{}:
      pip.absurd_ft({S.k_edge4(S.KDash{}) == False{} : Bool}, h)
    case S.KOth{}:
      pip.absurd_ft({S.k_edge4(S.KOth{}) == False{} : Bool}, h)

# The line before a position
# --------------------------

# reversing a text that ends with s starts with s reversed
def pip.rev_app(p: String, -s: String, -acc: String) -> {String.reverse.go(String.append(p, s), acc) == String.reverse.go(s, String.reverse.go(p, acc)) : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{h, t}:
      pip.rev_app(t, s, SCon{h, acc})

# a version's context at the end of the text before: no IPv4
def pip.v4_ctx(+b: String, -s: String, +h: {Cx.vctx(b) == True{} : Bool}) -> {Ip.v4(b, s) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Cx.vctx(b), True{}, h) : {Ip.v4.go(Bool.and(Ip.edge4(Ip.last2(b, None{}, None{})), Bool.not(_)), s) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.and(Ip.edge4(Ip.last2(b, None{}, None{})), False{}), False{}, pip.and_false(Ip.edge4(Ip.last2(b, None{}, None{})))) : {Ip.v4.go(_, s) == None{} : Maybe<&2, Nat>}
  {==}
