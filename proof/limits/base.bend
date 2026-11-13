# eukhe: lemmas shared by the proofs of area limits

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../spec/budget/limits.bend as S
import ../../spec/budget/ledger.bend as SL

def lmb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def lmb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def lmb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : lmb.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def lmb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : lmb.IfT(_, G)
  Unit{}

# a + 0 is a
def lmb.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, lmb.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

# a + (1 + b) is 1 + (a + b)
def lmb.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), lmb.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# the code's projection of a dimension is the spec's
def lmb.get(d: B.Dim, h: L.Lims) -> {L.get(d, h) == S.dim(d, h) : L.Val}:
  match d:
    case B.Cost{}:
      match h:
        case L.Lims{c, k, m, n, r}:
          {==}
    case B.Tok{}:
      match h:
        case L.Lims{c, k, m, n, r}:
          {==}
    case B.Time{}:
      match h:
        case L.Lims{c, k, m, n, r}:
          {==}
    case B.Calls{}:
      match h:
        case L.Lims{c, k, m, n, r}:
          {==}
    case B.Reqs{}:
      match h:
        case L.Lims{c, k, m, n, r}:
          {==}

# a pick found at place j of the presets after the first i is at place
# i + j of them all
def lmb.join(i: Nat, m: Maybe<&2, L.Pick>, acc: Maybe<&2, L.Pick>) -> Maybe<&2, L.Pick>:
  match m:
    case None{}:
      acc
    case Some{L.Pick{v, L.Preset{j}}}:
      Some{L.Pick{v, L.Preset{Nat.add(i, j)}}}
    case Some{L.Pick{v, L.UntilFinished{}}}:
      Some{L.Pick{v, L.UntilFinished{}}}
    case Some{L.Pick{v, L.Set{}}}:
      Some{L.Pick{v, L.Set{}}}
    case Some{L.Pick{v, L.LimitsProfile{}}}:
      Some{L.Pick{v, L.LimitsProfile{}}}
    case Some{L.Pick{v, L.Profile{}}}:
      Some{L.Pick{v, L.Profile{}}}

def lmb.last_step(m: Maybe<&2, L.Pick>, v: L.Val, +i: Nat, -acc: Maybe<&2, L.Pick>) -> {lmb.join(1n+i, m, L.last.take(v, i, acc)) == lmb.join(i, S.last.at(m, S.given(v), v), acc) : Maybe<&2, L.Pick>}:
  match m:
    case None{}:
      match v:
        case L.Unset{}:
          {==}
        case L.At{n}:
          %lmb.add_zero(i) : {Some{L.Pick{L.At{n}, L.Preset{_}}} == Some{L.Pick{L.At{n}, L.Preset{Nat.add(i, 0n)}}} : Maybe<&2, L.Pick>}
          {==}
        case L.Unlimited{}:
          %lmb.add_zero(i) : {Some{L.Pick{L.Unlimited{}, L.Preset{_}}} == Some{L.Pick{L.Unlimited{}, L.Preset{Nat.add(i, 0n)}}} : Maybe<&2, L.Pick>}
          {==}
    case Some{L.Pick{w, L.Preset{j}}}:
      %lmb.add_succ(i, j) : {Some{L.Pick{w, L.Preset{_}}} == Some{L.Pick{w, L.Preset{Nat.add(i, 1n+j)}}} : Maybe<&2, L.Pick>}
      {==}
    case Some{L.Pick{w, L.UntilFinished{}}}:
      {==}
    case Some{L.Pick{w, L.Set{}}}:
      {==}
    case Some{L.Pick{w, L.LimitsProfile{}}}:
      {==}
    case Some{L.Pick{w, L.Profile{}}}:
      {==}

# the code's last preset from place i after acc is the spec's, joined
def lmb.last(+d: B.Dim, ps: List<&2, L.Lims>, +i: Nat, +acc: Maybe<&2, L.Pick>) -> {L.last(d, ps, i, acc) == lmb.join(i, S.last(d, ps), acc) : Maybe<&2, L.Pick>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Maybe<&2, L.Pick>, L.last(d, t, 1n+i, L.last.take(L.get(d, h), i, acc)), lmb.join(1n+i, S.last(d, t), L.last.take(L.get(d, h), i, acc)), lmb.last(d, t, 1n+i, L.last.take(L.get(d, h), i, acc))) : {_ == lmb.join(i, S.last.at(S.last(d, t), S.given(S.dim(d, h)), S.dim(d, h)), acc) : Maybe<&2, L.Pick>}
      %Equal.sym(L.Val, L.get(d, h), S.dim(d, h), lmb.get(d, h)) : {lmb.join(1n+i, S.last(d, t), L.last.take(_, i, acc)) == lmb.join(i, S.last.at(S.last(d, t), S.given(S.dim(d, h)), S.dim(d, h)), acc) : Maybe<&2, L.Pick>}
      lmb.last_step(S.last(d, t), S.dim(d, h), i, acc)

def lmb.join0(m: Maybe<&2, L.Pick>) -> {lmb.join(0n, m, None{}) == m : Maybe<&2, L.Pick>}:
  match m:
    case None{}:
      {==}
    case Some{L.Pick{v, L.Preset{j}}}:
      {==}
    case Some{L.Pick{v, L.UntilFinished{}}}:
      {==}
    case Some{L.Pick{v, L.Set{}}}:
      {==}
    case Some{L.Pick{v, L.LimitsProfile{}}}:
      {==}
    case Some{L.Pick{v, L.Profile{}}}:
      {==}

# the code's last preset is the spec's
def lmb.last0(+d: B.Dim, +ps: List<&2, L.Lims>) -> {L.last(d, ps, 0n, None{}) == S.last(d, ps) : Maybe<&2, L.Pick>}:
  Equal.trans(Maybe<&2, L.Pick>, L.last(d, ps, 0n, None{}), lmb.join(0n, S.last(d, ps), None{}), S.last(d, ps), lmb.last(d, ps, 0n, None{}), lmb.join0(S.last(d, ps)))

# a pick read back field by field is the pick
def lmb.eta(p: L.Pick) -> {L.Pick{L.Pick.v(p), L.Pick.src(p)} == p : L.Pick}:
  match p:
    case L.Pick{v, x}:
      {==}

# the dimension of a set limit the principal left unset goes by the
# presets
def lmb.by_set(v: L.Val, -d: B.Dim, -t: L.Toggle, -ps: List<&2, L.Lims>, -own: L.Lims, -table: L.Lims, -G: L.Pick -> Type, g: {S.given(v) == False{} : Bool}, k: G(L.by_preset(L.last(d, ps, 0n, None{}), t, L.get(d, own), L.get(d, table)))) -> G(L.by_set(v, d, t, ps, own, table)):
  match v:
    case L.Unset{}:
      k
    case L.At{n}:
      lmb.absurd_tf(G(L.by_set(L.At{n}, d, t, ps, own, table)), g)
    case L.Unlimited{}:
      lmb.absurd_tf(G(L.by_set(L.Unlimited{}, d, t, ps, own, table)), g)

# a dimension no preset gives goes by the toggle and the profiles
def lmb.none_case(-G: L.Pick -> Type, +d: B.Dim, +ps: List<&2, L.Lims>, -t: L.Toggle, -o: L.Val, -tb: L.Val, e: {S.last(d, ps) == None{} : Maybe<&2, L.Pick>}, k: G(L.unset(t, o, tb))) -> G(L.by_preset(L.last(d, ps, 0n, None{}), t, o, tb)):
  %Equal.sym(Maybe<&2, L.Pick>, L.last(d, ps, 0n, None{}), S.last(d, ps), lmb.last0(d, ps)) : G(L.by_preset(_, t, o, tb))
  %Equal.sym(Maybe<&2, L.Pick>, S.last(d, ps), None{}, e) : G(L.by_preset(_, t, o, tb))
  k

# the code's dimension of the profiles is the spec's
def lmb.unset_get(-G: L.Pick -> Type, +d: B.Dim, -t: L.Toggle, +own: L.Lims, +table: L.Lims, k: G(L.unset(t, S.dim(d, own), S.dim(d, table)))) -> G(L.unset(t, L.get(d, own), L.get(d, table))):
  %Equal.sym(L.Val, L.get(d, own), S.dim(d, own), lmb.get(d, own)) : G(L.unset(t, _, L.get(d, table)))
  %Equal.sym(L.Val, L.get(d, table), S.dim(d, table), lmb.get(d, table)) : G(L.unset(t, S.dim(d, own), _))
  k

# Renewal
# -------

def lmb.at_add(d: B.Dim, x: B.Amt, y: B.Amt) -> {SL.at(d, B.add4(x, y)) == Nat.add(SL.at(d, x), SL.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Tok{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Time{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Calls{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Reqs{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}

def lmb.at_sub(d: B.Dim, x: B.Amt, y: B.Amt) -> {SL.at(d, B.sub4(x, y)) == Nat.sub(SL.at(d, x), SL.at(d, y)) : Nat}:
  match d:
    case B.Cost{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Tok{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Time{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Calls{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}
    case B.Reqs{}:
      match x y:
        case B.Amt{a1, a2, a3, a4} B.Amt{b1, b2, b3, b4}:
          {==}

def lmb.at_zero(d: B.Dim) -> {SL.at(d, B.zero()) == 0n : Nat}:
  match d:
    case B.Cost{}:
      {==}
    case B.Tok{}:
      {==}
    case B.Time{}:
      {==}
    case B.Calls{}:
      {==}
    case B.Reqs{}:
      {==}

# what the code's holds hold is the spec's
def lmb.at_holding(+d: B.Dim, hs: List<&2, B.Hold>) -> {SL.at(d, L.holding(hs)) == SL.held(d, hs) : Nat}:
  match hs:
    case Nil{}:
      lmb.at_zero(d)
    case Con{B.Hold{i, +x}, +t}:
      %Equal.sym(Nat, SL.at(d, B.add4(x, L.holding(t))), Nat.add(SL.at(d, x), SL.at(d, L.holding(t))), lmb.at_add(d, x, L.holding(t))) : {_ == Nat.add(SL.at(d, x), SL.held(d, t)) : Nat}
      %Equal.sym(Nat, SL.at(d, L.holding(t)), SL.held(d, t), lmb.at_holding(d, t)) : {Nat.add(SL.at(d, x), _) == Nat.add(SL.at(d, x), SL.held(d, t)) : Nat}
      {==}

# what the code counts a run used is the spec's
def lmb.used(+d: B.Dim, +sp: B.Amt, +mark: B.Amt, +hs: List<&2, B.Hold>, +le: B.Amt) -> {SL.at(d, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le))) == Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))) : Nat}:
  %Equal.sym(Nat, SL.at(d, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le))), Nat.add(SL.at(d, B.sub4(sp, mark)), SL.at(d, B.add4(L.holding(hs), le))), lmb.at_add(d, B.sub4(sp, mark), B.add4(L.holding(hs), le))) : {_ == Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))) : Nat}
  %Equal.sym(Nat, SL.at(d, B.sub4(sp, mark)), Nat.sub(SL.at(d, sp), SL.at(d, mark)), lmb.at_sub(d, sp, mark)) : {Nat.add(_, SL.at(d, B.add4(L.holding(hs), le))) == Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))) : Nat}
  %Equal.sym(Nat, SL.at(d, B.add4(L.holding(hs), le)), Nat.add(SL.at(d, L.holding(hs)), SL.at(d, le)), lmb.at_add(d, L.holding(hs), le)) : {Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), _) == Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))) : Nat}
  %Equal.sym(Nat, SL.at(d, L.holding(hs)), SL.held(d, hs), lmb.at_holding(d, hs)) : {Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(_, SL.at(d, le))) == Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))) : Nat}
  {==}

# a renewed free in a spent dimension is that dimension's renewal
def lmb.free(d: B.Dim, l: L.Lims, f: B.Amt, u: B.Amt, sd: {S.spent_dim(d) == True{} : Bool}) -> {SL.at(d, L.renew.free(l, f, u)) == L.renew.dim(S.dim(d, l), SL.at(d, f), SL.at(d, u)) : Nat}:
  match d:
    case B.Cost{}:
      match l f u:
        case L.Lims{c, k, m, n, r} B.Amt{f1, f2, f3, f4} B.Amt{u1, u2, u3, u4}:
          {==}
    case B.Tok{}:
      match l f u:
        case L.Lims{c, k, m, n, r} B.Amt{f1, f2, f3, f4} B.Amt{u1, u2, u3, u4}:
          {==}
    case B.Calls{}:
      match l f u:
        case L.Lims{c, k, m, n, r} B.Amt{f1, f2, f3, f4} B.Amt{u1, u2, u3, u4}:
          {==}
    case B.Reqs{}:
      match l f u:
        case L.Lims{c, k, m, n, r} B.Amt{f1, f2, f3, f4} B.Amt{u1, u2, u3, u4}:
          {==}
    case B.Time{}:
      lmb.absurd_ft({SL.at(B.Time{}, L.renew.free(l, f, u)) == L.renew.dim(S.dim(B.Time{}, l), SL.at(B.Time{}, f), SL.at(B.Time{}, u)) : Nat}, sd)

# (n - x) + x is the larger of n and x
def lmb.sub_add_max(+n: Nat, +x: Nat) -> {Nat.add(Nat.sub(n, x), x) == Nat.max(n, x) : Nat}:
  match n x:
    case 0n x:
      {==}
    case 1n+(+p) 0n:
      lmb.add_zero(1n+p)
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), lmb.add_succ(Nat.sub(p, q), q)) : {_ == 1n+Nat.max(p, q) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), q), Nat.max(p, q), lmb.sub_add_max(p, q)) : {1n+_ == 1n+Nat.max(p, q) : Nat}
      {==}
