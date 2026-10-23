# eukhe: lemmas the proofs of two or more areas share: list

import Base
import ../../bend/command.bend as Cmd
import ../../bend/semver.bend as Sv
import ../../bend/tree.bend as Tr
import ../../laws/command.bend as Command
import ../../laws/base.bend as LawsBase
import ./bool/and.bend as LBoolAnd
import ./bool/misc.bend as LBoolMisc
import ./nat/is_eq.bend as LNatIsEq
import ./nat/is_lt.bend as LNatIsLt

# the digits of q, lowest first, under the fuel g (put_nat.go's recursion)
def wn_L(g: Nat, q: Nat) -> List<&2, Nat>:
  match g:
    case 0n:
      Nil{}
    case 1n+f:
      match q:
        case 0n:
          Nil{}
        case 1n+p:
          +m = {1n+p : Nat}
          Nat.mod(m, 10n) <> wn_L(f, Nat.div(m, 10n))

# all the digits of n, lowest first
def wn_full(n: Nat) -> List<&2, Nat>:
  +m = n
  Nat.mod(m, 10n) <> wn_L(m, Nat.div(m, 10n))

def wn_Lzero(g: Nat) -> {wn_L(g, 0n) == Nil{} : List<&2, Nat>}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      {==}

def wn_lenL(g: Nat, +q: Nat) -> {List.length(&2, Nat, wn_L(g, q)) == LawsBase.wire_digits.go(g, q) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match q:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, wn_L(f, Nat.div(1n+p, 10n))),
            LawsBase.wire_digits.go(f, Nat.div(1n+p, 10n)), wn_lenL(f, Nat.div(1n+p, 10n)))

# wire_digits(n) counts the digits of n
def wn_wl(+n: Nat) -> {LawsBase.wire_digits(n) == List.length(&2, Nat, wn_full(n)) : Nat}:
  Equal.cong(Nat, Nat, k => 1n+k, LawsBase.wire_digits.go(n, Nat.div(n, 10n)), List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))),
    Equal.sym(Nat, List.length(&2, Nat, wn_L(n, Nat.div(n, 10n))), LawsBase.wire_digits.go(n, Nat.div(n, 10n)), wn_lenL(n, Nat.div(n, 10n))))

def cb_app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %cb_app_assoc(A, t, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

# cmd_eq true: the names are equal
def cb_eq(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: {Command.cmd_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      LBoolMisc.cb_absurd({Nil{} == y <> ys : List<&2, Nat>}, e)
    case Con{x, xs} Nil{}:
      LBoolMisc.cb_absurd({x <> xs == Nil{} : List<&2, Nat>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %LNatIsEq.cb_nat_eq(x, y, LBoolAnd.cb_and_l(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, Nat>}
      %cb_eq(xs, ys, LBoolAnd.cb_and_r(Nat.is_eq(x, y), Command.cmd_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, Nat>}
      {==}

# cmd_path_eq true: the paths are equal
def cb_path_eq(+a: List<&2, List<&2, Nat>>, +b: List<&2, List<&2, Nat>>, +e: {Command.cmd_path_eq(a, b) == True{} : Bool}) -> {a == b : List<&2, List<&2, Nat>>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      LBoolMisc.cb_absurd({Nil{} == y <> ys : List<&2, List<&2, Nat>>}, e)
    case Con{x, xs} Nil{}:
      LBoolMisc.cb_absurd({x <> xs == Nil{} : List<&2, List<&2, Nat>>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_eq(x, y, LBoolAnd.cb_and_l(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == _ <> ys : List<&2, List<&2, Nat>>}
      %cb_path_eq(xs, ys, LBoolAnd.cb_and_r(Command.cmd_eq(x, y), Command.cmd_path_eq(xs, ys), e)) : {x <> xs == x <> _ : List<&2, List<&2, Nat>>}
      {==}

def cb_names_app_l(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, +h: {Command.cmd_names_ok(List.append(&2, List<&2, Nat>, a, b)) == True{} : Bool}) -> {Command.cmd_names_ok(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      LBoolAnd.cb_and_intro(Command.cmd_name_ok(w), Command.cmd_names_ok(r), LBoolAnd.cb_and_l(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h), cb_names_app_l(r, b, LBoolAnd.cb_and_r(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h)))

# from q, the names of x <> more walked one by one are declared: so is
# q and all of them
def cb_walks_decl(more: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +h: {Command.cmd_walks.go(x <> more, t, q) == True{} : Bool}) -> {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, x <> more)) == True{} : Bool}:
  match more:
    case Nil{}:
      LBoolAnd.cb_and_l(Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])), True{}, h)
    case Con{+y, +m2}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      %cb_app_assoc(List<&2, Nat>, q, [x], y <> m2) : {Command.cmd_declared(t, _) == True{} : Bool}
      cb_walks_decl(m2, y, t, qx, LBoolAnd.cb_and_r(Command.cmd_declared(t, qx), Command.cmd_walks.go(y <> m2, t, qx), h))

# a path of the table is declared
def cb_path_decl(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, h: {Command.cmd_path(t, q) == True{} : Bool}) -> {Command.cmd_declared(t, q) == True{} : Bool}:
  match q:
    case Nil{}:
      LBoolMisc.cb_absurd({Command.cmd_declared(t, Nil{}) == True{} : Bool}, h)
    case Con{+x, +rest}:
      cb_walks_decl(rest, x, t, Nil{}, h)

# Lists

def tc.app_nil(xs: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, xs, Nil{}) == xs : List<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, t, Nil{}), t, tc.app_nil(t))

# Two nodes

# a and b in the order of the test lt
def tc.pair(lt: Bool, +a: Tr.Ent, +b: Tr.Ent) -> List<&2, Tr.Ent>:
  match lt:
    case True{}:
      [a, b]
    case False{}:
      [b, a]

def tc.pair_lt(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == True{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == True{} : Bool}) -> {LBoolMisc.tc.lt(tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      LNatIsLt.tc.lt_cons(a, [b], B, ha, LNatIsLt.tc.lt_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      LNatIsLt.tc.lt_cons(b, [a], B, hb, LNatIsLt.tc.lt_cons(a, Nil{}, B, ha, {==}))

def tc.pair_ge(c: Bool, +a: Tr.Ent, +b: Tr.Ent, +B: Nat, +ha: {Nat.is_lt(Tr.Ent.k(a), B) == False{} : Bool}, +hb: {Nat.is_lt(Tr.Ent.k(b), B) == False{} : Bool}) -> {LBoolMisc.tc.ge(tc.pair(c, a, b), B) == True{} : Bool}:
  match c:
    case True{}:
      LNatIsLt.tc.ge_cons(a, [b], B, ha, LNatIsLt.tc.ge_cons(b, Nil{}, B, hb, {==}))
    case False{}:
      LNatIsLt.tc.ge_cons(b, [a], B, hb, LNatIsLt.tc.ge_cons(a, Nil{}, B, ha, {==}))

# Lists
# -----

def pd.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %pd.app_nil(A, r) : {h <> List.append(&2, A, r, Nil{}) == h <> _ : List<&2, A>}
      {==}

def pd.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %pd.app_assoc(A, r, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, r, ys), zs) == h <> _ : List<&2, A>}
      {==}

def rk.I10(ds: List<&2, Sv.Dig>) -> List<&2, Sv.Dig>:
  Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(ds))))))))))

def rk.dcons(-d: Sv.Dig, -a: List<&2, Sv.Dig>, -b: List<&2, Sv.Dig>, e: {a == b : List<&2, Sv.Dig>}) -> {d <> a == d <> b : List<&2, Sv.Dig>}:
  %e : {d <> a == d <> _ : List<&2, Sv.Dig>}
  {==}

def rp.notin_append(+last: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {LBoolMisc.rp.notin(last, xs) == True{} : Bool}, hy: {LBoolMisc.rp.notin(last, ys) == True{} : Bool}) -> {LBoolMisc.rp.notin(last, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      ne = LBoolAnd.rp.and_l(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), hx)
      nr = LBoolAnd.rp.and_r(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, rest), hx)
      LBoolAnd.rp.and_tt(Bool.not(Nat.is_eq(x, last)), LBoolMisc.rp.notin(last, List.append(&2, Nat, rest, ys)), ne, rp.notin_append(last, rest, ys, nr, hy))
