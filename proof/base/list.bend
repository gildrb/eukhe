# eukhe: lemmas the proofs of two or more areas share: list

import Base
import ../../bend/command.bend as Cmd
import ../../bend/tree.bend as Tr
import ../../laws/command.bend as Command
import ../../laws/base.bend as LawsBase
import ./bool.bend as LBool
import ./logic/bool.bend as LLogicBool
import ./logic/list.bend as LLogicList
import ./logic/logic.bend as LLogicLogic

def wn_lenL(g: Nat, +q: Nat) -> {List.length(&2, Nat, LLogicList.wn_L(g, q)) == LawsBase.wire_digits.go(g, q) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      match q:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, LLogicList.wn_L(f, Nat.div(1n+p, 10n))),
            LawsBase.wire_digits.go(f, Nat.div(1n+p, 10n)), wn_lenL(f, Nat.div(1n+p, 10n)))

# wire_digits(n) counts the digits of n
def wn_wl(+n: Nat) -> {LawsBase.wire_digits(n) == List.length(&2, Nat, LLogicList.wn_full(n)) : Nat}:
  Equal.cong(Nat, Nat, k => 1n+k, LawsBase.wire_digits.go(n, Nat.div(n, 10n)), List.length(&2, Nat, LLogicList.wn_L(n, Nat.div(n, 10n))),
    Equal.sym(Nat, List.length(&2, Nat, LLogicList.wn_L(n, Nat.div(n, 10n))), LawsBase.wire_digits.go(n, Nat.div(n, 10n)), wn_lenL(n, Nat.div(n, 10n))))

def cb_app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %cb_app_assoc(A, t, ys, zs) : {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _ : List<&2, A>}
      {==}

# from q, the names of x <> more walked one by one are declared: so is
# q and all of them
def cb_walks_decl(more: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +h: {Command.cmd_walks.go(x <> more, t, q) == True{} : Bool}) -> {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, x <> more)) == True{} : Bool}:
  match more:
    case Nil{}:
      LLogicBool.cb_and_l(Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])), True{}, h)
    case Con{+y, +m2}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      %cb_app_assoc(List<&2, Nat>, q, [x], y <> m2) : {Command.cmd_declared(t, _) == True{} : Bool}
      cb_walks_decl(m2, y, t, qx, LLogicBool.cb_and_r(Command.cmd_declared(t, qx), Command.cmd_walks.go(y <> m2, t, qx), h))

# a path of the table is declared
def cb_path_decl(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, h: {Command.cmd_path(t, q) == True{} : Bool}) -> {Command.cmd_declared(t, q) == True{} : Bool}:
  match q:
    case Nil{}:
      LLogicLogic.cb_absurd({Command.cmd_declared(t, Nil{}) == True{} : Bool}, h)
    case Con{+x, +rest}:
      cb_walks_decl(rest, x, t, Nil{}, h)

# Lists

def tc.app_nil(xs: List<&2, Tr.Ent>) -> {List.append(&2, Tr.Ent, xs, Nil{}) == xs : List<&2, Tr.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Tr.Ent>, List<&2, Tr.Ent>, ys => h <> ys, List.append(&2, Tr.Ent, t, Nil{}), t, tc.app_nil(t))

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

def rp.notin_append(+last: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {LLogicBool.rp.notin(last, xs) == True{} : Bool}, hy: {LLogicBool.rp.notin(last, ys) == True{} : Bool}) -> {LLogicBool.rp.notin(last, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +rest:
      ne = LLogicBool.rp.and_l(Bool.not(Nat.is_eq(x, last)), LLogicBool.rp.notin(last, rest), hx)
      nr = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(x, last)), LLogicBool.rp.notin(last, rest), hx)
      LBool.rp.and_tt(Bool.not(Nat.is_eq(x, last)), LLogicBool.rp.notin(last, List.append(&2, Nat, rest, ys)), ne, rp.notin_append(last, rest, ys, nr, hy))
