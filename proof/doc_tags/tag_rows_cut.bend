# eukhe: the proof of LAW tag_rows_cut
#
# PROOF: by induction on ts with sel (as long as ts): a line of ts is kept
# or not before the rows after it, and the number of the first row of us
# counts the line (n + (1 + |r|) = (1 + n) + |r|). The one-line and empty
# cases compute.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

def trc.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      G

# 0 is no successor
def trc.zs(-G: Type, -k: Nat, e: {0n == 1n+k : Nat}) -> G:
  %e : trc.NZ(_, G)
  Unit{}

def trc.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def trc.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, trc.add_zero(p))

def trc.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), trc.add_succ(p, b))

# a row kept or not before a, then b
def trc.keep(s: Bool, -r: Dt.Row, -a: List<&2, Dt.Row>, -b: List<&2, Dt.Row>) -> {Dt.keep(s, r, List.append(&2, Dt.Row, a, b)) == List.append(&2, Dt.Row, Dt.keep(s, r, a), b) : List<&2, Dt.Row>}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

def trc.split(ts: List<&2, Nat>, +us: List<&2, Nat>, sel: List<&2, Bool>, +tel: List<&2, Bool>, +n: Nat, h: {List.length(&2, Bool, sel) == List.length(&2, Nat, ts) : Nat}) -> {Dt.rows(List.append(&2, Nat, ts, us), List.append(&2, Bool, sel, tel), n) == List.append(&2, Dt.Row, Dt.rows(ts, sel, n), Dt.rows(us, tel, Nat.add(n, List.length(&2, Nat, ts)))) : List<&2, Dt.Row>}:
  match ts sel:
    case Nil{} Nil{}:
      %Equal.sym(Nat, Nat.add(n, 0n), n, trc.add_zero(n)) : {Dt.rows(us, tel, n) == Dt.rows(us, tel, _) : List<&2, Dt.Row>}
      {==}
    case Nil{} s <> t:
      trc.zs({Dt.rows(us, List.append(&2, Bool, s <> t, tel), n) == Dt.rows(us, tel, Nat.add(n, 0n)) : List<&2, Dt.Row>}, List.length(&2, Bool, t), Equal.sym(Nat, 1n+List.length(&2, Bool, t), 0n, h))
    case +x <> +r Nil{}:
      trc.zs({Dt.rows(List.append(&2, Nat, x <> r, us), tel, n) == List.append(&2, Dt.Row, Nil{}, Dt.rows(us, tel, Nat.add(n, 1n+List.length(&2, Nat, r)))) : List<&2, Dt.Row>}, List.length(&2, Nat, r), h)
    case +x <> +r s <> +t:
      +ih = trc.split(r, us, t, tel, 1n+n, Equal.cong(Nat, Nat, trc.pred, 1n+List.length(&2, Bool, t), 1n+List.length(&2, Nat, r), h))
      %Equal.sym(List<&2, Dt.Row>, Dt.rows(List.append(&2, Nat, r, us), List.append(&2, Bool, t, tel), 1n+n), List.append(&2, Dt.Row, Dt.rows(r, t, 1n+n), Dt.rows(us, tel, 1n+Nat.add(n, List.length(&2, Nat, r)))), ih) : {Dt.keep(s, Dt.Row{n, x}, _) == List.append(&2, Dt.Row, Dt.keep(s, Dt.Row{n, x}, Dt.rows(r, t, 1n+n)), Dt.rows(us, tel, Nat.add(n, 1n+List.length(&2, Nat, r)))) : List<&2, Dt.Row>}
      %Equal.sym(Nat, Nat.add(n, 1n+List.length(&2, Nat, r)), 1n+Nat.add(n, List.length(&2, Nat, r)), trc.add_succ(n, List.length(&2, Nat, r))) : {Dt.keep(s, Dt.Row{n, x}, List.append(&2, Dt.Row, Dt.rows(r, t, 1n+n), Dt.rows(us, tel, 1n+Nat.add(n, List.length(&2, Nat, r))))) == List.append(&2, Dt.Row, Dt.keep(s, Dt.Row{n, x}, Dt.rows(r, t, 1n+n)), Dt.rows(us, tel, _)) : List<&2, Dt.Row>}
      trc.keep(s, Dt.Row{n, x}, Dt.rows(r, t, 1n+n), Dt.rows(us, tel, 1n+Nat.add(n, List.length(&2, Nat, r))))

# no selection cuts no row
def trc.nil(ts: List<&2, Nat>, -n: Nat) -> {Dt.rows(ts, Nil{}, n) == Nil{} : List<&2, Dt.Row>}:
  match ts:
    case Nil{}:
      {==}
    case x <> r:
      {==}

# the one-line and empty cases
def trc.ends(+ts: List<&2, Nat>, sel: List<&2, Bool>, +n: Nat, +x: Nat) -> {[Dt.rows([x], [True{}], n), Dt.rows([x], [False{}], n), Dt.rows(Nil{}, sel, n), Dt.rows(ts, Nil{}, n)] == [[Dt.Row{n, x}], Nil{}, Nil{}, Nil{}] : List<&2, List<&2, Dt.Row>>}:
  %Equal.sym(List<&2, Dt.Row>, Dt.rows(ts, Nil{}, n), Nil{}, trc.nil(ts, n)) : {[Dt.rows([x], [True{}], n), Dt.rows([x], [False{}], n), Dt.rows(Nil{}, sel, n), _] == [[Dt.Row{n, x}], Nil{}, Nil{}, Nil{}] : List<&2, List<&2, Dt.Row>>}
  {==}

def DocTags.tag_rows_cut(ts, us, sel, tel, n, x, h):
  (trc.split(ts, us, sel, tel, n, h), trc.ends(ts, sel, n, x))
