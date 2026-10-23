# eukhe: the proof of LAW tx_committed_inert

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base/bool/misc.bend as LBoolMisc

# Committed blocks are inert
def ps.app_assoc(xs: List<&2, Sc.Blk>, -ys: List<&2, Sc.Blk>, -zs: List<&2, Sc.Blk>) -> {List.append(&2, Sc.Blk, List.append(&2, Sc.Blk, xs, ys), zs) == List.append(&2, Sc.Blk, xs, List.append(&2, Sc.Blk, ys, zs)) : List<&2, Sc.Blk>}:
  match xs:
    case Nil{}:
      {==}
    case x <> xr:
      %ps.app_assoc(xr, ys, zs) : {x <> List.append(&2, Sc.Blk, List.append(&2, Sc.Blk, xr, ys), zs) == x <> _ : List<&2, Sc.Blk>}
      {==}

def ps.bcons(-x: Sc.Blk, -a: List<&2, Sc.Blk>, -b: List<&2, Sc.Blk>, e: {a == b : List<&2, Sc.Blk>}) -> {x <> a == x <> b : List<&2, Sc.Blk>}:
  %e : {x <> a == x <> _ : List<&2, Sc.Blk>}
  {==}

# a committed block heads the edit unchanged, hit or not
def ps.edit_comm(+i: Nat, +l: Nat, L: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>, h: Bool) -> {Sc.edit.go(Sc.Blk{i, Sc.Comm{}, l} <> L, x, g, h) == Sc.Blk{i, Sc.Comm{}, l} <> Sc.edit.go(L, x, g, Sc.bid.at(L, x)) : List<&2, Sc.Blk>}:
  match g h:
    case None{} True{}:
      {==}
    case Some{n} True{}:
      {==}
    case None{} False{}:
      {==}
    case Some{n} False{}:
      {==}

def ps.edit_inert(cs: List<&2, Sc.Blk>, +bs: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>, comm: {Screen.all_comm(cs) == True{} : Bool}) -> {Sc.edit.go(List.append(&2, Sc.Blk, cs, bs), x, g, Sc.bid.at(List.append(&2, Sc.Blk, cs, bs), x)) == List.append(&2, Sc.Blk, cs, Sc.edit.go(bs, x, g, Sc.bid.at(bs, x))) : List<&2, Sc.Blk>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +cr:
      match c:
        case Sc.Blk{+i, s, +l}:
          match s:
            case Sc.Comm{}:
              +L = List.append(&2, Sc.Blk, cr, bs)
              +R = List.append(&2, Sc.Blk, cr, Sc.edit.go(bs, x, g, Sc.bid.at(bs, x)))
              Equal.trans(List<&2, Sc.Blk>, Sc.edit.go(Sc.Blk{i, Sc.Comm{}, l} <> L, x, g, Sc.bid.at(Sc.Blk{i, Sc.Comm{}, l} <> L, x)), Sc.Blk{i, Sc.Comm{}, l} <> Sc.edit.go(L, x, g, Sc.bid.at(L, x)), Sc.Blk{i, Sc.Comm{}, l} <> R, ps.edit_comm(i, l, L, x, g, Sc.bid.at(Sc.Blk{i, Sc.Comm{}, l} <> L, x)), ps.bcons(Sc.Blk{i, Sc.Comm{}, l}, Sc.edit.go(L, x, g, Sc.bid.at(L, x)), R, ps.edit_inert(cr, bs, x, g, comm)))
            case Sc.Final{}:
              LBoolMisc.screen.ps.absurdF({Sc.edit.go(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Final{}, l} <> cr, bs), x, g, Sc.bid.at(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Final{}, l} <> cr, bs), x)) == List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Final{}, l} <> cr, Sc.edit.go(bs, x, g, Sc.bid.at(bs, x))) : List<&2, Sc.Blk>}, comm)
            case Sc.Active{}:
              LBoolMisc.screen.ps.absurdF({Sc.edit.go(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Active{}, l} <> cr, bs), x, g, Sc.bid.at(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Active{}, l} <> cr, bs), x)) == List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Active{}, l} <> cr, Sc.edit.go(bs, x, g, Sc.bid.at(bs, x))) : List<&2, Sc.Blk>}, comm)

def ps.flush_inert(cs: List<&2, Sc.Blk>, -bs: List<&2, Sc.Blk>, comm: {Screen.all_comm(cs) == True{} : Bool}) -> {Sc.flush(List.append(&2, Sc.Blk, cs, bs)) == List.append(&2, Sc.Blk, cs, Sc.flush(bs)) : List<&2, Sc.Blk>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +cr:
      match c:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              ps.bcons(Sc.Blk{i, Sc.Comm{}, l}, Sc.flush(List.append(&2, Sc.Blk, cr, bs)), List.append(&2, Sc.Blk, cr, Sc.flush(bs)), ps.flush_inert(cr, bs, comm))
            case Sc.Final{}:
              LBoolMisc.screen.ps.absurdF({Sc.flush(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Final{}, l} <> cr, bs)) == List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Final{}, l} <> cr, Sc.flush(bs)) : List<&2, Sc.Blk>}, comm)
            case Sc.Active{}:
              LBoolMisc.screen.ps.absurdF({Sc.flush(List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Active{}, l} <> cr, bs)) == List.append(&2, Sc.Blk, Sc.Blk{i, Sc.Active{}, l} <> cr, Sc.flush(bs)) : List<&2, Sc.Blk>}, comm)

def ps.tx_eq(-a: List<&2, Sc.Blk>, -b: List<&2, Sc.Blk>, -n: Nat, -w: Nat, e: {a == b : List<&2, Sc.Blk>}) -> {Sc.Tx{a, n, w} == Sc.Tx{b, n, w} : Sc.Tx}:
  %e : {Sc.Tx{a, n, w} == Sc.Tx{_, n, w} : Sc.Tx}
  {==}

def ps.step_inert(+cs: List<&2, Sc.Blk>, t: Sc.Tx, e: Sc.Ev, +comm: {Screen.all_comm(cs) == True{} : Bool}) -> {Sc.step(Screen.under(cs, t), e) == Screen.under(cs, Sc.step(t, e)) : Sc.Tx}:
  match t:
    case Sc.Tx{+bs, +n, +w}:
      match e:
        case Sc.Open{}:
          ps.tx_eq(List.append(&2, Sc.Blk, List.append(&2, Sc.Blk, cs, bs), [Sc.Blk{n, Sc.Active{}, 0n}]), List.append(&2, Sc.Blk, cs, List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}])), 1n+n, w, ps.app_assoc(cs, bs, [Sc.Blk{n, Sc.Active{}, 0n}]))
        case Sc.Grow{x, k}:
          ps.tx_eq(Sc.edit(List.append(&2, Sc.Blk, cs, bs), x, Some{k}), List.append(&2, Sc.Blk, cs, Sc.edit(bs, x, Some{k})), n, w, ps.edit_inert(cs, bs, x, Some{k}, comm))
        case Sc.Fin{x}:
          ps.tx_eq(Sc.edit(List.append(&2, Sc.Blk, cs, bs), x, None{}), List.append(&2, Sc.Blk, cs, Sc.edit(bs, x, None{})), n, w, ps.edit_inert(cs, bs, x, None{}, comm))
        case Sc.Flush{}:
          ps.tx_eq(Sc.flush(List.append(&2, Sc.Blk, cs, bs)), List.append(&2, Sc.Blk, cs, Sc.flush(bs)), n, w, ps.flush_inert(cs, bs, comm))
        case Sc.Resize{v}:
          {==}

def ps.run_inert(es: List<&2, Sc.Ev>, +cs: List<&2, Sc.Blk>, +t: Sc.Tx, +comm: {Screen.all_comm(cs) == True{} : Bool}) -> {Sc.run(es, Screen.under(cs, t)) == Screen.under(cs, Sc.run(es, t)) : Sc.Tx}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %Equal.sym(Sc.Tx, Sc.step(Screen.under(cs, t), e), Screen.under(cs, Sc.step(t, e)), ps.step_inert(cs, t, e, comm)) : {Sc.run(rest, _) == Screen.under(cs, Sc.run(rest, Sc.step(t, e))) : Sc.Tx}
      ps.run_inert(rest, cs, Sc.step(t, e), comm)

def ps.tx_committed_inert(es: List<&2, Sc.Ev>, +cs: List<&2, Sc.Blk>, +bs: List<&2, Sc.Blk>, +n: Nat, +w: Nat, comm: {Screen.all_comm(cs) == True{} : Bool}) -> {Sc.run(es, Sc.Tx{List.append(&2, Sc.Blk, cs, bs), n, w}) == Screen.under(cs, Sc.run(es, Sc.Tx{bs, n, w})) : Sc.Tx}:
  ps.run_inert(es, cs, Sc.Tx{bs, n, w}, comm)

def Screen.tx_committed_inert(es, cs, bs, n, w, comm):
  ps.tx_committed_inert(es, cs, bs, n, w, comm)
