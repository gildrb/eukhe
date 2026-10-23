# eukhe: lemmas of the proof of LAW push_agrees_always: list

import Base
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/push.bend as OPush
import ../../base/logic/nat.bend as LLogicNat
import ../../base/nat.bend as LNat
import ./logic.bend as LLLogic

def pa.vals_rev(xs: List<&2, List<&2, Bool>>, acc: List<&2, List<&2, Bool>>) -> {LLLogic.pa.vals(List.reverse.go(&2, List<&2, Bool>, xs, acc)) == List.reverse.go(&2, Nat, LLLogic.pa.vals(xs), LLLogic.pa.vals(acc)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      pa.vals_rev(t, h <> acc)

def pa.app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => h <> z, List.append(&2, Nat, List.append(&2, Nat, t, ys), zs), List.append(&2, Nat, t, List.append(&2, Nat, ys, zs)), pa.app_assoc(t, ys, zs))

# reversing onto acc is reversing, then acc
def pa.rev_app(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, xs, acc) == List.append(&2, Nat, List.reverse.go(&2, Nat, xs, Nil{}), acc) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +R = List.reverse.go(&2, Nat, t, Nil{})
      %Equal.sym(List<&2, Nat>, List.reverse.go(&2, Nat, t, [h]), List.append(&2, Nat, R, [h]), pa.rev_app(t, [h])) : {List.reverse.go(&2, Nat, t, h <> acc) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, R, [h]), acc), List.append(&2, Nat, R, h <> acc), pa.app_assoc(R, [h], acc)) : {List.reverse.go(&2, Nat, t, h <> acc) == _ : List<&2, Nat>}
      pa.rev_app(t, h <> acc)

def pa.dbls_rev(xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.reverse.go(&2, Nat, LLLogic.pa.dbls(xs), LLLogic.pa.dbls(acc)) == LLLogic.pa.dbls(List.reverse.go(&2, Nat, xs, acc)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      pa.dbls_rev(t, h <> acc)

def pa.app2(-xs: List<&2, Nat>, -ys: List<&2, Nat>, -a: Nat, -b: Nat, et: {xs == ys : List<&2, Nat>}, ea: {a == b : Nat}) -> {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, ys, [b]) : List<&2, Nat>}:
  %et : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, _, [b]) : List<&2, Nat>}
  %ea : {List.append(&2, Nat, xs, [a]) == List.append(&2, Nat, xs, [_]) : List<&2, Nat>}
  {==}

def pa.len_GE(ds: List<&2, Bool>, +j: Nat) -> {List.length(&2, OPush.Entry, LLLogic.pa.GE(ds, j)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> +r:
      match d:
        case False{}:
          LLogicNat.pa.succ(List.length(&2, OPush.Entry, LLLogic.pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))
        case True{}:
          LLogicNat.pa.succ(List.length(&2, OPush.Entry, LLLogic.pa.GE(r, 1n+j)), List.length(&2, Bool, r), pa.len_GE(r, 1n+j))

def pa.len_app1(xs: List<&2, ONode.Node>, -y: ONode.Node) -> {List.length(&2, ONode.Node, List.append(&2, ONode.Node, xs, [y])) == 1n+List.length(&2, ONode.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      LLogicNat.pa.succ(List.length(&2, ONode.Node, List.append(&2, ONode.Node, t, [y])), 1n+List.length(&2, ONode.Node, t), pa.len_app1(t, y))

def pa.size_app(xs: List<&2, ONode.Node>, +ys: List<&2, ONode.Node>) -> {LLLogic.pa.vs(List.append(&2, ONode.Node, xs, ys)) == Nat.add(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, xs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(LLLogic.pa.vs(ys), 0n), LLLogic.pa.vs(ys), LNat.pa.add_zero(LLLogic.pa.vs(ys)))
    case h <> +t:
      Equal.trans(Nat, 1n+LLLogic.pa.vs(List.append(&2, ONode.Node, t, ys)), 1n+Nat.add(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, t)), Nat.add(LLLogic.pa.vs(ys), 1n+List.length(&2, ONode.Node, t)),
        LLogicNat.pa.succ(LLLogic.pa.vs(List.append(&2, ONode.Node, t, ys)), Nat.add(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, t)), pa.size_app(t, ys)),
        Equal.sym(Nat, Nat.add(LLLogic.pa.vs(ys), 1n+List.length(&2, ONode.Node, t)), 1n+Nat.add(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, t)), LNat.pa.add_succ(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, t))))

def pa.app_ab(xs: List<&2, ONode.Node>, +a: ONode.Node, +b: ONode.Node) -> {List.append(&2, ONode.Node, List.append(&2, ONode.Node, xs, [a]), [b]) == List.append(&2, ONode.Node, xs, [a, b]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, z => h <> z, List.append(&2, ONode.Node, List.append(&2, ONode.Node, t, [a]), [b]), List.append(&2, ONode.Node, t, [a, b]), pa.app_ab(t, a, b))

def pa.len_lifts(xs: List<&2, ONode.Node>) -> {List.length(&2, ONode.Node, LLLogic.pa.lifts(xs)) == List.length(&2, ONode.Node, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      LLogicNat.pa.succ(List.length(&2, ONode.Node, LLLogic.pa.lifts(t)), List.length(&2, ONode.Node, t), pa.len_lifts(t))

def pa.len_GV(ds: List<&2, Bool>) -> {List.length(&2, ONode.Node, LLLogic.pa.GV(ds)) == List.length(&2, Bool, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +r:
      Equal.trans(Nat, List.length(&2, ONode.Node, LLLogic.pa.GV(d <> r)), 1n+List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r))), 1n+List.length(&2, Bool, r),
        pa.len_app1(LLLogic.pa.lifts(LLLogic.pa.GV(r)), LLLogic.pa.line(d, LLLogic.pa.B(r))),
        LLogicNat.pa.succ(List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r))), List.length(&2, ONode.Node, LLLogic.pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(LLLogic.pa.GV(r)), pa.len_GV(r))))

# the higher lines of the view of r, then ys
def pa.size_hi(+r: List<&2, Bool>, +ys: List<&2, ONode.Node>) -> {LLLogic.pa.vs(List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), ys)) == Nat.add(LLLogic.pa.vs(ys), List.length(&2, Bool, r)) : Nat}:
  Equal.trans(Nat, LLLogic.pa.vs(List.append(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)), ys)), Nat.add(LLLogic.pa.vs(ys), List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r)))), Nat.add(LLLogic.pa.vs(ys), List.length(&2, Bool, r)),
    pa.size_app(LLLogic.pa.lifts(LLLogic.pa.GV(r)), ys),
    Equal.cong(Nat, Nat, z => Nat.add(LLLogic.pa.vs(ys), z), List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r))), List.length(&2, Bool, r), Equal.trans(Nat, List.length(&2, ONode.Node, LLLogic.pa.lifts(LLLogic.pa.GV(r))), List.length(&2, ONode.Node, LLLogic.pa.GV(r)), List.length(&2, Bool, r), pa.len_lifts(LLLogic.pa.GV(r)), pa.len_GV(r))))

def pa.good_app(xs: List<&2, ONode.Node>, -y: ONode.Node, -R: Nat, gx: LLLogic.pa.GoodAll(R, xs), gy: LLLogic.pa.Good(y, R)) -> LLLogic.pa.GoodAll(R, List.append(&2, ONode.Node, xs, [y])):
  match xs:
    case Nil{}:
      (gy, Unit{})
    case c <> t:
      (gc, gt) = gx
      (gc, pa.good_app(t, y, R, gt, gy))

def pa.lifts_app1(xs: List<&2, ONode.Node>, +y: ONode.Node) -> {LLLogic.pa.lifts(List.append(&2, ONode.Node, xs, [y])) == List.append(&2, ONode.Node, LLLogic.pa.lifts(xs), [LLLogic.pa.lift(y)]) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, z => LLLogic.pa.lift(h) <> z, LLLogic.pa.lifts(List.append(&2, ONode.Node, t, [y])), List.append(&2, ONode.Node, LLLogic.pa.lifts(t), [LLLogic.pa.lift(y)]), pa.lifts_app1(t, y))
