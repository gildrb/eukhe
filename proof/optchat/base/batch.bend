# eukhe: lemmas the proofs of area optchat share: the model's sizes,
# geometry, due order, batch test and node order computed on bits are the
# spec's computed on numbers (spec/memory/optchat.bend), piece by piece

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/step.bend as OStep
import ../../../spec/memory/optchat.bend as S
import ../push_agrees_always/logic.bend as LLLogic
import ../push_agrees_always/optchat.bend as LLOptchat
import ./step.bend as LA
import ./over.bend as LOv
import ./queries.bend as LQ

# Sizes
# -----

def ob.size_of(+ph: Nat, m: Maybe<&2, Nat>) -> {OFit.size.of(ph, m) == S.size_of(ph, m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{z}:
      {==}

def ob.vsize(+ph: Nat, +info: OInfo.Info, v: List<&2, ONode.Node>) -> {OFit.view_size(ph, info, v) == S.vsize(ph, info, v) : Nat}:
  match v:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Nat, OFit.size.of(ph, OInfo.Info.get(info, h)), S.size_of(ph, OInfo.Info.get(info, h)), ob.size_of(ph, OInfo.Info.get(info, h))) : {Nat.add(_, OFit.view_size(ph, info, t)) == S.vsize(ph, info, h <> t) : Nat}
      %Equal.sym(Nat, OFit.view_size(ph, info, t), S.vsize(ph, info, t), ob.vsize(ph, info, t)) : {Nat.add(S.size_of(ph, OInfo.Info.get(info, h)), _) == S.vsize(ph, info, h <> t) : Nat}
      {==}

def ob.over(+ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>, +b: Nat) -> {OFit.over(ph, info, v, b) == Nat.is_gt(S.vsize(ph, info, v), b) : Bool}:
  %ob.vsize(ph, info, v) : {OFit.over(ph, info, v, b) == Nat.is_gt(_, b) : Bool}
  LOv.ov.over(ph, info, v, b)

# Pairs
# -----

def ob.beq(x: Bool, y: Bool, r: Bool) -> {Bool.and(OBits.Bool.eq(x, y), r) == Bool.and(S.bit_same(x, y), r) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ob.bits_eq(a: List<&2, Bool>, b: List<&2, Bool>) -> {OBits.Bits.eq(a, b) == S.bits_same(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> ys:
      {==}
    case x <> xs Nil{}:
      {==}
    case +x <> +xs +y <> +ys:
      %Equal.sym(Bool, OBits.Bits.eq(xs, ys), S.bits_same(xs, ys), ob.bits_eq(xs, ys)) : {Bool.and(OBits.Bool.eq(x, y), _) == S.bits_same(x <> xs, y <> ys) : Bool}
      ob.beq(x, y, S.bits_same(xs, ys))

def ob.low(i: List<&2, Bool>) -> {OBits.Bits.low(i) == S.low(i) : Bool}:
  match i:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def ob.up(i: List<&2, Bool>) -> {OBits.Bits.up(i) == S.half(i) : List<&2, Bool>}:
  match i:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def ob.parent(n: ONode.Node) -> {ONode.Node.parent(n) == S.parent(n) : ONode.Node}:
  match n:
    case ONode.Node{l, +i}:
      Equal.cong(List<&2, Bool>, ONode.Node, x => ONode.Node{1n+l, x}, OBits.Bits.up(i), S.half(i), ob.up(i))

def ob.sib(a: ONode.Node, b: ONode.Node) -> {ONode.Node.sib(a, b) == S.sib(a, b) : Bool}:
  match a b:
    case ONode.Node{la, +ia} ONode.Node{lb, +ib}:
      %Equal.sym(Bool, OBits.Bits.low(ia), S.low(ia), ob.low(ia)) : {Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(_), Bool.and(OBits.Bits.low(ib), OBits.Bits.eq(OBits.Bits.up(ia), OBits.Bits.up(ib))))) == S.sib(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      %Equal.sym(Bool, OBits.Bits.low(ib), S.low(ib), ob.low(ib)) : {Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(S.low(ia)), Bool.and(_, OBits.Bits.eq(OBits.Bits.up(ia), OBits.Bits.up(ib))))) == S.sib(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      %Equal.sym(List<&2, Bool>, OBits.Bits.up(ia), S.half(ia), ob.up(ia)) : {Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(S.low(ia)), Bool.and(S.low(ib), OBits.Bits.eq(_, OBits.Bits.up(ib))))) == S.sib(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      %Equal.sym(List<&2, Bool>, OBits.Bits.up(ib), S.half(ib), ob.up(ib)) : {Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(S.low(ia)), Bool.and(S.low(ib), OBits.Bits.eq(S.half(ia), _)))) == S.sib(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      %Equal.sym(Bool, OBits.Bits.eq(S.half(ia), S.half(ib)), S.bits_same(S.half(ia), S.half(ib)), ob.bits_eq(S.half(ia), S.half(ib))) : {Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(S.low(ia)), Bool.and(S.low(ib), _))) == S.sib(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      {==}

def ob.merg(+info: OInfo.Info, +a: ONode.Node, +b: ONode.Node) -> {OFit.mergeable(info, a, b) == S.mergeable(info, a, b) : Bool}:
  %Equal.sym(Bool, ONode.Node.sib(a, b), S.sib(a, b), ob.sib(a, b)) : {Bool.and(_, OInfo.Info.built(info, ONode.Node.parent(a))) == S.mergeable(info, a, b) : Bool}
  %Equal.sym(ONode.Node, ONode.Node.parent(a), S.parent(a), ob.parent(a)) : {Bool.and(S.sib(a, b), OInfo.Info.built(info, _)) == S.mergeable(info, a, b) : Bool}
  {==}

# The due order
# -------------

def ob.vshl(+l: Nat, +x: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.shl(l, x)) == S.sh(l, OBits.Bits.val(x)) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.shl(l, x)), LLLogic.pa.sh(l, OBits.Bits.val(x)), S.sh(l, OBits.Bits.val(x)), LLOptchat.pa.val_shl(l, x), LQ.oq.sh(l, OBits.Bits.val(x)))

def ob.add_sh(+l1: Nat, +p: List<&2, Bool>, +l2: Nat, +q: List<&2, Bool>) -> {Nat.add(OBits.Bits.val(OBits.Bits.shl(l1, p)), OBits.Bits.val(OBits.Bits.shl(l2, q))) == Nat.add(S.sh(l1, OBits.Bits.val(p)), S.sh(l2, OBits.Bits.val(q))) : Nat}:
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(l1, p)), S.sh(l1, OBits.Bits.val(p)), ob.vshl(l1, p)) : {Nat.add(_, OBits.Bits.val(OBits.Bits.shl(l2, q))) == Nat.add(S.sh(l1, OBits.Bits.val(p)), S.sh(l2, OBits.Bits.val(q))) : Nat}
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(l2, q)), S.sh(l2, OBits.Bits.val(q)), ob.vshl(l2, q)) : {Nat.add(S.sh(l1, OBits.Bits.val(p)), _) == Nat.add(S.sh(l1, OBits.Bits.val(p)), S.sh(l2, OBits.Bits.val(q))) : Nat}
  {==}

# the value of two shifted lists added
def ob.vadd(+l1: Nat, +p: List<&2, Bool>, +l2: Nat, +q: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.add(OBits.Bits.shl(l1, p), OBits.Bits.shl(l2, q))) == Nat.add(S.sh(l1, OBits.Bits.val(p)), S.sh(l2, OBits.Bits.val(q))) : Nat}:
  Equal.trans(Nat, OBits.Bits.val(OBits.Bits.add(OBits.Bits.shl(l1, p), OBits.Bits.shl(l2, q))), Nat.add(OBits.Bits.val(OBits.Bits.shl(l1, p)), OBits.Bits.val(OBits.Bits.shl(l2, q))), Nat.add(S.sh(l1, OBits.Bits.val(p)), S.sh(l2, OBits.Bits.val(q))), LLOptchat.pa.val_add(OBits.Bits.shl(l1, p), OBits.Bits.shl(l2, q), False{}), ob.add_sh(l1, p, l2, q))

def ob.cross(+u: List<&2, Bool>, +la: Nat, +lb: Nat, +xa: List<&2, Bool>, +xb: List<&2, Bool>) -> {OFit.more_due.cross(u, la, lb, xa, xb) == S.cross(OBits.Bits.val(u), la, lb, OBits.Bits.val(xa), OBits.Bits.val(xb)) : Bool}:
  +X = OBits.Bits.add(OBits.Bits.shl(lb, u), OBits.Bits.shl(la, xb))
  +Y = OBits.Bits.add(OBits.Bits.shl(la, u), OBits.Bits.shl(lb, xa))
  %Equal.sym(Cmp, OBits.Bits.cmp(X, Y), Nat.cmp(OBits.Bits.val(X), OBits.Bits.val(Y)), LA.pa.cmp_val(X, Y)) : {Cmp.is_gt(_) == S.cross(OBits.Bits.val(u), la, lb, OBits.Bits.val(xa), OBits.Bits.val(xb)) : Bool}
  %Equal.sym(Nat, OBits.Bits.val(X), Nat.add(S.sh(lb, OBits.Bits.val(u)), S.sh(la, OBits.Bits.val(xb))), ob.vadd(lb, u, la, xb)) : {Cmp.is_gt(Nat.cmp(_, OBits.Bits.val(Y))) == S.cross(OBits.Bits.val(u), la, lb, OBits.Bits.val(xa), OBits.Bits.val(xb)) : Bool}
  %Equal.sym(Nat, OBits.Bits.val(Y), Nat.add(S.sh(la, OBits.Bits.val(u)), S.sh(lb, OBits.Bits.val(xa))), ob.vadd(la, u, lb, xa)) : {Cmp.is_gt(Nat.cmp(Nat.add(S.sh(lb, OBits.Bits.val(u)), S.sh(la, OBits.Bits.val(xb))), _)) == S.cross(OBits.Bits.val(u), la, lb, OBits.Bits.val(xa), OBits.Bits.val(xb)) : Bool}
  {==}

# a pair's end in bits, (i+2)·2^l
def ob.vpe(+l: Nat, +i: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i)))) == S.sh(l, 2n+OBits.Bits.val(i)) : Nat}:
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i)))), S.sh(l, OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i)))), ob.vshl(l, OBits.Bits.inc(OBits.Bits.inc(i)))) : {_ == S.sh(l, 2n+OBits.Bits.val(i)) : Nat}
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.inc(OBits.Bits.inc(i))), 1n+OBits.Bits.val(OBits.Bits.inc(i)), LLOptchat.pa.val_inc(OBits.Bits.inc(i))) : {S.sh(l, _) == S.sh(l, 2n+OBits.Bits.val(i)) : Nat}
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.inc(i)), 1n+OBits.Bits.val(i), LLOptchat.pa.val_inc(i)) : {S.sh(l, 1n+_) == S.sh(l, 2n+OBits.Bits.val(i)) : Nat}
  {==}

def ob.md(a: ONode.Node, b: ONode.Node, m: OFit.Age, +t: List<&2, Bool>) -> {OFit.more_due(m, t, a, b) == S.more_due(m, t, a, b) : Bool}:
  match a b:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      match m:
        case OFit.Last{}:
          +XA = OBits.Bits.shl(la, OBits.Bits.inc(OBits.Bits.inc(ia)))
          +XB = OBits.Bits.shl(lb, OBits.Bits.inc(OBits.Bits.inc(ib)))
          %Equal.sym(Bool, OFit.more_due.cross(OBits.Bits.inc(t), la, lb, XA, XB), S.cross(OBits.Bits.val(OBits.Bits.inc(t)), la, lb, OBits.Bits.val(XA), OBits.Bits.val(XB)), ob.cross(OBits.Bits.inc(t), la, lb, XA, XB)) : {_ == S.more_due(OFit.Last{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.inc(t)), 1n+OBits.Bits.val(t), LLOptchat.pa.val_inc(t)) : {S.cross(_, la, lb, OBits.Bits.val(XA), OBits.Bits.val(XB)) == S.more_due(OFit.Last{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          %Equal.sym(Nat, OBits.Bits.val(XA), S.sh(la, 2n+OBits.Bits.val(ia)), ob.vpe(la, ia)) : {S.cross(1n+OBits.Bits.val(t), la, lb, _, OBits.Bits.val(XB)) == S.more_due(OFit.Last{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          %Equal.sym(Nat, OBits.Bits.val(XB), S.sh(lb, 2n+OBits.Bits.val(ib)), ob.vpe(lb, ib)) : {S.cross(1n+OBits.Bits.val(t), la, lb, S.sh(la, 2n+OBits.Bits.val(ia)), _) == S.more_due(OFit.Last{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          {==}
        case OFit.First{}:
          %Equal.sym(Bool, OFit.more_due.cross(t, la, lb, OBits.Bits.shl(la, ia), OBits.Bits.shl(lb, ib)), S.cross(OBits.Bits.val(t), la, lb, OBits.Bits.val(OBits.Bits.shl(la, ia)), OBits.Bits.val(OBits.Bits.shl(lb, ib))), ob.cross(t, la, lb, OBits.Bits.shl(la, ia), OBits.Bits.shl(lb, ib))) : {_ == S.more_due(OFit.First{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(la, ia)), S.sh(la, OBits.Bits.val(ia)), ob.vshl(la, ia)) : {S.cross(OBits.Bits.val(t), la, lb, _, OBits.Bits.val(OBits.Bits.shl(lb, ib))) == S.more_due(OFit.First{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(lb, ib)), S.sh(lb, OBits.Bits.val(ib)), ob.vshl(lb, ib)) : {S.cross(OBits.Bits.val(t), la, lb, S.sh(la, OBits.Bits.val(ia)), _) == S.more_due(OFit.First{}, t, ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
          {==}

# The batch test and the ready order
# ----------------------------------

# the model's batch test is the spec's
def ob.batch(+cfg: OState.Cfg, +s: OState.St) -> {OStep.St.batch(cfg, s) == S.batch(cfg, s) : Bool}:
  %Equal.sym(Bool, OFit.over(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s), OState.Cfg.ceil(cfg)), Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s)), OState.Cfg.ceil(cfg)), ob.over(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s), OState.Cfg.ceil(cfg))) : {Bool.or(OState.St.shrink(s), _) == S.batch(cfg, s) : Bool}
  {==}

# the model's node order is the spec's
def ob.before(a: ONode.Node, b: ONode.Node) -> {ONode.Node.lt(a, b) == S.before(a, b) : Bool}:
  match a b:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      %Equal.sym(Cmp, OBits.Bits.cmp(ia, ib), Nat.cmp(OBits.Bits.val(ia), OBits.Bits.val(ib)), LA.pa.cmp_val(ia, ib)) : {Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Cmp.is_lt(_))) == S.before(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      {==}
