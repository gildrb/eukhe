# eukhe: lemmas the proofs of optchat_fit_spec, optchat_batch_spec,
# optchat_msg_spec and optchat_build_spec share: the model's fit, message
# and build are the spec's (spec/memory/optchat.bend), piece by piece

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

# The most due pair
# -----------------

def ob.vs(x: Bool, a: ONode.Node, c: ONode.Node) -> {OFit.best.vs(x, a, c) == S.best.vs(x, a, c) : ONode.Node}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def ob.take(+m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> {OFit.best.take(m, t, a, cur) == S.best.take(m, t, a, cur) : Maybe<&2, ONode.Node>}:
  match cur:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Bool, OFit.more_due(m, t, a, c), S.more_due(m, t, a, c), ob.md(a, c, m, t)) : {Some{OFit.best.vs(_, a, c)} == S.best.take(m, t, a, Some{c}) : Maybe<&2, ONode.Node>}
      Equal.cong(ONode.Node, Maybe<&2, ONode.Node>, z => Some{z}, OFit.best.vs(S.more_due(m, t, a, c), a, c), S.best.vs(S.more_due(m, t, a, c), a, c), ob.vs(S.more_due(m, t, a, c), a, c))

def ob.pick(ok: Bool, +m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> {OFit.best.pick(ok, m, t, a, cur) == S.best.pick(ok, m, t, a, cur) : Maybe<&2, ONode.Node>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      ob.take(m, t, a, cur)

def ob.pair(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, next: Maybe<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>) -> {OFit.best.pair(m, t, info, a, next, cur) == S.best.pair(m, t, info, a, next, cur) : Maybe<&2, ONode.Node>}:
  match next:
    case None{}:
      {==}
    case Some{+b}:
      %Equal.sym(Bool, OFit.mergeable(info, a, b), S.mergeable(info, a, b), ob.merg(info, a, b)) : {OFit.best.pick(_, m, t, a, cur) == S.best.pair(m, t, info, a, Some{b}, cur) : Maybe<&2, ONode.Node>}
      ob.pick(S.mergeable(info, a, b), m, t, a, cur)

def ob.best_go(v: List<&2, ONode.Node>, +cur: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info) -> {OFit.best.go(m, t, info, v, cur) == S.best.go(m, t, info, v, cur) : Maybe<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur), S.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur), ob.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur)) : {OFit.best.go(m, t, info, rest, _) == S.best.go(m, t, info, rest, S.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur)) : Maybe<&2, ONode.Node>}
      ob.best_go(rest, S.best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur), m, t, info)

# Merging
# -------

def ob.mpick(hit: Bool, +x: ONode.Node, +y: ONode.Node, more: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> {OFit.merge.pick(hit, x, y, more, rec) == S.merge.pick(hit, x, y, more, rec) : List<&2, ONode.Node>}:
  match hit:
    case True{}:
      Equal.cong(ONode.Node, List<&2, ONode.Node>, z => z <> more, ONode.Node.parent(x), S.parent(x), ob.parent(x))
    case False{}:
      {==}

def ob.here(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> {OFit.merge.here(info, a, x, rest, rec) == S.merge.here(info, a, x, rest, rec) : List<&2, ONode.Node>}:
  match rest:
    case Nil{}:
      {==}
    case +y <> more:
      %Equal.sym(Bool, ONode.Node.eq(x, a), S.same(x, a), LQ.oq.eq(x, a)) : {OFit.merge.pick(Bool.and(_, OFit.mergeable(info, x, y)), x, y, more, rec) == S.merge.here(info, a, x, y <> more, rec) : List<&2, ONode.Node>}
      %Equal.sym(Bool, OFit.mergeable(info, x, y), S.mergeable(info, x, y), ob.merg(info, x, y)) : {OFit.merge.pick(Bool.and(S.same(x, a), _), x, y, more, rec) == S.merge.here(info, a, x, y <> more, rec) : List<&2, ONode.Node>}
      ob.mpick(Bool.and(S.same(x, a), S.mergeable(info, x, y)), x, y, more, rec)

def ob.merge(v: List<&2, ONode.Node>, +info: OInfo.Info, +a: ONode.Node) -> {OFit.merge(info, v, a) == S.merge(info, v, a) : List<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(info, rest, a), S.merge(info, rest, a), ob.merge(rest, info, a)) : {OFit.merge.here(info, a, x, rest, _) == S.merge(info, x <> rest, a) : List<&2, ONode.Node>}
      ob.here(info, a, x, rest, S.merge(info, rest, a))

# The fit
# -------

def ob.cif(over: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> {OFit.choose.if(over, m, t, info, v) == S.choose.if(over, m, t, info, v) : Maybe<&2, ONode.Node>}:
  match over:
    case False{}:
      {==}
    case True{}:
      ob.best_go(v, None{}, m, t, info)

def ob.choose(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> {OFit.choose(m, t, budget, ph, info, v) == S.choose(m, t, budget, ph, info, v) : Maybe<&2, ONode.Node>}:
  %Equal.sym(Bool, OFit.over(ph, info, v, budget), Nat.is_gt(S.vsize(ph, info, v), budget), ob.over(ph, info, v, budget)) : {OFit.choose.if(_, m, t, info, v) == S.choose(m, t, budget, ph, info, v) : Maybe<&2, ONode.Node>}
  ob.cif(Nat.is_gt(S.vsize(ph, info, v), budget), m, t, info, v)

def ob.cons(+n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> {OFit.fit.cons(n, r) == S.fit.cons(n, r) : List<&2, ONode.Node> & List<&2, ONode.Node>}:
  (ms, out) = r
  {==}

def ob.fit_go(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> {OFit.fit.go(fuel, c, m, t, budget, ph, info, v) == S.fit.go(fuel, c, m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}:
  match fuel c:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n++f Some{+a}:
      +W = S.merge(info, v, a)
      +C = S.choose(m, t, budget, ph, info, W)
      %Equal.sym(List<&2, ONode.Node>, OFit.merge(info, v, a), W, ob.merge(v, info, a)) : {OFit.fit.cons(ONode.Node.parent(a), OFit.fit.go(f, OFit.choose(m, t, budget, ph, info, _), m, t, budget, ph, info, _)) == S.fit.go(1n+f, Some{a}, m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}
      %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(m, t, budget, ph, info, W), C, ob.choose(m, t, budget, ph, info, W)) : {OFit.fit.cons(ONode.Node.parent(a), OFit.fit.go(f, _, m, t, budget, ph, info, W)) == S.fit.go(1n+f, Some{a}, m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node> & List<&2, ONode.Node>, OFit.fit.go(f, C, m, t, budget, ph, info, W), S.fit.go(f, C, m, t, budget, ph, info, W), ob.fit_go(f, C, m, t, budget, ph, info, W)) : {OFit.fit.cons(ONode.Node.parent(a), _) == S.fit.go(1n+f, Some{a}, m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}
      %Equal.sym(ONode.Node, ONode.Node.parent(a), S.parent(a), ob.parent(a)) : {OFit.fit.cons(_, S.fit.go(f, C, m, t, budget, ph, info, W)) == S.fit.go(1n+f, Some{a}, m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}
      ob.cons(S.parent(a), S.fit.go(f, C, m, t, budget, ph, info, W))

def ob.fit(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> {OFit.fit(m, t, budget, ph, info, v) == S.fit(m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}:
  %Equal.sym(Maybe<&2, ONode.Node>, OFit.choose(m, t, budget, ph, info, v), S.choose(m, t, budget, ph, info, v), ob.choose(m, t, budget, ph, info, v)) : {OFit.fit.go(List.length(&2, ONode.Node, v), _, m, t, budget, ph, info, v) == S.fit(m, t, budget, ph, info, v) : List<&2, ONode.Node> & List<&2, ONode.Node>}
  ob.fit_go(List.length(&2, ONode.Node, v), S.choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v)

def ob.fit_view(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> {OFit.fit.view(m, t, budget, ph, info, v) == S.fit.view(m, t, budget, ph, info, v) : List<&2, ONode.Node>}:
  Equal.cong(List<&2, ONode.Node> & List<&2, ONode.Node>, List<&2, ONode.Node>, r => Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, r), OFit.fit(m, t, budget, ph, info, v), S.fit(m, t, budget, ph, info, v), ob.fit(m, t, budget, ph, info, v))

# The compaction sawtooth and a message
# -------------------------------------

def ob.fcif(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> {OStep.fitc.if(over, cfg, t, info, cv) == S.fitc.if(over, cfg, t, info, cv) : List<&2, ONode.Node>}:
  match over:
    case False{}:
      {==}
    case True{}:
      ob.fit_view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv)

def ob.fitc(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> {OStep.fitc(cfg, t, info, cv) == S.fitc(cfg, t, info, cv) : List<&2, ONode.Node>}:
  %Equal.sym(Bool, OFit.over(OState.Cfg.ph(cfg), info, cv, OState.Cfg.cceil(cfg)), Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), ob.over(OState.Cfg.ph(cfg), info, cv, OState.Cfg.cceil(cfg))) : {OStep.fitc.if(_, cfg, t, info, cv) == S.fitc(cfg, t, info, cv) : List<&2, ONode.Node>}
  ob.fcif(Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv)

def ob.mcview(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> {OStep.msg.cview(merged, cfg, t, info, view, cv) == S.msg.cview(merged, cfg, t, info, view, cv) : List<&2, ONode.Node>}:
  match merged:
    case Nil{}:
      ob.fitc(cfg, t, info, cv)
    case h <> rest:
      ob.fit_view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view)

def ob.mbatch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> {OStep.msg.batch(r, cfg, t, info, cv, ready, busy) == S.msg.batch(r, cfg, t, info, cv, ready, busy) : OState.St & List<&2, ONode.Node>}:
  (merged0, view0) = r
  +merged = merged0
  +view = view0
  %Equal.sym(Bool, OFit.over(OState.Cfg.ph(cfg), info, view, OState.Cfg.floor(cfg)), Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), ob.over(OState.Cfg.ph(cfg), info, view, OState.Cfg.floor(cfg))) : {(OState.St{t, info, view, _, OStep.msg.cview(merged, cfg, t, info, view, cv), ready, busy}, merged) == S.msg.batch((merged, view), cfg, t, info, cv, ready, busy) : OState.St & List<&2, ONode.Node>}
  %Equal.sym(List<&2, ONode.Node>, OStep.msg.cview(merged, cfg, t, info, view, cv), S.msg.cview(merged, cfg, t, info, view, cv), ob.mcview(merged, cfg, t, info, view, cv)) : {(OState.St{t, info, view, Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), _, ready, busy}, merged) == S.msg.batch((merged, view), cfg, t, info, cv, ready, busy) : OState.St & List<&2, ONode.Node>}
  {==}

def ob.mgo(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +ready: List<&2, ONode.Node>, +busy: List<&2, ONode.Node>) -> {OStep.msg.go(grow, cfg, t, info, view, cv, ready, busy) == S.msg.go(grow, cfg, t, info, view, cv, ready, busy) : OState.St & List<&2, ONode.Node>}:
  match grow:
    case False{}:
      Equal.cong(List<&2, ONode.Node>, OState.St & List<&2, ONode.Node>, x => (OState.St{t, info, view, False{}, x, ready, busy}, Nil{}), OStep.fitc(cfg, t, info, cv), S.fitc(cfg, t, info, cv), ob.fitc(cfg, t, info, cv))
    case True{}:
      %Equal.sym(List<&2, ONode.Node> & List<&2, ONode.Node>, OFit.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), S.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), ob.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view)) : {OStep.msg.batch(_, cfg, t, info, cv, ready, busy) == S.msg.go(True{}, cfg, t, info, view, cv, ready, busy) : OState.St & List<&2, ONode.Node>}
      ob.mbatch(S.fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

def ob.inc(bs: List<&2, Bool>) -> {OBits.Bits.inc(bs) == S.inc(bs) : List<&2, Bool>}:
  match bs:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          {==}
        case True{}:
          Equal.cong(List<&2, Bool>, List<&2, Bool>, x => False{} <> x, OBits.Bits.inc(t), S.inc(t), ob.inc(t))

def ob.batch(+cfg: OState.Cfg, +s: OState.St) -> {OStep.St.batch(cfg, s) == S.batch(cfg, s) : Bool}:
  %Equal.sym(Bool, OFit.over(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s), OState.Cfg.ceil(cfg)), Nat.is_gt(S.vsize(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s)), OState.Cfg.ceil(cfg)), ob.over(OState.Cfg.ph(cfg), OState.St.info(s), OStep.St.grown(s), OState.Cfg.ceil(cfg))) : {Bool.or(OState.St.shrink(s), _) == S.batch(cfg, s) : Bool}
  {==}

def ob.msg(+cfg: OState.Cfg, +s: OState.St) -> {OStep.msg(cfg, s) == S.msg(cfg, s) : OState.St & List<&2, ONode.Node>}:
  %Equal.sym(Bool, OStep.St.batch(cfg, s), S.batch(cfg, s), ob.batch(cfg, s)) : {OStep.msg.go(_, cfg, OBits.Bits.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s)) == S.msg(cfg, s) : OState.St & List<&2, ONode.Node>}
  %Equal.sym(List<&2, Bool>, OBits.Bits.inc(OState.St.t(s)), S.inc(OState.St.t(s)), ob.inc(OState.St.t(s))) : {OStep.msg.go(S.batch(cfg, s), cfg, _, OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s)) == S.msg(cfg, s) : OState.St & List<&2, ONode.Node>}
  ob.mgo(S.batch(cfg, s), cfg, S.inc(OState.St.t(s)), OState.St.info(s), OStep.St.grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node.leaf(OState.St.t(s))]), OState.St.ready(s), OState.St.busy(s))

# A build
# -------

def ob.flip(bs: List<&2, Bool>) -> {ONode.Bits.flip(bs) == S.flip(bs) : List<&2, Bool>}:
  match bs:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case False{}:
          {==}
        case True{}:
          match t:
            case Nil{}:
              {==}
            case x <> r:
              {==}

def ob.sibling(n: ONode.Node) -> {ONode.Node.sibling(n) == S.sibling(n) : ONode.Node}:
  match n:
    case ONode.Node{l, +i}:
      Equal.cong(List<&2, Bool>, ONode.Node, x => ONode.Node{l, x}, ONode.Bits.flip(i), S.flip(i), ob.flip(i))

def ob.before(a: ONode.Node, b: ONode.Node) -> {ONode.Node.lt(a, b) == S.before(a, b) : Bool}:
  match a b:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      %Equal.sym(Cmp, OBits.Bits.cmp(ia, ib), Nat.cmp(OBits.Bits.val(ia), OBits.Bits.val(ib)), LA.pa.cmp_val(ia, ib)) : {Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Cmp.is_lt(_))) == S.before(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      {==}

def ob.insat(here: Bool, dup: Bool, +x: ONode.Node, +h: ONode.Node, t: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> {ONode.Nodes.ins.at(here, dup, x, h, t, rec) == S.ins.at(here, dup, x, h, t, rec) : List<&2, ONode.Node>}:
  match here dup:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ob.ins(xs: List<&2, ONode.Node>, +x: ONode.Node) -> {ONode.Nodes.ins(xs, x) == S.ins(xs, x) : List<&2, ONode.Node>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, ONode.Node.lt(x, h), S.before(x, h), ob.before(x, h)) : {ONode.Nodes.ins.at(_, ONode.Node.eq(x, h), x, h, t, ONode.Nodes.ins(t, x)) == S.ins(h <> t, x) : List<&2, ONode.Node>}
      %Equal.sym(Bool, ONode.Node.eq(x, h), S.same(x, h), LQ.oq.eq(x, h)) : {ONode.Nodes.ins.at(S.before(x, h), _, x, h, t, ONode.Nodes.ins(t, x)) == S.ins(h <> t, x) : List<&2, ONode.Node>}
      %Equal.sym(List<&2, ONode.Node>, ONode.Nodes.ins(t, x), S.ins(t, x), ob.ins(t, x)) : {ONode.Nodes.ins.at(S.before(x, h), S.same(x, h), x, h, t, _) == S.ins(h <> t, x) : List<&2, ONode.Node>}
      ob.insat(S.before(x, h), S.same(x, h), x, h, t, S.ins(t, x))

def ob.rif(go: Bool, +p: ONode.Node, rs: List<&2, ONode.Node>) -> {OStep.ready.if(go, p, rs) == S.ready.if(go, p, rs) : List<&2, ONode.Node>}:
  match go:
    case False{}:
      {==}
    case True{}:
      ob.ins(rs, p)

def ob.note(+info: OInfo.Info, +n: ONode.Node, rs: List<&2, ONode.Node>) -> {OStep.ready.note(info, n, rs) == S.ready_note(info, n, rs) : List<&2, ONode.Node>}:
  %Equal.sym(ONode.Node, ONode.Node.sibling(n), S.sibling(n), ob.sibling(n)) : {OStep.ready.if(Bool.and(OInfo.Info.built(info, _), Bool.not(OInfo.Info.built(info, ONode.Node.parent(n)))), ONode.Node.parent(n), rs) == S.ready_note(info, n, rs) : List<&2, ONode.Node>}
  %Equal.sym(ONode.Node, ONode.Node.parent(n), S.parent(n), ob.parent(n)) : {OStep.ready.if(Bool.and(OInfo.Info.built(info, S.sibling(n)), Bool.not(OInfo.Info.built(info, _))), _, rs) == S.ready_note(info, n, rs) : List<&2, ONode.Node>}
  ob.rif(Bool.and(OInfo.Info.built(info, S.sibling(n)), Bool.not(OInfo.Info.built(info, S.parent(n)))), S.parent(n), rs)

def ob.build(+cfg: OState.Cfg, s: OState.St, +n: ONode.Node, +size: Nat) -> {OStep.build(cfg, s, n, size) == S.build(cfg, s, n, size) : OState.St}:
  match s:
    case OState.St{+t, i0, +view, +shrink, +cview, +ready, +busy}:
      +I = OInfo.Info.set(i0, n, size)
      %Equal.sym(List<&2, ONode.Node>, OStep.fitc(cfg, t, I, cview), S.fitc(cfg, t, I, cview), ob.fitc(cfg, t, I, cview)) : {OState.St{t, I, view, shrink, _, OStep.ready.note(I, n, ONode.Nodes.del(ready, n)), ONode.Nodes.del(busy, n)} == S.build(cfg, OState.St{t, i0, view, shrink, cview, ready, busy}, n, size) : OState.St}
      %Equal.sym(List<&2, ONode.Node>, ONode.Nodes.del(ready, n), S.busy_del(ready, n), LQ.oq.del(ready, n)) : {OState.St{t, I, view, shrink, S.fitc(cfg, t, I, cview), OStep.ready.note(I, n, _), ONode.Nodes.del(busy, n)} == S.build(cfg, OState.St{t, i0, view, shrink, cview, ready, busy}, n, size) : OState.St}
      %Equal.sym(List<&2, ONode.Node>, OStep.ready.note(I, n, S.busy_del(ready, n)), S.ready_note(I, n, S.busy_del(ready, n)), ob.note(I, n, S.busy_del(ready, n))) : {OState.St{t, I, view, shrink, S.fitc(cfg, t, I, cview), _, ONode.Nodes.del(busy, n)} == S.build(cfg, OState.St{t, i0, view, shrink, cview, ready, busy}, n, size) : OState.St}
      %Equal.sym(List<&2, ONode.Node>, ONode.Nodes.del(busy, n), S.busy_del(busy, n), LQ.oq.del(busy, n)) : {OState.St{t, I, view, shrink, S.fitc(cfg, t, I, cview), S.ready_note(I, n, S.busy_del(ready, n)), _} == S.build(cfg, OState.St{t, i0, view, shrink, cview, ready, busy}, n, size) : OState.St}
      {==}
