# eukhe: lemmas the proofs of laws/optchat/queries.bend share: the
# model's node sets, work queue and compaction view are the spec's
# (spec/memory/optchat.bend)

import Base
import ../../../bend/optchat/bits.bend as OBits
import ../../../bend/optchat/node.bend as ONode
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/state.bend as OState
import ../../../bend/optchat/step.bend as OStep
import ../../../bend/optchat/queue.bend as OQueue
import ../../../bend/optchat/ctx.bend as OCtx
import ../../../spec/memory/optchat.bend as S
import ../push_agrees_always/logic.bend as LLLogic
import ../push_agrees_always/optchat.bend as LLOptchat
import ./step.bend as LA

# Logic and Nat
# -------------

def oq.FT(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False is not True
def oq.false_true(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : oq.FT(_, G)
  Unit{}

def oq.sub0(r: Nat) -> {Nat.sub(r, 0n) == r : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      {==}

def oq.ge_zero(x: Nat) -> {Nat.is_ge(x, 0n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# at least j, and more, is at least j
def oq.ge_add(u: Nat, j: Nat, +x: Nat, e: {Nat.is_ge(u, j) == True{} : Bool}) -> {Nat.is_ge(Nat.add(u, x), j) == True{} : Bool}:
  match u j:
    case 0n 0n:
      oq.ge_zero(x)
    case 0n 1n+q:
      oq.false_true({Nat.is_ge(x, 1n+q) == True{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      oq.ge_add(p, q, x, e)

# x·2^l: the push proof's doubling is the spec's
def oq.sh(l: Nat, +x: Nat) -> {LLLogic.pa.sh(l, x) == S.sh(l, x) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => Nat.double(y), LLLogic.pa.sh(p, x), S.sh(p, x), oq.sh(p, x))

# Nodes
# -----

def oq.eq(a: ONode.Node, b: ONode.Node) -> {ONode.Node.eq(a, b) == S.same(a, b) : Bool}:
  match a b:
    case ONode.Node{+la, +ia} ONode.Node{+lb, +ib}:
      %Equal.sym(Cmp, OBits.Bits.cmp(ia, ib), Nat.cmp(OBits.Bits.val(ia), OBits.Bits.val(ib)), LA.pa.cmp_val(ia, ib)) : {Bool.and(Nat.is_eq(la, lb), Cmp.is_eq(_)) == S.same(ONode.Node{la, ia}, ONode.Node{lb, ib}) : Bool}
      {==}

def oq.has(xs: List<&2, ONode.Node>, +x: ONode.Node) -> {ONode.Nodes.has(xs, x) == S.member(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, ONode.Node.eq(h, x), S.same(h, x), oq.eq(h, x)) : {Bool.or(_, ONode.Nodes.has(t, x)) == S.member(h <> t, x) : Bool}
      %Equal.sym(Bool, ONode.Nodes.has(t, x), S.member(t, x), oq.has(t, x)) : {Bool.or(S.same(h, x), _) == S.member(h <> t, x) : Bool}
      {==}

# The work queue
# --------------

# with at least jobs unbuilt lines seen, no line of the view starts
def oq.lines_nil(v: List<&2, ONode.Node>, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +u: Nat, +e: {Nat.is_ge(u, jobs) == True{} : Bool}) -> {S.queue.lines(info, busy, jobs, v, u) == Nil{} : List<&2, ONode.Node>}:
  match v:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, Nat.is_ge(u, jobs), True{}, e) : {S.keep(Bool.and(Bool.not(_), Bool.and(Bool.not(OInfo.Info.built(info, h)), Bool.not(S.member(busy, h)))), h, S.queue.lines(info, busy, jobs, t, Nat.add(u, S.unbuilt(OInfo.Info.built(info, h))))) == Nil{} : List<&2, ONode.Node>}
      oq.lines_nil(t, info, busy, jobs, Nat.add(u, S.unbuilt(OInfo.Info.built(info, h))), oq.ge_add(u, jobs, S.unbuilt(OInfo.Info.built(info, h)), e))

def oq.view_at(g: Bool, b: Bool, f: Bool, +h: ONode.Node, +t: List<&2, ONode.Node>, +r: Nat, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +u: Nat,
  eg: {Nat.is_ge(u, jobs) == g : Bool},
  ib: {OQueue.cand.view(t, info, busy, jobs, Nat.add(u, 0n), 1n+r) == S.take(1n+r, S.queue.lines(info, busy, jobs, t, Nat.add(u, 0n))) : List<&2, ONode.Node>},
  ifr: {OQueue.cand.view(t, info, busy, jobs, Nat.add(u, 1n), Nat.sub(r, 0n)) == S.take(Nat.sub(r, 0n), S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n))) : List<&2, ONode.Node>},
  inb: {OQueue.cand.view(t, info, busy, jobs, Nat.add(u, 1n), 1n+r) == S.take(1n+r, S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n))) : List<&2, ONode.Node>})
  -> {OQueue.cand.emit(g, b, f, h, OQueue.cand.view(t, info, busy, jobs, Nat.add(u, OBits.bit(Bool.not(b), 0n)), Nat.sub(1n+r, OBits.bit(Bool.and(Bool.not(b), f), 0n)))) == S.take(1n+r, S.keep(Bool.and(Bool.not(g), Bool.and(Bool.not(b), f)), h, S.queue.lines(info, busy, jobs, t, Nat.add(u, S.unbuilt(b))))) : List<&2, ONode.Node>}:
  match g b f:
    case True{} True{} True{}:
      %Equal.sym(List<&2, ONode.Node>, S.queue.lines(info, busy, jobs, t, Nat.add(u, 0n)), Nil{}, oq.lines_nil(t, info, busy, jobs, Nat.add(u, 0n), oq.ge_add(u, jobs, 0n, eg))) : {Nil{} == S.take(1n+r, _) : List<&2, ONode.Node>}
      {==}
    case True{} True{} False{}:
      %Equal.sym(List<&2, ONode.Node>, S.queue.lines(info, busy, jobs, t, Nat.add(u, 0n)), Nil{}, oq.lines_nil(t, info, busy, jobs, Nat.add(u, 0n), oq.ge_add(u, jobs, 0n, eg))) : {Nil{} == S.take(1n+r, _) : List<&2, ONode.Node>}
      {==}
    case True{} False{} True{}:
      %Equal.sym(List<&2, ONode.Node>, S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n)), Nil{}, oq.lines_nil(t, info, busy, jobs, Nat.add(u, 1n), oq.ge_add(u, jobs, 1n, eg))) : {Nil{} == S.take(1n+r, _) : List<&2, ONode.Node>}
      {==}
    case True{} False{} False{}:
      %Equal.sym(List<&2, ONode.Node>, S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n)), Nil{}, oq.lines_nil(t, info, busy, jobs, Nat.add(u, 1n), oq.ge_add(u, jobs, 1n, eg))) : {Nil{} == S.take(1n+r, _) : List<&2, ONode.Node>}
      {==}
    case False{} True{} True{}:
      ib
    case False{} True{} False{}:
      ib
    case False{} False{} True{}:
      %oq.sub0(r) : {h <> OQueue.cand.view(t, info, busy, jobs, Nat.add(u, 1n), Nat.sub(r, 0n)) == h <> S.take(_, S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n))) : List<&2, ONode.Node>}
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, x => h <> x, OQueue.cand.view(t, info, busy, jobs, Nat.add(u, 1n), Nat.sub(r, 0n)), S.take(Nat.sub(r, 0n), S.queue.lines(info, busy, jobs, t, Nat.add(u, 1n))), ifr)
    case False{} False{} False{}:
      inb

# the view's lines that start: the spec's, within the room
def oq.view(v: List<&2, ONode.Node>, room: Nat, +info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, +u: Nat) -> {OQueue.cand.view(v, info, busy, jobs, u, room) == S.take(room, S.queue.lines(info, busy, jobs, v, u)) : List<&2, ONode.Node>}:
  match v room:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+r:
      {==}
    case h <> t 0n:
      {==}
    case +h <> +t 1n++r:
      %oq.has(busy, h) : {OQueue.cand.view(h <> t, info, busy, jobs, u, 1n+r) == S.take(1n+r, S.keep(Bool.and(Bool.not(Nat.is_ge(u, jobs)), Bool.and(Bool.not(OInfo.Info.built(info, h)), Bool.not(_))), h, S.queue.lines(info, busy, jobs, t, Nat.add(u, S.unbuilt(OInfo.Info.built(info, h)))))) : List<&2, ONode.Node>}
      oq.view_at(Nat.is_ge(u, jobs), OInfo.Info.built(info, h), Bool.not(ONode.Nodes.has(busy, h)), h, t, r, info, busy, jobs, u, {==}, oq.view(t, 1n+r, info, busy, jobs, Nat.add(u, 0n)), oq.view(t, Nat.sub(r, 0n), info, busy, jobs, Nat.add(u, 1n)), oq.view(t, 1n+r, info, busy, jobs, Nat.add(u, 1n)))

def oq.ready_at(f: Bool, +h: ONode.Node, +t: List<&2, ONode.Node>, +r: Nat, +busy: List<&2, ONode.Node>,
  i1: {OQueue.cand.ready(t, busy, Nat.sub(r, 0n)) == S.take(Nat.sub(r, 0n), S.queue.ready(busy, t)) : List<&2, ONode.Node>},
  i0: {OQueue.cand.ready(t, busy, 1n+r) == S.take(1n+r, S.queue.ready(busy, t)) : List<&2, ONode.Node>})
  -> {ONode.Nodes.keep(f, h, OQueue.cand.ready(t, busy, Nat.sub(1n+r, OBits.bit(f, 0n)))) == S.take(1n+r, S.keep(f, h, S.queue.ready(busy, t))) : List<&2, ONode.Node>}:
  match f:
    case True{}:
      %oq.sub0(r) : {h <> OQueue.cand.ready(t, busy, Nat.sub(r, 0n)) == h <> S.take(_, S.queue.ready(busy, t)) : List<&2, ONode.Node>}
      Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, x => h <> x, OQueue.cand.ready(t, busy, Nat.sub(r, 0n)), S.take(Nat.sub(r, 0n), S.queue.ready(busy, t)), i1)
    case False{}:
      i0

# the ready merges that start: the spec's, within the room
def oq.ready(rs: List<&2, ONode.Node>, room: Nat, +busy: List<&2, ONode.Node>) -> {OQueue.cand.ready(rs, busy, room) == S.take(room, S.queue.ready(busy, rs)) : List<&2, ONode.Node>}:
  match rs room:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+r:
      {==}
    case h <> t 0n:
      {==}
    case +h <> +t 1n++r:
      %oq.has(busy, h) : {OQueue.cand.ready(h <> t, busy, 1n+r) == S.take(1n+r, S.keep(Bool.not(_), h, S.queue.ready(busy, t))) : List<&2, ONode.Node>}
      oq.ready_at(Bool.not(ONode.Nodes.has(busy, h)), h, t, r, busy, oq.ready(t, Nat.sub(r, 0n), busy), oq.ready(t, 1n+r, busy))

# the first n of xs, then the first of ys that are left: the first n of
# both
def oq.take_app(n: Nat, xs: List<&2, ONode.Node>, +ys: List<&2, ONode.Node>) -> {List.append(&2, ONode.Node, S.take(n, xs), S.take(Nat.sub(n, List.length(&2, ONode.Node, S.take(n, xs))), ys)) == S.take(n, List.append(&2, ONode.Node, xs, ys)) : List<&2, ONode.Node>}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      match xs:
        case Nil{}:
          {==}
        case +x <> +t:
          Equal.cong(List<&2, ONode.Node>, List<&2, ONode.Node>, z => x <> z, List.append(&2, ONode.Node, S.take(k, t), S.take(Nat.sub(k, List.length(&2, ONode.Node, S.take(k, t))), ys)), S.take(k, List.append(&2, ONode.Node, t, ys)), oq.take_app(k, t, ys))

# A compaction's view
# -------------------

# a line's end, in bits, is worth the spec's (i+1)·2^l
def oq.val_end(+l: Nat, +i: List<&2, Bool>) -> {OBits.Bits.val(OBits.Bits.shl(l, OBits.Bits.inc(i))) == S.sh(l, 1n+OBits.Bits.val(i)) : Nat}:
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.shl(l, OBits.Bits.inc(i))), LLLogic.pa.sh(l, OBits.Bits.val(OBits.Bits.inc(i))), LLOptchat.pa.val_shl(l, OBits.Bits.inc(i))) : {_ == S.sh(l, 1n+OBits.Bits.val(i)) : Nat}
  %Equal.sym(Nat, OBits.Bits.val(OBits.Bits.inc(i)), 1n+OBits.Bits.val(i), LLOptchat.pa.val_inc(i)) : {LLLogic.pa.sh(l, _) == S.sh(l, 1n+OBits.Bits.val(i)) : Nat}
  oq.sh(l, 1n+OBits.Bits.val(i))

def oq.end(n: ONode.Node) -> {OBits.Bits.val(OCtx.Node.end_bits(n)) == S.line_end(n) : Nat}:
  match n:
    case ONode.Node{+l, +i}:
      oq.val_end(l, i)

def oq.bound(n: ONode.Node) -> {OBits.Bits.val(OCtx.ctx.bound(n)) == S.ctx_bound(n) : Nat}:
  match n:
    case ONode.Node{l, +i}:
      match l:
        case 0n:
          {==}
        case 1n+p:
          oq.val_end(1n+p, i)

# a line ends by the bound, in bits, as in numbers
def oq.le(+h: ONode.Node, +bd: List<&2, Bool>) -> {OBits.Bits.le(OCtx.Node.end_bits(h), bd) == Nat.is_le(S.line_end(h), OBits.Bits.val(bd)) : Bool}:
  %Equal.sym(Cmp, OBits.Bits.cmp(OCtx.Node.end_bits(h), bd), Nat.cmp(OBits.Bits.val(OCtx.Node.end_bits(h)), OBits.Bits.val(bd)), LA.pa.cmp_val(OCtx.Node.end_bits(h), bd)) : {Cmp.is_le(_) == Nat.is_le(S.line_end(h), OBits.Bits.val(bd)) : Bool}
  %Equal.sym(Nat, OBits.Bits.val(OCtx.Node.end_bits(h)), S.line_end(h), oq.end(h)) : {Cmp.is_le(Nat.cmp(_, OBits.Bits.val(bd))) == Nat.is_le(S.line_end(h), OBits.Bits.val(bd)) : Bool}
  {==}

# The built nodes' sizes
# ----------------------

def oq.tg_tip(j: List<&2, Bool>) -> {OInfo.Trie.get(j, OInfo.Tip{}) == None{} : Maybe<&2, Nat>}:
  match j:
    case Nil{}:
      {==}
    case False{} <> r:
      {==}
    case True{} <> r:
      {==}

def oq.lg_nil(q: Nat, j: List<&2, Bool>) -> {OInfo.Lvls.get(q, Nil{}, j) == None{} : Maybe<&2, Nat>}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a trie, read after a set
def oq.tr(i: List<&2, Bool>, t: OInfo.Trie, j: List<&2, Bool>, +z: Nat) -> {OInfo.Trie.get(j, OInfo.Trie.set(i, t, z)) == S.info_pick(S.bits_same(i, j), z, OInfo.Trie.get(j, t)) : Maybe<&2, Nat>}:
  match i t:
    case Nil{} OInfo.Tip{}:
      match j:
        case Nil{}:
          {==}
        case False{} <> r:
          oq.tg_tip(r)
        case True{} <> r:
          oq.tg_tip(r)
    case Nil{} OInfo.Bin{v, lo, hi}:
      match j:
        case Nil{}:
          {==}
        case False{} <> r:
          {==}
        case True{} <> r:
          {==}
    case False{} <> +r OInfo.Tip{}:
      match j:
        case Nil{}:
          {==}
        case False{} <> +q:
          %oq.tg_tip(q) : {OInfo.Trie.get(q, OInfo.Trie.set(r, OInfo.Tip{}, z)) == S.info_pick(S.bits_same(r, q), z, _) : Maybe<&2, Nat>}
          oq.tr(r, OInfo.Tip{}, q, z)
        case True{} <> q:
          oq.tg_tip(q)
    case True{} <> +r OInfo.Tip{}:
      match j:
        case Nil{}:
          {==}
        case False{} <> q:
          oq.tg_tip(q)
        case True{} <> +q:
          %oq.tg_tip(q) : {OInfo.Trie.get(q, OInfo.Trie.set(r, OInfo.Tip{}, z)) == S.info_pick(S.bits_same(r, q), z, _) : Maybe<&2, Nat>}
          oq.tr(r, OInfo.Tip{}, q, z)
    case False{} <> r OInfo.Bin{v, lo, hi}:
      match j:
        case Nil{}:
          {==}
        case False{} <> q:
          oq.tr(r, lo, q, z)
        case True{} <> q:
          {==}
    case True{} <> r OInfo.Bin{v, lo, hi}:
      match j:
        case Nil{}:
          {==}
        case False{} <> q:
          {==}
        case True{} <> q:
          oq.tr(r, hi, q, z)

# the levels, read after a set
def oq.lv(l: Nat, ts: List<&2, OInfo.Trie>, k: Nat, +i: List<&2, Bool>, +j: List<&2, Bool>, +z: Nat) -> {OInfo.Lvls.get(k, OInfo.Lvls.set(l, ts, i, z), j) == S.info_pick(Bool.and(Nat.is_eq(l, k), S.bits_same(i, j)), z, OInfo.Lvls.get(k, ts, j)) : Maybe<&2, Nat>}:
  match l:
    case 0n:
      match ts:
        case Nil{}:
          match k:
            case 0n:
              %oq.tg_tip(j) : {OInfo.Trie.get(j, OInfo.Trie.set(i, OInfo.Tip{}, z)) == S.info_pick(S.bits_same(i, j), z, _) : Maybe<&2, Nat>}
              oq.tr(i, OInfo.Tip{}, j, z)
            case 1n++q:
              Equal.trans(Maybe<&2, Nat>, OInfo.Lvls.get(q, Nil{}, j), None{}, OInfo.Lvls.get(1n+q, Nil{}, j), oq.lg_nil(q, j), Equal.sym(Maybe<&2, Nat>, OInfo.Lvls.get(1n+q, Nil{}, j), None{}, oq.lg_nil(1n+q, j)))
        case +h <> t:
          match k:
            case 0n:
              oq.tr(i, h, j, z)
            case 1n+q:
              {==}
    case 1n+p:
      match ts:
        case Nil{}:
          match k:
            case 0n:
              oq.tg_tip(j)
            case 1n++q:
              %oq.lg_nil(q, j) : {OInfo.Lvls.get(q, OInfo.Lvls.set(p, Nil{}, i, z), j) == S.info_pick(Bool.and(Nat.is_eq(p, q), S.bits_same(i, j)), z, _) : Maybe<&2, Nat>}
              oq.lv(p, Nil{}, q, i, j, z)
        case h <> t:
          match k:
            case 0n:
              {==}
            case 1n+q:
              oq.lv(p, t, q, i, j, z)
