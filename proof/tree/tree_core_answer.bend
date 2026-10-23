# eukhe: the proof of LAW tree_core_answer

import Base
import ../../bend/tree.bend as Tr
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# the keys a delete cuts are the keys it removes

def tc.lost_at_cong(c: Bool, +k: Nat, +X: List<&2, Nat>, +Y: List<&2, Nat>, +e: {X == Y : List<&2, Nat>}) -> {Laws.tree.lost.at(c, k, X) == Laws.tree.lost.at(c, k, Y) : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => Laws.tree.lost.at(c, k, ys), X, Y, e)

# a node below every key of r does not change what r loses
def tc.lost_skip(r: List<&2, Tr.Ent>, +e: Tr.Ent, +P: List<&2, Tr.Ent>, +ar: {Tr.above(Tr.Ent.k(e), r) == True{} : Bool}, +sr: {Tr.sorted(r) == True{} : Bool}) -> {Laws.tree.lost(r, e <> P) == Laws.tree.lost(r, P) : List<&2, Nat>}:
  match r:
    case Nil{}:
      {==}
    case +f <> +r2:
      +ne = L.pt.lt_ne(Tr.Ent.k(e), Tr.Ent.k(f), ar)
      +ar2 = LA.pt.above_lt(Tr.Ent.k(e), Tr.Ent.k(f), r2, ar, L.tree.pt.and_l(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr))
      +sr2 = L.tree.pt.and_r(Tr.above(Tr.Ent.k(f), r2), Tr.sorted(r2), sr)
      +ih = tc.lost_skip(r2, e, P, ar2, sr2)
      %Equal.sym(Bool, Tr.has(e <> P, Tr.Ent.k(f)), Tr.has(P, Tr.Ent.k(f)), LA.pt.has_miss(e, P, Tr.Ent.k(f), ne)) : {Laws.tree.lost.at(_, Tr.Ent.k(f), Laws.tree.lost(r2, e <> P)) == Laws.tree.lost.at(Tr.has(P, Tr.Ent.k(f)), Tr.Ent.k(f), Laws.tree.lost(r2, P)) : List<&2, Nat>}
      tc.lost_at_cong(Tr.has(P, Tr.Ent.k(f)), Tr.Ent.k(f), Laws.tree.lost(r2, e <> P), Laws.tree.lost(r2, P), ih)

def tc.lost_drops(t: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool, +st: {Tr.sorted(t) == True{} : Bool}) -> {Laws.tree.lost(t, Tr.prune.go(t, gone, hit)) == LA.tc.dgo(t, gone, hit) : List<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      match hit:
        case True{}:
          +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +g2 = {Tr.Ent.k(e) <> gone : List<&2, Nat>}
          +Q = Tr.prune.go(r, g2, Tr.gone.at(r, g2))
          +aq = LA.pt.above_prune_go(r, g2, Tr.gone.at(r, g2), Tr.Ent.k(e), ar, sr)
          +sq = LA.pt.sorted_prune_go(r, g2, Tr.gone.at(r, g2), sr)
          +nh = LA.pt.has_below(Q, Tr.Ent.k(e), aq, sq)
          %Equal.sym(Bool, Tr.has(Q, Tr.Ent.k(e)), False{}, nh) : {Laws.tree.lost.at(_, Tr.Ent.k(e), Laws.tree.lost(r, Q)) == Tr.Ent.k(e) <> LA.tc.dgo(r, g2, Tr.gone.at(r, g2)) : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => Tr.Ent.k(e) <> ys, Laws.tree.lost(r, Q), LA.tc.dgo(r, g2, Tr.gone.at(r, g2)), tc.lost_drops(r, g2, Tr.gone.at(r, g2), sr))
        case False{}:
          +ar = L.tree.pt.and_l(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +sr = L.tree.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), st)
          +Q = Tr.prune.go(r, gone, Tr.gone.at(r, gone))
          %Equal.sym(Bool, Tr.has(e <> Q, Tr.Ent.k(e)), True{}, LA.pt.has_head(e, Q)) : {Laws.tree.lost.at(_, Tr.Ent.k(e), Laws.tree.lost(r, e <> Q)) == LA.tc.dgo(r, gone, Tr.gone.at(r, gone)) : List<&2, Nat>}
          Equal.trans(List<&2, Nat>, Laws.tree.lost(r, e <> Q), Laws.tree.lost(r, Q), LA.tc.dgo(r, gone, Tr.gone.at(r, gone)), tc.lost_skip(r, e, Q, ar, sr), tc.lost_drops(r, gone, Tr.gone.at(r, gone), sr))

def tc.put_case_ans(b: Bool, +m: Tr.KMap, +hs: List<&2, Nat>, +e: Tr.Ent) -> {Pair.snd(Tr.KMap, Tr.Ans, Tr.put.ans(b, m, hs, e)) == Laws.tree.took(b) : Tr.Ans}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.keep_case_ans(b: Bool, +m: Tr.KMap, +n: Tr.KMap) -> {Pair.snd(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n)) == Laws.tree.took(b) : Tr.Ans}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.rec_ans(+m: Tr.KMap, +hs: List<&2, Nat>, r: Tr.Rec, +bt: {L.tc.bst(m) == True{} : Bool}, +mk: {LA.tc.mpok(m) == True{} : Bool}, +sd: {Tr.sound(Tr.KMap.read(m)) == True{} : Bool}) -> {Pair.snd(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r)) == Laws.tree.answer(Tr.KMap.read(m), r) : Tr.Ans}:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, +v}:
          +e = {Tr.Ent{k, p, v} : Tr.Ent}
          +G = Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.KMap.has(m, p)))
          %Equal.sym(Bool, G, Tr.ok(Tr.KMap.read(m), k, p), LA.tc.good_put(m, k, p, bt)) : {Pair.snd(Tr.KMap, Tr.Ans, Tr.put.ans(_, m, hs, e)) == Laws.tree.took(Tr.ok(Tr.KMap.read(m), k, p)) : Tr.Ans}
          tc.put_case_ans(Tr.ok(Tr.KMap.read(m), k, p), m, hs, e)
        case Tr.Del{x}:
          match x:
            case 0n:
              {==}
            case 1n++y:
              +t = Tr.KMap.read(m)
              +F = Tr.KMap.ups(m, 1n+y, Nil{}, Tr.KMap.gl(m, 1n+y), Tr.KMap.gr(m, 1n+y))
              +KS = Tr.drops(F, hs, 1n+y)
              +D = LA.tc.dgo(t, [1n+y], Tr.gone.at(t, [1n+y]))
              +s1 = Equal.trans(List<&2, Nat>, KS, LA.tc.dgo(F, [1n+y], Tr.gone.at(F, [1n+y])), D, LA.tc.drops(F, hs, 1n+y), LA.tc.del_keys(m, 1n+y, bt, mk, sd))
              +s2 = Equal.sym(List<&2, Nat>, Laws.tree.lost(t, Tr.prune(t, 1n+y)), D, tc.lost_drops(t, [1n+y], Tr.gone.at(t, [1n+y]), LA.tc.sorted_read(m, bt)))
              Equal.cong(List<&2, Nat>, Tr.Ans, z => Tr.Cut{z}, KS, Laws.tree.lost(t, Tr.prune(t, 1n+y)), Equal.trans(List<&2, Nat>, KS, D, Laws.tree.lost(t, Tr.prune(t, 1n+y)), s1, s2))
    case Tr.Rewind{+ops}:
      +n = Tr.KMap.patch(ops, hs, m)
      +G = Tr.KMap.hangs(Tr.KMap.onto(n, Nil{}), n)
      +N = Tr.patch(ops, Tr.KMap.read(m))
      %Equal.sym(Bool, G, Tr.sound(N), LA.tc.good_rewind(ops, hs, m, bt)) : {Pair.snd(Tr.KMap, Tr.Ans, Tr.keep.ans(_, m, n)) == Laws.tree.took(Tr.sound(N)) : Tr.Ans}
      tc.keep_case_ans(Tr.sound(N), m, n)

def tc.go_mpok(rs: List<&2, Tr.Rec>, +hs: List<&2, Nat>, +m: Tr.KMap, +mk: {LA.tc.mpok(m) == True{} : Bool}) -> {LA.tc.mpok(Tr.KMap.go(rs, hs, m)) == True{} : Bool}:
  match rs:
    case Nil{}:
      mk
    case +r <> rest:
      tc.go_mpok(rest, hs, Pair.fst(Tr.KMap, Tr.Ans, Tr.KMap.rec(m, hs, r)), LA.tc.rec_mpok(m, hs, r, mk))

def tc.note_snd(+log: List<&2, Tr.Rec>, +r: Tr.Rec, +hs: List<&2, Nat>, p: Tr.KMap & Tr.Ans) -> {Pair.snd(Tr.St, Tr.Ans, Tr.St.note(log, r, hs, p)) == Pair.snd(Tr.KMap, Tr.Ans, p) : Tr.Ans}:
  match p:
    case Tuple{a, b}:
      {==}

def tc.live_mpok(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {LA.tc.mpok(Tr.KMap.go(rs, hs, Tr.KNil{})) == True{} : Bool}:
  tc.go_mpok(rs, hs, Tr.KNil{}, {==})

def tc.live_sound(+hs: List<&2, Nat>, +rs: List<&2, Tr.Rec>) -> {Tr.sound(Tr.KMap.read(Tr.KMap.go(rs, hs, Tr.KNil{}))) == True{} : Bool}:
  %Equal.sym(List<&2, Tr.Ent>, Tr.KMap.read(Tr.KMap.go(rs, hs, Tr.KNil{})), Tr.replay(rs), LA.tc.live_read(hs, rs)) : {Tr.sound(_) == True{} : Bool}
  LA.replay_sound(rs)

def Laws.tree_core_answer(hs, rs, r):
  +M = Tr.KMap.go(rs, hs, Tr.KNil{})
  +L = List.reverse.go(&2, Tr.Rec, rs, Nil{})
  +R = Tr.replay(rs)
  %Equal.sym(Tr.St, Tr.core.feed(hs, rs), Tr.St{M, L, hs}, LA.tc.feed(hs, rs)) : {Pair.snd(Tr.St, Tr.Ans, Tr.core.step(_, Tr.Note{r})) == Laws.tree.answer(R, r) : Tr.Ans}
  +s1 = tc.note_snd(L, r, hs, Tr.KMap.rec(M, hs, r))
  +s2 = tc.rec_ans(M, hs, r, LA.tc.live_bst(hs, rs), tc.live_mpok(hs, rs), tc.live_sound(hs, rs))
  +s3 = Equal.cong(List<&2, Tr.Ent>, Tr.Ans, z => Laws.tree.answer(z, r), Tr.KMap.read(M), R, LA.tc.live_read(hs, rs))
  Equal.trans(Tr.Ans, Pair.snd(Tr.St, Tr.Ans, Tr.St.note(L, r, hs, Tr.KMap.rec(M, hs, r))), Pair.snd(Tr.KMap, Tr.Ans, Tr.KMap.rec(M, hs, r)), Laws.tree.answer(R, r), s1, Equal.trans(Tr.Ans, Pair.snd(Tr.KMap, Tr.Ans, Tr.KMap.rec(M, hs, r)), Laws.tree.answer(Tr.KMap.read(M), r), Laws.tree.answer(R, r), s2, s3))
