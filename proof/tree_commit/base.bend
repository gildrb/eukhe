# eukhe: lemmas of the proofs of area tree_commit (the model)
#
# The code's rounds (bend/tree_commit.bend: a mark per change, walked in
# place) against the spec's (laws/tree_commit.bend: the waiting Puts'
# indices, looked up in the commit): tc.T lists the indices of the
# unmarked Puts; one round of the code answers what one pass of the spec
# answers over them (tc.R); the rounds then agree (tc.CR).

import Base
import ../../bend/tree_commit.bend as Tc
import ../../laws/tree_commit.bend as TreeCommit

# ---- logic ----

def tc.LI(xs: List<&2, Tc.Ch>, G: Type) -> Type:
  match xs:
    case Nil{}:
      Unit
    case c <> t:
      G

# the empty list is no list with a head
def tc.nil_cons(-G: Type, -c: Tc.Ch, -t: List<&2, Tc.Ch>, e: {Nil{} == c <> t : List<&2, Tc.Ch>}) -> G:
  %e : tc.LI(_, G)
  Unit{}

def tc.BD(b: Bool, T: Type, F: Type) -> Type:
  match b:
    case True{}:
      T
    case False{}:
      F

def tc.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tc.BD(_, G, Unit)
  Unit{}

# ---- lists ----

def tc.app_assoc(xs: List<&2, Tc.Res>, -ys: List<&2, Tc.Res>, -zs: List<&2, Tc.Res>) -> {List.append(&2, Tc.Res, List.append(&2, Tc.Res, xs, ys), zs) == List.append(&2, Tc.Res, xs, List.append(&2, Tc.Res, ys, zs)) : List<&2, Tc.Res>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, Tc.Res>, List<&2, Tc.Res>, l => x <> l, List.append(&2, Tc.Res, List.append(&2, Tc.Res, t, ys), zs), List.append(&2, Tc.Res, t, List.append(&2, Tc.Res, ys, zs)), tc.app_assoc(t, ys, zs))

# the changes of cs from index i
def tc.drop(+i: Nat, cs: List<&2, Tc.Ch>) -> List<&2, Tc.Ch>:
  match i:
    case 0n:
      cs
    case 1n+j:
      match cs:
        case Nil{}:
          []
        case c <> t:
          tc.drop(j, t)

# the change at i is the head of the changes from i
def tc.at_drop(+i: Nat, cs: List<&2, Tc.Ch>, +c: Tc.Ch, +t: List<&2, Tc.Ch>, h: {tc.drop(i, cs) == c <> t : List<&2, Tc.Ch>}) -> {TreeCommit.at(cs, i) == c : Tc.Ch}:
  match i:
    case 0n:
      %Equal.sym(List<&2, Tc.Ch>, cs, c <> t, h) : {TreeCommit.at(_, 0n) == c : Tc.Ch}
      {==}
    case 1n+j:
      match cs:
        case Nil{}:
          tc.nil_cons({TreeCommit.at([], 1n+j) == c : Tc.Ch}, c, t, h)
        case c0 <> t0:
          tc.at_drop(j, t0, c, t, h)

# the changes from i + 1 are the tail of the changes from i
def tc.drop_next(+i: Nat, cs: List<&2, Tc.Ch>, +c: Tc.Ch, +t: List<&2, Tc.Ch>, h: {tc.drop(i, cs) == c <> t : List<&2, Tc.Ch>}) -> {tc.drop(1n+i, cs) == t : List<&2, Tc.Ch>}:
  match i:
    case 0n:
      %Equal.sym(List<&2, Tc.Ch>, cs, c <> t, h) : {tc.drop(1n, _) == t : List<&2, Tc.Ch>}
      {==}
    case 1n+j:
      match cs:
        case Nil{}:
          tc.nil_cons({tc.drop(2n+j, []) == t : List<&2, Tc.Ch>}, c, t, h)
        case c0 <> t0:
          tc.drop_next(j, t0, c, t, h)

# ---- the waiting Puts of the code's marks ----

def tc.T.mark(m: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case True{}:
      rest
    case False{}:
      i <> rest

def tc.T.one(c: Tc.Ch, m: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case Tc.Here{k}:
      tc.T.mark(m, i, rest)
    case Tc.Under{k, u}:
      tc.T.mark(m, i, rest)
    case Tc.Gone{}:
      rest

# the indices of the Puts of cs (the first at index i) not marked in ms
def tc.T(cs: List<&2, Tc.Ch>, ms: List<&2, Bool>, +i: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case c <> t:
      match ms:
        case Nil{}:
          tc.T.one(c, False{}, i, tc.T(t, [], 1n+i))
        case m <> u:
          tc.T.one(c, m, i, tc.T(t, u, 1n+i))

# with no mark, the waiting Puts are all the Puts
def tc.T_none(cs: List<&2, Tc.Ch>, +i: Nat) -> {tc.T(cs, [], i) == TreeCommit.put_indices(cs, i) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Tc.Here{k}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, l => i <> l, tc.T(t, [], 1n+i), TreeCommit.put_indices(t, 1n+i), tc.T_none(t, 1n+i))
        case Tc.Under{k, u}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, l => i <> l, tc.T(t, [], 1n+i), TreeCommit.put_indices(t, 1n+i), tc.T_none(t, 1n+i))
        case Tc.Gone{}:
          tc.T_none(t, 1n+i)

# the code's unknown parents are the spec's, of the waiting Puts
def tc.orph_one(c: Tc.Ch, m: Bool, +i: Nat, -rest: List<&2, Tc.Res>, -w: List<&2, Nat>, e: {rest == TreeCommit.unknowns(w) : List<&2, Tc.Res>}) -> {Tc.orphans.one(c, m, i, rest) == TreeCommit.unknowns(tc.T.one(c, m, i, w)) : List<&2, Tc.Res>}:
  match c:
    case Tc.Here{k}:
      match m:
        case True{}:
          e
        case False{}:
          Equal.cong(List<&2, Tc.Res>, List<&2, Tc.Res>, l => Tc.Orphan{i} <> l, rest, TreeCommit.unknowns(w), e)
    case Tc.Under{k, u}:
      match m:
        case True{}:
          e
        case False{}:
          Equal.cong(List<&2, Tc.Res>, List<&2, Tc.Res>, l => Tc.Orphan{i} <> l, rest, TreeCommit.unknowns(w), e)
    case Tc.Gone{}:
      e

def tc.orph(cs: List<&2, Tc.Ch>, ms: List<&2, Bool>, +i: Nat) -> {Tc.orphans(cs, ms, i) == TreeCommit.unknowns(tc.T(cs, ms, i)) : List<&2, Tc.Res>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match ms:
        case Nil{}:
          tc.orph_one(c, False{}, i, Tc.orphans(t, [], 1n+i), tc.T(t, [], 1n+i), tc.orph(t, [], 1n+i))
        case m <> u:
          tc.orph_one(c, m, i, Tc.orphans(t, u, 1n+i), tc.T(t, u, 1n+i), tc.orph(t, u, 1n+i))

# the code's Dels are the spec's
def tc.ret(cs: List<&2, Tc.Ch>, +i: Nat) -> {Tc.retires(cs, i) == TreeCommit.dels_spec(cs, i) : List<&2, Tc.Res>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Tc.Here{k}:
          tc.ret(t, 1n+i)
        case Tc.Under{k, u}:
          tc.ret(t, 1n+i)
        case Tc.Gone{}:
          Equal.cong(List<&2, Tc.Res>, List<&2, Tc.Res>, l => Tc.Retire{i} <> l, Tc.retires(t, 1n+i), TreeCommit.dels_spec(t, 1n+i), tc.ret(t, 1n+i))

# ---- one change ----

def tc.has(xs: List<&2, Nat>, +u: Nat) -> {Tc.has(xs, u) == TreeCommit.member(xs, u) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, u), z), Tc.has(t, u), TreeCommit.member(t, u), tc.has(t, u))

def tc.grow(b: Bool, -k: Nat, -ready: List<&2, Nat>) -> {Tc.grow(b, k, ready) == TreeCommit.add_if(b, k, ready) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's step at a change c is the code's
def tc.Q2(c: Tc.Ch, +ready: List<&2, Nat>, -i: Nat, -rest: List<&2, Nat>, -cs: List<&2, Tc.Ch>) -> {TreeCommit.pass.cons(TreeCommit.parent_in(ready, c), i, TreeCommit.pass(rest, cs, TreeCommit.add_if(TreeCommit.parent_in(ready, c), TreeCommit.key_of(c), ready))) == TreeCommit.pass.cons(Tc.free(ready, c), i, TreeCommit.pass(rest, cs, Tc.grow(Tc.free(ready, c), Tc.key(c), ready))) : TreeCommit.Pass}:
  match c:
    case Tc.Here{k}:
      {==}
    case Tc.Under{+k, +u}:
      %tc.has(ready, u) : {TreeCommit.pass.cons(_, i, TreeCommit.pass(rest, cs, TreeCommit.add_if(_, k, ready))) == TreeCommit.pass.cons(Tc.has(ready, u), i, TreeCommit.pass(rest, cs, Tc.grow(Tc.has(ready, u), k, ready))) : TreeCommit.Pass}
      %tc.grow(Tc.has(ready, u), k, ready) : {TreeCommit.pass.cons(Tc.has(ready, u), i, TreeCommit.pass(rest, cs, _)) == TreeCommit.pass.cons(Tc.has(ready, u), i, TreeCommit.pass(rest, cs, Tc.grow(Tc.has(ready, u), k, ready))) : TreeCommit.Pass}
      {==}
    case Tc.Gone{}:
      {==}

# the spec's pass at the change c of index i
def tc.Q(+ready: List<&2, Nat>, +cs: List<&2, Tc.Ch>, +i: Nat, +c: Tc.Ch, +rest: List<&2, Nat>, h: {TreeCommit.at(cs, i) == c : Tc.Ch}) -> {TreeCommit.pass(i <> rest, cs, ready) == TreeCommit.pass.cons(Tc.free(ready, c), i, TreeCommit.pass(rest, cs, Tc.grow(Tc.free(ready, c), Tc.key(c), ready))) : TreeCommit.Pass}:
  %Equal.sym(Tc.Ch, TreeCommit.at(cs, i), c, h) : {TreeCommit.pass.cons(TreeCommit.parent_in(ready, _), i, TreeCommit.pass(rest, cs, TreeCommit.add_if(TreeCommit.parent_in(ready, _), TreeCommit.key_of(_), ready))) == TreeCommit.pass.cons(Tc.free(ready, c), i, TreeCommit.pass(rest, cs, Tc.grow(Tc.free(ready, c), Tc.key(c), ready))) : TreeCommit.Pass}
  tc.Q2(c, ready, i, rest, cs)

# ---- one round ----

# what a code round answers: its results, its waiting Puts, the keys
# present, whether it applied one
def tc.view(r: Tc.Round, cs: List<&2, Tc.Ch>, +i: Nat) -> List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)):
  match r:
    case Tc.Round{out, ms, rd, hit}:
      (out, (tc.T(cs, ms, i), (rd, hit)))

def tc.nonnil(a: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case x <> t:
      True{}

# what a spec pass answers, in the same shape
def tc.sview(p: TreeCommit.Pass) -> List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)):
  match p:
    case TreeCommit.Pass{+a, w, rd}:
      (TreeCommit.applies(a), (w, (rd, tc.nonnil(a))))

def tc.bump_t(+i: Nat, v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)):
  match v:
    case (x, y):
      match y:
        case (z, q):
          match q:
            case (r, h):
              (Tc.Apply{i} <> x, (z, (r, True{})))

def tc.bump_f(+i: Nat, v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)):
  match v:
    case (x, y):
      match y:
        case (z, q):
          match q:
            case (r, h):
              (x, (i <> z, (r, h)))

def tc.is_put(c: Tc.Ch) -> Bool:
  match c:
    case Tc.Here{k}:
      True{}
    case Tc.Under{k, u}:
      True{}
    case Tc.Gone{}:
      False{}

# a change whose Put was marked (m) or a Del keeps the round's answer
def tc.keep(c: Tc.Ch, m: Bool, +i: Nat, -t: List<&2, Tc.Ch>, r: Tc.Round, k: {Bool.or(m, Bool.not(tc.is_put(c))) == True{} : Bool}) -> {tc.view(Tc.round.one(False{}, m, i, r), c <> t, i) == tc.view(r, t, 1n+i) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}:
  match c:
    case Tc.Here{x}:
      match m:
        case True{}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              {==}
        case False{}:
          tc.absurd({tc.view(Tc.round.one(False{}, False{}, i, r), Tc.Here{x} <> t, i) == tc.view(r, t, 1n+i) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, k)
    case Tc.Under{x, y}:
      match m:
        case True{}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              {==}
        case False{}:
          tc.absurd({tc.view(Tc.round.one(False{}, False{}, i, r), Tc.Under{x, y} <> t, i) == tc.view(r, t, 1n+i) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, k)
    case Tc.Gone{}:
      match r:
        case Tc.Round{out, ms, rd, hit}:
          {==}

# an unmarked Put: applied now or still waiting, as the spec's pass.cons
def tc.put(b: Bool, c: Tc.Ch, +i: Nat, -t: List<&2, Tc.Ch>, r: Tc.Round, p: TreeCommit.Pass, isput: {tc.is_put(c) == True{} : Bool}, e: {tc.view(r, t, 1n+i) == tc.sview(p) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}) -> {tc.view(Tc.round.one(b, False{}, i, r), c <> t, i) == tc.sview(TreeCommit.pass.cons(b, i, p)) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}:
  match b:
    case True{}:
      match c:
        case Tc.Here{x}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              match p:
                case TreeCommit.Pass{a, w, rd2}:
                  Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), v => tc.bump_t(i, v), tc.view(Tc.Round{out, ms, rd, hit}, t, 1n+i), tc.sview(TreeCommit.Pass{a, w, rd2}), e)
        case Tc.Under{x, y}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              match p:
                case TreeCommit.Pass{a, w, rd2}:
                  Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), v => tc.bump_t(i, v), tc.view(Tc.Round{out, ms, rd, hit}, t, 1n+i), tc.sview(TreeCommit.Pass{a, w, rd2}), e)
        case Tc.Gone{}:
          tc.absurd({tc.view(Tc.round.one(True{}, False{}, i, r), Tc.Gone{} <> t, i) == tc.sview(TreeCommit.pass.cons(True{}, i, p)) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, isput)
    case False{}:
      match c:
        case Tc.Here{x}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              match p:
                case TreeCommit.Pass{a, w, rd2}:
                  Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), v => tc.bump_f(i, v), tc.view(Tc.Round{out, ms, rd, hit}, t, 1n+i), tc.sview(TreeCommit.Pass{a, w, rd2}), e)
        case Tc.Under{x, y}:
          match r:
            case Tc.Round{out, ms, rd, hit}:
              match p:
                case TreeCommit.Pass{a, w, rd2}:
                  Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), v => tc.bump_f(i, v), tc.view(Tc.Round{out, ms, rd, hit}, t, 1n+i), tc.sview(TreeCommit.Pass{a, w, rd2}), e)
        case Tc.Gone{}:
          tc.absurd({tc.view(Tc.round.one(False{}, False{}, i, r), Tc.Gone{} <> t, i) == tc.sview(TreeCommit.pass.cons(False{}, i, p)) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, isput)

# a change after the round of the changes after it: kept (marked, or a
# Del), or an unmarked Put (tc.put, the spec's step at it: tc.Q)
def tc.Rc(m: Bool, c: Tc.Ch, +t: List<&2, Tc.Ch>, +u: List<&2, Bool>, +i: Nat, +ready: List<&2, Nat>, +cs: List<&2, Tc.Ch>, h: {tc.drop(i, cs) == c <> t : List<&2, Tc.Ch>}, ih: {tc.view(Tc.round(t, u, 1n+i, Tc.grow(Bool.and(Bool.not(m), Tc.free(ready, c)), Tc.key(c), ready)), t, 1n+i) == tc.sview(TreeCommit.pass(tc.T(t, u, 1n+i), cs, Tc.grow(Bool.and(Bool.not(m), Tc.free(ready, c)), Tc.key(c), ready))) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}) -> {tc.view(Tc.round.one(Bool.and(Bool.not(m), Tc.free(ready, c)), m, i, Tc.round(t, u, 1n+i, Tc.grow(Bool.and(Bool.not(m), Tc.free(ready, c)), Tc.key(c), ready))), c <> t, i) == tc.sview(TreeCommit.pass(tc.T.one(c, m, i, tc.T(t, u, 1n+i)), cs, ready)) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}:
  match m:
    case True{}:
      match c:
        case Tc.Here{x}:
          Equal.trans(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), tc.view(Tc.round.one(False{}, True{}, i, Tc.round(t, u, 1n+i, ready)), Tc.Here{x} <> t, i), tc.view(Tc.round(t, u, 1n+i, ready), t, 1n+i), tc.sview(TreeCommit.pass(tc.T(t, u, 1n+i), cs, ready)), tc.keep(Tc.Here{x}, True{}, i, t, Tc.round(t, u, 1n+i, ready), {==}), ih)
        case Tc.Under{x, y}:
          Equal.trans(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), tc.view(Tc.round.one(False{}, True{}, i, Tc.round(t, u, 1n+i, ready)), Tc.Under{x, y} <> t, i), tc.view(Tc.round(t, u, 1n+i, ready), t, 1n+i), tc.sview(TreeCommit.pass(tc.T(t, u, 1n+i), cs, ready)), tc.keep(Tc.Under{x, y}, True{}, i, t, Tc.round(t, u, 1n+i, ready), {==}), ih)
        case Tc.Gone{}:
          Equal.trans(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), tc.view(Tc.round.one(False{}, True{}, i, Tc.round(t, u, 1n+i, ready)), Tc.Gone{} <> t, i), tc.view(Tc.round(t, u, 1n+i, ready), t, 1n+i), tc.sview(TreeCommit.pass(tc.T(t, u, 1n+i), cs, ready)), tc.keep(Tc.Gone{}, True{}, i, t, Tc.round(t, u, 1n+i, ready), {==}), ih)
    case False{}:
      match c:
        case Tc.Here{+x}:
          %Equal.sym(TreeCommit.Pass, TreeCommit.pass(i <> tc.T(t, u, 1n+i), cs, ready), TreeCommit.pass.cons(Tc.free(ready, Tc.Here{x}), i, TreeCommit.pass(tc.T(t, u, 1n+i), cs, Tc.grow(Tc.free(ready, Tc.Here{x}), Tc.key(Tc.Here{x}), ready))), tc.Q(ready, cs, i, Tc.Here{x}, tc.T(t, u, 1n+i), tc.at_drop(i, cs, Tc.Here{x}, t, h))) : {tc.view(Tc.round.one(Tc.free(ready, Tc.Here{x}), False{}, i, Tc.round(t, u, 1n+i, Tc.grow(Tc.free(ready, Tc.Here{x}), Tc.key(Tc.Here{x}), ready))), Tc.Here{x} <> t, i) == tc.sview(_) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}
          tc.put(Tc.free(ready, Tc.Here{x}), Tc.Here{x}, i, t, Tc.round(t, u, 1n+i, Tc.grow(Tc.free(ready, Tc.Here{x}), Tc.key(Tc.Here{x}), ready)), TreeCommit.pass(tc.T(t, u, 1n+i), cs, Tc.grow(Tc.free(ready, Tc.Here{x}), Tc.key(Tc.Here{x}), ready)), {==}, ih)
        case Tc.Under{+x, +y}:
          %Equal.sym(TreeCommit.Pass, TreeCommit.pass(i <> tc.T(t, u, 1n+i), cs, ready), TreeCommit.pass.cons(Tc.free(ready, Tc.Under{x, y}), i, TreeCommit.pass(tc.T(t, u, 1n+i), cs, Tc.grow(Tc.free(ready, Tc.Under{x, y}), Tc.key(Tc.Under{x, y}), ready))), tc.Q(ready, cs, i, Tc.Under{x, y}, tc.T(t, u, 1n+i), tc.at_drop(i, cs, Tc.Under{x, y}, t, h))) : {tc.view(Tc.round.one(Tc.free(ready, Tc.Under{x, y}), False{}, i, Tc.round(t, u, 1n+i, Tc.grow(Tc.free(ready, Tc.Under{x, y}), Tc.key(Tc.Under{x, y}), ready))), Tc.Under{x, y} <> t, i) == tc.sview(_) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}
          tc.put(Tc.free(ready, Tc.Under{x, y}), Tc.Under{x, y}, i, t, Tc.round(t, u, 1n+i, Tc.grow(Tc.free(ready, Tc.Under{x, y}), Tc.key(Tc.Under{x, y}), ready)), TreeCommit.pass(tc.T(t, u, 1n+i), cs, Tc.grow(Tc.free(ready, Tc.Under{x, y}), Tc.key(Tc.Under{x, y}), ready)), {==}, ih)
        case Tc.Gone{}:
          Equal.trans(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), tc.view(Tc.round.one(False{}, False{}, i, Tc.round(t, u, 1n+i, ready)), Tc.Gone{} <> t, i), tc.view(Tc.round(t, u, 1n+i, ready), t, 1n+i), tc.sview(TreeCommit.pass(tc.T(t, u, 1n+i), cs, ready)), tc.keep(Tc.Gone{}, False{}, i, t, Tc.round(t, u, 1n+i, ready), {==}), ih)

# one code round over the changes suf of cs from index i answers one spec
# pass over its waiting Puts
def tc.R(suf: List<&2, Tc.Ch>, ms: List<&2, Bool>, +i: Nat, +ready: List<&2, Nat>, +cs: List<&2, Tc.Ch>, +h: {tc.drop(i, cs) == suf : List<&2, Tc.Ch>}) -> {tc.view(Tc.round(suf, ms, i, ready), suf, i) == tc.sview(TreeCommit.pass(tc.T(suf, ms, i), cs, ready)) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}:
  match suf:
    case Nil{}:
      {==}
    case +c <> +t:
      match ms:
        case Nil{}:
          tc.Rc(False{}, c, t, [], i, ready, cs, h, tc.R(t, [], 1n+i, Tc.grow(Tc.free(ready, c), Tc.key(c), ready), cs, tc.drop_next(i, cs, c, t, h)))
        case +m <> +u:
          tc.Rc(m, c, t, u, i, ready, cs, h, tc.R(t, u, 1n+i, Tc.grow(Bool.and(Bool.not(m), Tc.free(ready, c)), Tc.key(c), ready), cs, tc.drop_next(i, cs, c, t, h)))

# ---- the rounds ----

def tc.rd(r: Tc.Round) -> List<&2, Nat>:
  match r:
    case Tc.Round{out, ms, rd, hit}:
      rd

def tc.ms(r: Tc.Round) -> List<&2, Bool>:
  match r:
    case Tc.Round{out, ms, rd, hit}:
      ms

def tc.p1(v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> List<&2, Tc.Res>:
  match v:
    case (x, y):
      x

def tc.p2(v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> List<&2, Nat>:
  match v:
    case (x, y):
      match y:
        case (z, q):
          z

def tc.p3(v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> List<&2, Nat>:
  match v:
    case (x, y):
      match y:
        case (z, q):
          match q:
            case (r, h):
              r

def tc.p4(v: List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))) -> Bool:
  match v:
    case (x, y):
      match y:
        case (z, q):
          match q:
            case (r, h):
              h

# a round that answered (out, its waiting Puts, rd, hit) as the spec's
# pass answered (a, w, rd2): the code's next rounds are the spec's
def tc.CRt(g: Nat, +cs: List<&2, Tc.Ch>, -ms: List<&2, Bool>, +out: List<&2, Tc.Res>, +ms2: List<&2, Bool>, +rd: List<&2, Nat>, +hit: Bool, a: List<&2, Nat>, +w: List<&2, Nat>, +rd2: List<&2, Nat>, +e: {(out, (tc.T(cs, ms2, 0n), (rd, hit))) == (TreeCommit.applies(a), (w, (rd2, tc.nonnil(a)))) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, ih: {Tc.rounds(g, cs, ms2, Tc.round(cs, ms2, 0n, rd)) == List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, rd, tc.T(cs, ms2, 0n)), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}) -> {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, hit}) == List.append(&2, Tc.Res, TreeCommit.rounds.pick(a, w, TreeCommit.rounds_spec(g, cs, rd2, w)), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}:
  match a:
    case Nil{}:
      e4 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), Bool, v => tc.p4(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), ([], (w, (rd2, False{}))), e)
      e2 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Nat>, v => tc.p2(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), ([], (w, (rd2, False{}))), e)
      %Equal.sym(Bool, hit, False{}, e4) : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, _}) == List.append(&2, Tc.Res, TreeCommit.unknowns(w), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %e2 : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, False{}}) == List.append(&2, Tc.Res, TreeCommit.unknowns(_), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %tc.orph(cs, ms2, 0n) : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, False{}}) == List.append(&2, Tc.Res, _, TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %tc.ret(cs, 0n) : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, False{}}) == List.append(&2, Tc.Res, Tc.orphans(cs, ms2, 0n), _) : List<&2, Tc.Res>}
      {==}
    case +x <> +y:
      e1 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Tc.Res>, v => tc.p1(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), (Tc.Apply{x} <> TreeCommit.applies(y), (w, (rd2, True{}))), e)
      e2 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Nat>, v => tc.p2(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), (Tc.Apply{x} <> TreeCommit.applies(y), (w, (rd2, True{}))), e)
      e3 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), List<&2, Nat>, v => tc.p3(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), (Tc.Apply{x} <> TreeCommit.applies(y), (w, (rd2, True{}))), e)
      e4 = Equal.cong(List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool)), Bool, v => tc.p4(v), (out, (tc.T(cs, ms2, 0n), (rd, hit))), (Tc.Apply{x} <> TreeCommit.applies(y), (w, (rd2, True{}))), e)
      +A = TreeCommit.applies(x <> y)
      +S = TreeCommit.rounds_spec(g, cs, rd2, w)
      %Equal.sym(Bool, hit, True{}, e4) : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, _}) == List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %Equal.sym(List<&2, Tc.Res>, Tc.rounds(g, cs, ms2, Tc.round(cs, ms2, 0n, rd)), List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, rd, tc.T(cs, ms2, 0n)), TreeCommit.dels_spec(cs, 0n)), ih) : {List.append(&2, Tc.Res, out, _) == List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %Equal.sym(List<&2, Tc.Res>, out, A, e1) : {List.append(&2, Tc.Res, _, List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, rd, tc.T(cs, ms2, 0n)), TreeCommit.dels_spec(cs, 0n))) == List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %Equal.sym(List<&2, Nat>, rd, rd2, e3) : {List.append(&2, Tc.Res, A, List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, _, tc.T(cs, ms2, 0n)), TreeCommit.dels_spec(cs, 0n))) == List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %Equal.sym(List<&2, Nat>, tc.T(cs, ms2, 0n), w, e2) : {List.append(&2, Tc.Res, A, List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, rd2, _), TreeCommit.dels_spec(cs, 0n))) == List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      Equal.sym(List<&2, Tc.Res>, List.append(&2, Tc.Res, List.append(&2, Tc.Res, A, S), TreeCommit.dels_spec(cs, 0n)), List.append(&2, Tc.Res, A, List.append(&2, Tc.Res, S, TreeCommit.dels_spec(cs, 0n))), tc.app_assoc(A, S, TreeCommit.dels_spec(cs, 0n)))

# a round r that answered as the spec's pass p
def tc.CRs(g: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +ms: List<&2, Bool>, r: Tc.Round, p: TreeCommit.Pass, e: {tc.view(r, cs, 0n) == tc.sview(p) : List<&2, Tc.Res> & (List<&2, Nat> & (List<&2, Nat> & Bool))}, ep: {TreeCommit.pass(tc.T(cs, ms, 0n), cs, ready) == p : TreeCommit.Pass}, ih: {Tc.rounds(g, cs, tc.ms(r), Tc.round(cs, tc.ms(r), 0n, tc.rd(r))) == List.append(&2, Tc.Res, TreeCommit.rounds_spec(g, cs, tc.rd(r), tc.T(cs, tc.ms(r), 0n)), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}) -> {Tc.rounds(1n+g, cs, ms, r) == List.append(&2, Tc.Res, TreeCommit.rounds_spec(1n+g, cs, ready, tc.T(cs, ms, 0n)), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}:
  match r:
    case Tc.Round{out, ms2, rd, hit}:
      match p:
        case TreeCommit.Pass{a, w, rd2}:
          %Equal.sym(TreeCommit.Pass, TreeCommit.pass(tc.T(cs, ms, 0n), cs, ready), TreeCommit.Pass{a, w, rd2}, ep) : {Tc.rounds(1n+g, cs, ms, Tc.Round{out, ms2, rd, hit}) == List.append(&2, Tc.Res, TreeCommit.rounds.pick(TreeCommit.Pass.applied(_), TreeCommit.Pass.waiting(_), TreeCommit.rounds_spec(g, cs, TreeCommit.Pass.ready(_), TreeCommit.Pass.waiting(_))), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
          tc.CRt(g, cs, ms, out, ms2, rd, hit, a, w, rd2, e, ih)

# the code's rounds are the spec's, the Dels after them
def tc.CR(f: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +ms: List<&2, Bool>) -> {Tc.rounds(f, cs, ms, Tc.round(cs, ms, 0n, ready)) == List.append(&2, Tc.Res, TreeCommit.rounds_spec(f, cs, ready, tc.T(cs, ms, 0n)), TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}:
  match f:
    case 0n:
      %tc.orph(cs, ms, 0n) : {Tc.rounds(0n, cs, ms, Tc.round(cs, ms, 0n, ready)) == List.append(&2, Tc.Res, _, TreeCommit.dels_spec(cs, 0n)) : List<&2, Tc.Res>}
      %tc.ret(cs, 0n) : {Tc.rounds(0n, cs, ms, Tc.round(cs, ms, 0n, ready)) == List.append(&2, Tc.Res, Tc.orphans(cs, ms, 0n), _) : List<&2, Tc.Res>}
      {==}
    case 1n++g:
      +r = Tc.round(cs, ms, 0n, ready)
      tc.CRs(g, cs, ready, ms, r, TreeCommit.pass(tc.T(cs, ms, 0n), cs, ready), tc.R(cs, ms, 0n, ready, cs, {==}), {==}, tc.CR(g, cs, tc.rd(r), tc.ms(r)))
