# eukhe: lemmas of the entry proofs of area agent_tree
# (bend/ffi_agent_tree.bend): a spelled request that fits reads back
# (ate.reads: each field by the wire's round trips, a list by
# wire_list_reads_items, a node by induction on it with fuel: the node
# reader's fuel, the length of its input, is at least ate.need of the node,
# ate.len_node), and the entry's answer is the spec's spelling of the
# model's decision (ate.reply: each encoder is the spec's speller) that
# never opens with 'E' (ate.answer_ok)

import Base
import ../../../bend/agent_tree.bend as T
import ../../../bend/agent_crown.bend as C
import ../../../bend/ffi_agent_tree.bend as FAt
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/agent_tree.bend as AgentTree
import ../../base/nat.bend as LNat
import ../../base/wire.bend as LWire
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr

# Bool
# ----

def ate.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def ate.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : ate.If(_, G)
  Unit{}

# True is not False
def ate.absurdT(-G: Type, e: {True{} == False{} : Bool}) -> G:
  ate.absurd(G, Equal.sym(Bool, True{}, False{}, e))

def ate.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def ate.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ate.absurd({b == True{} : Bool}, e)

def ate.and_t(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# Round trip: the fields
# ----------------------
# Each lemma is stated as the rewrite it is used for: the answer Got{x,
# rest} on the left, the decoder on the spelling on the right.

def ate.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def ate.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

def ate.mnat(m: Maybe<&2, Nat>, +rest: String, h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FAt.get_mnat(AgentTree.w_mnat(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %ate.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == FAt.get_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def ate.dir(d: T.Dir, rest: String) -> {Wr.Got{d, rest} == FAt.get_dir(Wr.put_nat(AgentTree.dir_tag(d), rest)) : Wr.Dec<T.Dir>}:
  match d:
    case T.GoL{}:
      {==}
    case T.GoR{}:
      {==}

def ate.lim(l: T.Lim, +rest: String, h: {AgentTree.fit_lim(l) == True{} : Bool}) -> {Wr.Got{l, rest} == FAt.get_lim(AgentTree.w_lim(l, rest)) : Wr.Dec<T.Lim>}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{+n}:
      %ate.nat(n, rest, h) : {Wr.Got{T.Value{n}, rest} == FAt.get_lim.value(_) : Wr.Dec<T.Lim>}
      {==}

def ate.status(st: T.Status, rest: String) -> {Wr.Got{st, rest} == FAt.get_status(Wr.put_nat(AgentTree.status_tag(st), rest)) : Wr.Dec<T.Status>}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

# Round trip: the lists
# ---------------------

def ate.bools.items(xs: List<&2, Bool>, +rest: String) -> {Wr.Got{xs, rest} == LawsBase.wire_items(~Bool, ~Wr.get_bool, List.length(&2, Bool, xs), AgentTree.w_bools.items(xs, rest)) : Wr.Dec<List<&2, Bool>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +m = List.length(&2, Bool, t)
      +s1 = AgentTree.w_bools.items(t, rest)
      %ate.bool(x, s1) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(Bool, _, r => LawsBase.wire_items(~Bool, ~Wr.get_bool, m, r)) : Wr.Dec<List<&2, Bool>>}
      %ate.bools.items(t, rest) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(Bool, x, _) : Wr.Dec<List<&2, Bool>>}
      {==}

def ate.bools(+xs: List<&2, Bool>, +rest: String, fc: {AgentTree.fit_bools(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FAt.get_bools(AgentTree.w_bools(xs, rest)) : Wr.Dec<List<&2, Bool>>}:
  +n = List.length(&2, Bool, xs)
  +s1 = AgentTree.w_bools.items(xs, rest)
  %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~Bool, ~Wr.get_bool, Wr.put_nat(n, s1))) : {Wr.Got{xs, rest} == _ : Wr.Dec<List<&2, Bool>>}
  %ate.nat(n, s1, fc) : {Wr.Got{xs, rest} == LawsBase.wire_read_list.count(~Bool, ~Wr.get_bool, _) : Wr.Dec<List<&2, Bool>>}
  ate.bools.items(xs, rest)

def ate.patch.items(xs: List<&2, Maybe<&2, Nat>>, +rest: String, h: {AgentTree.fit_patch.items(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, List.length(&2, Maybe<&2, Nat>, xs), AgentTree.w_patch.items(xs, rest)) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = h
      +fx = ate.and_l(LawsBase.wire_mfits(x), AgentTree.fit_patch.items(t), h0)
      +ft = ate.and_r(LawsBase.wire_mfits(x), AgentTree.fit_patch.items(t), h0)
      +m = List.length(&2, Maybe<&2, Nat>, t)
      +s1 = AgentTree.w_patch.items(t, rest)
      %ate.mnat(x, s1, fx) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(Maybe<&2, Nat>, _, r => LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, m, r)) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      %ate.patch.items(t, rest, ft) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(Maybe<&2, Nat>, x, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
      {==}

def ate.patch(+xs: List<&2, Maybe<&2, Nat>>, +rest: String, h: {AgentTree.fit_patch(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FAt.get_patch(AgentTree.w_patch(xs, rest)) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}:
  +h0 = h
  +n = List.length(&2, Maybe<&2, Nat>, xs)
  +fc = ate.and_l(LawsBase.wire_fits(n), AgentTree.fit_patch.items(xs), h0)
  +fx = ate.and_r(LawsBase.wire_fits(n), AgentTree.fit_patch.items(xs), h0)
  +s1 = AgentTree.w_patch.items(xs, rest)
  %Equal.sym(Wr.Dec<List<&2, Maybe<&2, Nat>>>, Wr.get_list(~Maybe<&2, Nat>, ~FAt.get_mnat, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~Maybe<&2, Nat>, ~FAt.get_mnat, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~Maybe<&2, Nat>, ~FAt.get_mnat, Wr.put_nat(n, s1))) : {Wr.Got{xs, rest} == _ : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
  %ate.nat(n, s1, fc) : {Wr.Got{xs, rest} == LawsBase.wire_read_list.count(~Maybe<&2, Nat>, ~FAt.get_mnat, _) : Wr.Dec<List<&2, Maybe<&2, Nat>>>}
  ate.patch.items(xs, rest, fx)

def ate.path.items(ps: List<&2, T.Dir>, +rest: String) -> {Wr.Got{ps, rest} == LawsBase.wire_items(~T.Dir, ~FAt.get_dir, List.length(&2, T.Dir, ps), AgentTree.w_path.items(ps, rest)) : Wr.Dec<List<&2, T.Dir>>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +m = List.length(&2, T.Dir, t)
      +s1 = AgentTree.w_path.items(t, rest)
      %ate.dir(x, s1) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(T.Dir, _, r => LawsBase.wire_items(~T.Dir, ~FAt.get_dir, m, r)) : Wr.Dec<List<&2, T.Dir>>}
      %ate.path.items(t, rest) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(T.Dir, x, _) : Wr.Dec<List<&2, T.Dir>>}
      {==}

def ate.path(+ps: List<&2, T.Dir>, +rest: String, fc: {AgentTree.fit_path(ps) == True{} : Bool}) -> {Wr.Got{ps, rest} == FAt.get_path(AgentTree.w_path(ps, rest)) : Wr.Dec<List<&2, T.Dir>>}:
  +n = List.length(&2, T.Dir, ps)
  +s1 = AgentTree.w_path.items(ps, rest)
  %Equal.sym(Wr.Dec<List<&2, T.Dir>>, Wr.get_list(~T.Dir, ~FAt.get_dir, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~T.Dir, ~FAt.get_dir, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~T.Dir, ~FAt.get_dir, Wr.put_nat(n, s1))) : {Wr.Got{ps, rest} == _ : Wr.Dec<List<&2, T.Dir>>}
  %ate.nat(n, s1, fc) : {Wr.Got{ps, rest} == LawsBase.wire_read_list.count(~T.Dir, ~FAt.get_dir, _) : Wr.Dec<List<&2, T.Dir>>}
  ate.path.items(ps, rest)

# Round trip: info, node
# ----------------------

def ate.info(i: T.Info, +rest: String, h: {AgentTree.fit_info(i) == True{} : Bool}) -> {Wr.Got{i, rest} == FAt.get_info(AgentTree.w_info(i, rest)) : Wr.Dec<T.Info>}:
  match i:
    case T.Info{+st, +sc, +lim, +sp, +dl, +p}:
      +h0 = h
      +b3 = Bool.and(AgentTree.fit_lim(dl), AgentTree.fit_patch(p))
      +b2 = Bool.and(LawsBase.wire_fits(sp), b3)
      +b1 = Bool.and(AgentTree.fit_lim(lim), b2)
      +f1 = ate.and_l(AgentTree.fit_bools(sc), b1, h0)
      +h1 = ate.and_r(AgentTree.fit_bools(sc), b1, h0)
      +f2 = ate.and_l(AgentTree.fit_lim(lim), b2, h1)
      +h2 = ate.and_r(AgentTree.fit_lim(lim), b2, h1)
      +f3 = ate.and_l(LawsBase.wire_fits(sp), b3, h2)
      +h3 = ate.and_r(LawsBase.wire_fits(sp), b3, h2)
      +f4 = ate.and_l(AgentTree.fit_lim(dl), AgentTree.fit_patch(p), h3)
      +f5 = ate.and_r(AgentTree.fit_lim(dl), AgentTree.fit_patch(p), h3)
      +s5 = AgentTree.w_patch(p, rest)
      +s4 = AgentTree.w_lim(dl, s5)
      +s3 = Wr.put_nat(sp, s4)
      +s2 = AgentTree.w_lim(lim, s3)
      +s1 = AgentTree.w_bools(sc, s2)
      +v = {Wr.Got{T.Info{st, sc, lim, sp, dl, p}, rest} : Wr.Dec<T.Info>}
      %ate.status(st, s1) : {v == FAt.get_info.status(_) : Wr.Dec<T.Info>}
      %ate.bools(sc, s2, f1) : {v == FAt.get_info.scope(st, _) : Wr.Dec<T.Info>}
      %ate.lim(lim, s3, f2) : {v == FAt.get_info.limit(st, sc, _) : Wr.Dec<T.Info>}
      %ate.nat(sp, s4, f3) : {v == FAt.get_info.spent(st, sc, lim, _) : Wr.Dec<T.Info>}
      %ate.lim(dl, s5, f4) : {v == FAt.get_info.deadline(st, sc, lim, sp, _) : Wr.Dec<T.Info>}
      %ate.patch(p, rest, f5) : {v == FAt.get_info.patch(st, sc, lim, sp, dl, _) : Wr.Dec<T.Info>}
      {==}

# the fuel a node needs: one for a leaf; for a split two more than its
# children's
def ate.need(t: T.Node) -> Nat:
  match t:
    case T.Leaf{i}:
      1n
    case T.Split{i, own, l, r}:
      1n+1n+Nat.add(ate.need(l), ate.need(r))

# a spelled node that fits reads back with any fuel f of at least its need
def ate.node(t: T.Node, +rest: String, f: Nat, h: {AgentTree.fit_node(t) == True{} : Bool}, le: {Nat.is_le(ate.need(t), f) == True{} : Bool}) -> {FAt.get_node.go(f, FAt.AtHead{FAt.get_head(AgentTree.w_node(t, rest))}) == Wr.Got{t, rest} : Wr.Dec<T.Node>}:
  match t:
    case T.Leaf{+i}:
      match f:
        case 0n:
          ate.absurd({FAt.get_node.go(0n, FAt.AtHead{FAt.get_head(AgentTree.w_node(T.Leaf{i}, rest))}) == Wr.Got{T.Leaf{i}, rest} : Wr.Dec<T.Node>}, le)
        case 1n+g:
          %ate.info(i, rest, h) : {FAt.get_node.go(1n+g, FAt.AtHead{FAt.get_head.leaf(_)}) == Wr.Got{T.Leaf{i}, rest} : Wr.Dec<T.Node>}
          {==}
    case T.Split{+i, +own, +l, +r}:
      match f:
        case 0n:
          ate.absurd({FAt.get_node.go(0n, FAt.AtHead{FAt.get_head(AgentTree.w_node(T.Split{i, own, l, r}, rest))}) == Wr.Got{T.Split{i, own, l, r}, rest} : Wr.Dec<T.Node>}, le)
        case 1n+g:
          match g:
            case 0n:
              ate.absurd({FAt.get_node.go(1n, FAt.AtHead{FAt.get_head(AgentTree.w_node(T.Split{i, own, l, r}, rest))}) == Wr.Got{T.Split{i, own, l, r}, rest} : Wr.Dec<T.Node>}, le)
            case 1n++g2:
              +h0 = h
              +bl = Bool.and(AgentTree.fit_node(l), AgentTree.fit_node(r))
              +bo = Bool.and(AgentTree.fit_bools(own), bl)
              +fi = ate.and_l(AgentTree.fit_info(i), bo, h0)
              +h1 = ate.and_r(AgentTree.fit_info(i), bo, h0)
              +fo = ate.and_l(AgentTree.fit_bools(own), bl, h1)
              +h2 = ate.and_r(AgentTree.fit_bools(own), bl, h1)
              +fl = ate.and_l(AgentTree.fit_node(l), AgentTree.fit_node(r), h2)
              +fr = ate.and_r(AgentTree.fit_node(l), AgentTree.fit_node(r), h2)
              +nl = ate.need(l)
              +nr = ate.need(r)
              +le0 = le
              +le_l = LNat.pu.le_succ_r(nl, g2, LNat.pu.le_trans(nl, Nat.add(nl, nr), g2, LNat.pu.le_add_r(nl, nr), le0))
              +le_r = LNat.pu.le_trans(nr, Nat.add(nl, nr), g2, LNat.compactor.pc.le_add(nl, nr), le0)
              +rr = AgentTree.w_node(r, rest)
              +y = AgentTree.w_node(l, rr)
              +v = {Wr.Got{T.Split{i, own, l, r}, rest} : Wr.Dec<T.Node>}
              %ate.info(i, AgentTree.w_bools(own, y), fi) : {FAt.get_node.go(1n+1n+g2, FAt.AtHead{FAt.get_head.split(_)}) == v : Wr.Dec<T.Node>}
              %ate.bools(own, y, fo) : {FAt.get_node.go(1n+1n+g2, FAt.AtHead{FAt.get_head.own(i, _)}) == v : Wr.Dec<T.Node>}
              %Equal.sym(Wr.Dec<T.Node>, FAt.get_node.go(1n+g2, FAt.AtHead{FAt.get_head(y)}), Wr.Got{l, rr}, ate.node(l, rr, 1n+g2, fl, le_l)) : {FAt.get_node.go(1n+g2, FAt.AtRight{i, own, _}) == v : Wr.Dec<T.Node>}
              %Equal.sym(Wr.Dec<T.Node>, FAt.get_node.go(g2, FAt.AtHead{FAt.get_head(rr)}), Wr.Got{r, rest}, ate.node(r, rest, g2, fr, le_r)) : {FAt.get_node.join(i, own, l, _) == v : Wr.Dec<T.Node>}
              {==}

# Fuel: a spelling only grows its rest
# ------------------------------------

def ate.grow_go(g: Nat, q: Nat, +acc: String) -> {Nat.is_le(String.length(acc), String.length(Wr.put_nat.go(g, q, acc))) == True{} : Bool}:
  match g:
    case 0n:
      LNat.pu.le_refl(String.length(acc))
    case 1n++f:
      match q:
        case 0n:
          LNat.pu.le_refl(String.length(acc))
        case 1n+p:
          +m = {1n+p : Nat}
          +a2 = {SCon{Wr.dchar(Nat.mod(m, 10n)), acc} : String}
          LNat.pu.le_trans(String.length(acc), String.length(a2), String.length(Wr.put_nat.go(f, Nat.div(m, 10n), a2)), LNat.screen.ps.le_succ(String.length(acc)), ate.grow_go(f, Nat.div(m, 10n), a2))

def ate.grow_nat(+n: Nat, +rest: String) -> {Nat.is_le(String.length(rest), String.length(Wr.put_nat(n, rest))) == True{} : Bool}:
  +a2 = {SCon{Wr.dchar(Nat.mod(n, 10n)), SCon{',', rest}} : String}
  LNat.pu.le_trans(String.length(rest), String.length(a2), String.length(Wr.put_nat.go(n, Nat.div(n, 10n), a2)), LNat.pu.le_succ_r(String.length(rest), 1n+String.length(rest), LNat.screen.ps.le_succ(String.length(rest))), ate.grow_go(n, Nat.div(n, 10n), a2))

def ate.grow_bool(b: Bool, +rest: String) -> {Nat.is_le(String.length(rest), String.length(Wr.put_bool(b, rest))) == True{} : Bool}:
  match b:
    case True{}:
      LNat.screen.ps.le_succ(String.length(rest))
    case False{}:
      LNat.screen.ps.le_succ(String.length(rest))

# a <= b <= c
def ate.tr(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  LNat.pu.le_trans(a, b, c, ab, bc)

def ate.grow_bools.items(xs: List<&2, Bool>, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_bools.items(xs, rest))) == True{} : Bool}:
  match xs:
    case Nil{}:
      LNat.pu.le_refl(String.length(rest))
    case Con{+x, +t}:
      +s1 = AgentTree.w_bools.items(t, rest)
      ate.tr(String.length(rest), String.length(s1), String.length(Wr.put_bool(x, s1)), ate.grow_bools.items(t, rest), ate.grow_bool(x, s1))

def ate.grow_bools(+xs: List<&2, Bool>, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_bools(xs, rest))) == True{} : Bool}:
  +s1 = AgentTree.w_bools.items(xs, rest)
  ate.tr(String.length(rest), String.length(s1), String.length(Wr.put_nat(List.length(&2, Bool, xs), s1)), ate.grow_bools.items(xs, rest), ate.grow_nat(List.length(&2, Bool, xs), s1))

# a tag then a Nat
def ate.grow_two(+k: Nat, +n: Nat, +rest: String) -> {Nat.is_le(String.length(rest), String.length(Wr.put_nat(k, Wr.put_nat(n, rest)))) == True{} : Bool}:
  +s1 = Wr.put_nat(n, rest)
  ate.tr(String.length(rest), String.length(s1), String.length(Wr.put_nat(k, s1)), ate.grow_nat(n, rest), ate.grow_nat(k, s1))

def ate.grow_mnat(m: Maybe<&2, Nat>, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_mnat(m, rest))) == True{} : Bool}:
  match m:
    case None{}:
      ate.grow_nat(0n, rest)
    case Some{x}:
      ate.grow_two(1n, x, rest)

def ate.grow_lim(l: T.Lim, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_lim(l, rest))) == True{} : Bool}:
  match l:
    case T.Unlimited{}:
      ate.grow_nat(0n, rest)
    case T.Value{n}:
      ate.grow_two(1n, n, rest)

def ate.grow_patch.items(xs: List<&2, Maybe<&2, Nat>>, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_patch.items(xs, rest))) == True{} : Bool}:
  match xs:
    case Nil{}:
      LNat.pu.le_refl(String.length(rest))
    case Con{+x, +t}:
      +s1 = AgentTree.w_patch.items(t, rest)
      ate.tr(String.length(rest), String.length(s1), String.length(AgentTree.w_mnat(x, s1)), ate.grow_patch.items(t, rest), ate.grow_mnat(x, s1))

def ate.grow_patch(+xs: List<&2, Maybe<&2, Nat>>, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_patch(xs, rest))) == True{} : Bool}:
  +s1 = AgentTree.w_patch.items(xs, rest)
  ate.tr(String.length(rest), String.length(s1), String.length(Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), s1)), ate.grow_patch.items(xs, rest), ate.grow_nat(List.length(&2, Maybe<&2, Nat>, xs), s1))

def ate.grow_info(i: T.Info, +rest: String) -> {Nat.is_le(String.length(rest), String.length(AgentTree.w_info(i, rest))) == True{} : Bool}:
  match i:
    case T.Info{+st, +sc, +lim, +sp, +dl, +p}:
      +s5 = AgentTree.w_patch(p, rest)
      +s4 = AgentTree.w_lim(dl, s5)
      +s3 = Wr.put_nat(sp, s4)
      +s2 = AgentTree.w_lim(lim, s3)
      +s1 = AgentTree.w_bools(sc, s2)
      +s0 = Wr.put_nat(AgentTree.status_tag(st), s1)
      +l5 = ate.grow_patch(p, rest)
      +l4 = ate.tr(String.length(rest), String.length(s5), String.length(s4), l5, ate.grow_lim(dl, s5))
      +l3 = ate.tr(String.length(rest), String.length(s4), String.length(s3), l4, ate.grow_nat(sp, s4))
      +l2 = ate.tr(String.length(rest), String.length(s3), String.length(s2), l3, ate.grow_lim(lim, s3))
      +l1 = ate.tr(String.length(rest), String.length(s2), String.length(s1), l2, ate.grow_bools(sc, s2))
      ate.tr(String.length(rest), String.length(s1), String.length(s0), l1, ate.grow_nat(AgentTree.status_tag(st), s1))

# the spelling of t before rest is at least need(t) longer than rest
def ate.len_node(t: T.Node, +rest: String) -> {Nat.is_le(Nat.add(ate.need(t), String.length(rest)), String.length(AgentTree.w_node(t, rest))) == True{} : Bool}:
  match t:
    case T.Leaf{+i}:
      LNat.pu.le_succ_r(String.length(rest), String.length(AgentTree.w_info(i, rest)), ate.grow_info(i, rest))
    case T.Split{+i, +own, +l, +r}:
      +nl = ate.need(l)
      +nr = ate.need(r)
      +lr = String.length(rest)
      +rr = AgentTree.w_node(r, rest)
      +y = AgentTree.w_node(l, rr)
      +ln = String.length(AgentTree.w_info(i, AgentTree.w_bools(own, y)))
      +gy = ate.tr(String.length(y), String.length(AgentTree.w_bools(own, y)), ln, ate.grow_bools(own, y), ate.grow_info(i, AgentTree.w_bools(own, y)))
      %LNat.add_assoc_r(nl, nr, lr) : {Nat.is_le(_, ln) == True{} : Bool}
      ate.tr(Nat.add(nl, Nat.add(nr, lr)), Nat.add(nl, String.length(rr)), ln, LNat.ps.le_mono(nl, Nat.add(nr, lr), String.length(rr), ate.len_node(r, rest)), ate.tr(Nat.add(nl, String.length(rr)), String.length(y), ln, ate.len_node(l, rr), gy))

# a spelled node that fits reads back
def ate.node_top(+t: T.Node, +rest: String, h: {AgentTree.fit_node(t) == True{} : Bool}) -> {FAt.get_node(AgentTree.w_node(t, rest)) == Wr.Got{t, rest} : Wr.Dec<T.Node>}:
  +s = AgentTree.w_node(t, rest)
  +n = ate.need(t)
  ate.node(t, rest, String.length(s), h, ate.tr(n, Nat.add(n, String.length(rest)), String.length(s), LNat.pu.le_add_r(n, String.length(rest)), ate.len_node(t, rest)))

# Round trip: bounds, view, event, request
# ----------------------------------------

def ate.bounds(b: T.Bounds, +rest: String, h: {AgentTree.fit_bounds(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FAt.get_bounds(AgentTree.w_bounds(b, rest)) : Wr.Dec<T.Bounds>}:
  match b:
    case T.Bounds{+d, +n, +m}:
      +h0 = h
      +fd = ate.and_l(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(m)), h0)
      +h1 = ate.and_r(LawsBase.wire_fits(d), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(m)), h0)
      +fn = ate.and_l(LawsBase.wire_fits(n), LawsBase.wire_fits(m), h1)
      +fm = ate.and_r(LawsBase.wire_fits(n), LawsBase.wire_fits(m), h1)
      +v = {Wr.Got{T.Bounds{d, n, m}, rest} : Wr.Dec<T.Bounds>}
      %ate.nat(d, Wr.put_nat(n, Wr.put_nat(m, rest)), fd) : {v == FAt.get_bounds.depth(_) : Wr.Dec<T.Bounds>}
      %ate.nat(n, Wr.put_nat(m, rest), fn) : {v == FAt.get_bounds.nodes(d, _) : Wr.Dec<T.Bounds>}
      %ate.nat(m, rest, fm) : {v == FAt.get_bounds.margin(d, n, _) : Wr.Dec<T.Bounds>}
      {==}

def ate.view(v: T.View, +rest: String, h: {AgentTree.fit_view(v) == True{} : Bool}) -> {Wr.Got{v, rest} == FAt.get_view(AgentTree.w_view(v, rest)) : Wr.Dec<T.View>}:
  match v:
    case T.View{+m, +n, +w}:
      +g = {Wr.Got{T.View{m, n, w}, rest} : Wr.Dec<T.View>}
      %ate.bool(m, Wr.put_nat(n, Wr.put_bool(w, rest))) : {g == FAt.get_view.message(_) : Wr.Dec<T.View>}
      %ate.nat(n, Wr.put_bool(w, rest), h) : {g == FAt.get_view.arrived(m, _) : Wr.Dec<T.View>}
      %ate.bool(w, rest) : {g == FAt.get_view.work(m, n, _) : Wr.Dec<T.View>}
      {==}

def ate.ev(e: T.Ev, +rest: String, h: {AgentTree.fit_ev(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FAt.get_ev(AgentTree.w_ev(e, rest)) : Wr.Dec<T.Ev>}:
  match e:
    case T.EvSplit{+at, +own, +ls, +rs, +hold}:
      +h0 = h
      +b3 = Bool.and(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold))
      +b2 = Bool.and(AgentTree.fit_bools(ls), b3)
      +b1 = Bool.and(AgentTree.fit_bools(own), b2)
      +fa = ate.and_l(AgentTree.fit_path(at), b1, h0)
      +h1 = ate.and_r(AgentTree.fit_path(at), b1, h0)
      +fo = ate.and_l(AgentTree.fit_bools(own), b2, h1)
      +h2 = ate.and_r(AgentTree.fit_bools(own), b2, h1)
      +fl = ate.and_l(AgentTree.fit_bools(ls), b3, h2)
      +h3 = ate.and_r(AgentTree.fit_bools(ls), b3, h2)
      +fr = ate.and_l(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold), h3)
      +fh = ate.and_r(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold), h3)
      +s4 = Wr.put_nat(hold, rest)
      +s3 = AgentTree.w_bools(rs, s4)
      +s2 = AgentTree.w_bools(ls, s3)
      +s1 = AgentTree.w_bools(own, s2)
      +g = {Wr.Got{T.EvSplit{at, own, ls, rs, hold}, rest} : Wr.Dec<T.Ev>}
      %ate.path(at, s1, fa) : {g == FAt.get_ev.at(0n, _) : Wr.Dec<T.Ev>}
      %ate.bools(own, s2, fo) : {g == FAt.get_ev.split_own(at, _) : Wr.Dec<T.Ev>}
      %ate.bools(ls, s3, fl) : {g == FAt.get_ev.split_ls(at, own, _) : Wr.Dec<T.Ev>}
      %ate.bools(rs, s4, fr) : {g == FAt.get_ev.split_rs(at, own, ls, _) : Wr.Dec<T.Ev>}
      %ate.nat(hold, rest, fh) : {g == FAt.get_ev.split_hold(at, own, ls, rs, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvSpend{+at, +n}:
      +h0 = h
      +fa = ate.and_l(AgentTree.fit_path(at), LawsBase.wire_fits(n), h0)
      +fn = ate.and_r(AgentTree.fit_path(at), LawsBase.wire_fits(n), h0)
      +g = {Wr.Got{T.EvSpend{at, n}, rest} : Wr.Dec<T.Ev>}
      %ate.path(at, Wr.put_nat(n, rest), fa) : {g == FAt.get_ev.at(1n, _) : Wr.Dec<T.Ev>}
      %ate.nat(n, rest, fn) : {g == FAt.get_ev.spend(at, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvFinish{+at, +p}:
      +h0 = h
      +fa = ate.and_l(AgentTree.fit_path(at), AgentTree.fit_patch(p), h0)
      +fp = ate.and_r(AgentTree.fit_path(at), AgentTree.fit_patch(p), h0)
      +g = {Wr.Got{T.EvFinish{at, p}, rest} : Wr.Dec<T.Ev>}
      %ate.path(at, AgentTree.w_patch(p, rest), fa) : {g == FAt.get_ev.at(2n, _) : Wr.Dec<T.Ev>}
      %ate.patch(p, rest, fp) : {g == FAt.get_ev.finish(at, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvFail{+at, +p}:
      +h0 = h
      +fa = ate.and_l(AgentTree.fit_path(at), AgentTree.fit_patch(p), h0)
      +fp = ate.and_r(AgentTree.fit_path(at), AgentTree.fit_patch(p), h0)
      +g = {Wr.Got{T.EvFail{at, p}, rest} : Wr.Dec<T.Ev>}
      %ate.path(at, AgentTree.w_patch(p, rest), fa) : {g == FAt.get_ev.at(3n, _) : Wr.Dec<T.Ev>}
      %ate.patch(p, rest, fp) : {g == FAt.get_ev.fail(at, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvCancel{+at}:
      %ate.path(at, rest, h) : {Wr.Got{T.EvCancel{at}, rest} == FAt.get_ev.at(4n, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvRedo{+at, +side, +x}:
      +h0 = h
      +fa = ate.and_l(AgentTree.fit_path(at), LawsBase.wire_fits(x), h0)
      +fx = ate.and_r(AgentTree.fit_path(at), LawsBase.wire_fits(x), h0)
      +s2 = Wr.put_nat(x, rest)
      +s1 = Wr.put_nat(AgentTree.dir_tag(side), s2)
      +g = {Wr.Got{T.EvRedo{at, side, x}, rest} : Wr.Dec<T.Ev>}
      %ate.path(at, s1, fa) : {g == FAt.get_ev.at(5n, _) : Wr.Dec<T.Ev>}
      %ate.dir(side, s2) : {g == FAt.get_ev.redo_side(at, _) : Wr.Dec<T.Ev>}
      %ate.nat(x, rest, fx) : {g == FAt.get_ev.redo_extra(at, side, _) : Wr.Dec<T.Ev>}
      {==}
    case T.EvTick{+now}:
      %ate.nat(now, rest, h) : {Wr.Got{T.EvTick{now}, rest} == FAt.get_ev.tick(_) : Wr.Dec<T.Ev>}
      {==}

# Round trip: help leaves, crown, crown event
# -------------------------------------------

def ate.help(h: C.Help, +rest: String, f: {AgentTree.fit_help(h) == True{} : Bool}) -> {Wr.Got{h, rest} == FAt.get_help(AgentTree.w_help(h, rest)) : Wr.Dec<C.Help>}:
  match h:
    case C.Help{+at, +st, +lim, +sp, +dl}:
      +h0 = f
      +b2 = Bool.and(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl))
      +b1 = Bool.and(AgentTree.fit_lim(lim), b2)
      +fa = ate.and_l(AgentTree.fit_path(at), b1, h0)
      +h1 = ate.and_r(AgentTree.fit_path(at), b1, h0)
      +fl = ate.and_l(AgentTree.fit_lim(lim), b2, h1)
      +h2 = ate.and_r(AgentTree.fit_lim(lim), b2, h1)
      +fs = ate.and_l(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl), h2)
      +fd = ate.and_r(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl), h2)
      +s3 = AgentTree.w_lim(dl, rest)
      +s2 = Wr.put_nat(sp, s3)
      +s1 = AgentTree.w_lim(lim, s2)
      +s0 = Wr.put_nat(AgentTree.status_tag(st), s1)
      +g = {Wr.Got{C.Help{at, st, lim, sp, dl}, rest} : Wr.Dec<C.Help>}
      %ate.path(at, s0, fa) : {g == FAt.get_help.at(_) : Wr.Dec<C.Help>}
      %ate.status(st, s1) : {g == FAt.get_help.status(at, _) : Wr.Dec<C.Help>}
      %ate.lim(lim, s2, fl) : {g == FAt.get_help.limit(at, st, _) : Wr.Dec<C.Help>}
      %ate.nat(sp, s3, fs) : {g == FAt.get_help.spent(at, st, lim, _) : Wr.Dec<C.Help>}
      %ate.lim(dl, rest, fd) : {g == FAt.get_help.deadline(at, st, lim, sp, _) : Wr.Dec<C.Help>}
      {==}

def ate.helps.items(hs: List<&2, C.Help>, +rest: String, h: {AgentTree.fit_helps.items(hs) == True{} : Bool}) -> {Wr.Got{hs, rest} == LawsBase.wire_items(~C.Help, ~FAt.get_help, List.length(&2, C.Help, hs), AgentTree.w_helps.items(hs, rest)) : Wr.Dec<List<&2, C.Help>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = h
      +fx = ate.and_l(AgentTree.fit_help(x), AgentTree.fit_helps.items(t), h0)
      +ft = ate.and_r(AgentTree.fit_help(x), AgentTree.fit_helps.items(t), h0)
      +m = List.length(&2, C.Help, t)
      +s1 = AgentTree.w_helps.items(t, rest)
      %ate.help(x, s1, fx) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.then(C.Help, _, r => LawsBase.wire_items(~C.Help, ~FAt.get_help, m, r)) : Wr.Dec<List<&2, C.Help>>}
      %ate.helps.items(t, rest, ft) : {Wr.Got{x <> t, rest} == LawsBase.wire_items.cons(C.Help, x, _) : Wr.Dec<List<&2, C.Help>>}
      {==}

def ate.helps(+hs: List<&2, C.Help>, +rest: String, h: {AgentTree.fit_helps(hs) == True{} : Bool}) -> {Wr.Got{hs, rest} == FAt.get_helps(AgentTree.w_helps(hs, rest)) : Wr.Dec<List<&2, C.Help>>}:
  +h0 = h
  +n = List.length(&2, C.Help, hs)
  +fc = ate.and_l(LawsBase.wire_fits(n), AgentTree.fit_helps.items(hs), h0)
  +fx = ate.and_r(LawsBase.wire_fits(n), AgentTree.fit_helps.items(hs), h0)
  +s1 = AgentTree.w_helps.items(hs, rest)
  %Equal.sym(Wr.Dec<List<&2, C.Help>>, Wr.get_list(~C.Help, ~FAt.get_help, Wr.put_nat(n, s1)), LawsBase.wire_read_list(~C.Help, ~FAt.get_help, Wr.put_nat(n, s1)), Wire.wire_list_reads_items(~C.Help, ~FAt.get_help, Wr.put_nat(n, s1))) : {Wr.Got{hs, rest} == _ : Wr.Dec<List<&2, C.Help>>}
  %ate.nat(n, s1, fc) : {Wr.Got{hs, rest} == LawsBase.wire_read_list.count(~C.Help, ~FAt.get_help, _) : Wr.Dec<List<&2, C.Help>>}
  ate.helps.items(hs, rest, fx)

def ate.crown(c: C.Crown, +rest: String, h: {AgentTree.fit_crown(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FAt.get_crown(AgentTree.w_crown(c, rest)) : Wr.Dec<C.Crown>}:
  match c:
    case C.Crown{+t, +hs}:
      +h0 = h
      +ft = ate.and_l(AgentTree.fit_node(t), AgentTree.fit_helps(hs), h0)
      +fh = ate.and_r(AgentTree.fit_node(t), AgentTree.fit_helps(hs), h0)
      +s1 = AgentTree.w_helps(hs, rest)
      +g = {Wr.Got{C.Crown{t, hs}, rest} : Wr.Dec<C.Crown>}
      %Equal.sym(Wr.Dec<T.Node>, FAt.get_node(AgentTree.w_node(t, s1)), Wr.Got{t, s1}, ate.node_top(t, s1, ft)) : {g == FAt.get_crown.node(_) : Wr.Dec<C.Crown>}
      %ate.helps(hs, rest, fh) : {g == FAt.get_crown.helps(t, _) : Wr.Dec<C.Crown>}
      {==}

def ate.cev(e: C.CEv, +rest: String, h: {AgentTree.fit_cev(e) == True{} : Bool}) -> {Wr.Got{e, rest} == FAt.get_cev(AgentTree.w_cev(e, rest)) : Wr.Dec<C.CEv>}:
  match e:
    case C.OnTree{+x}:
      %ate.ev(x, rest, h) : {Wr.Got{C.OnTree{x}, rest} == FAt.get_cev.on(_) : Wr.Dec<C.CEv>}
      {==}
    case C.EvHelp{+at, +n}:
      +h0 = h
      +fa = ate.and_l(AgentTree.fit_path(at), LawsBase.wire_fits(n), h0)
      +fn = ate.and_r(AgentTree.fit_path(at), LawsBase.wire_fits(n), h0)
      +g = {Wr.Got{C.EvHelp{at, n}, rest} : Wr.Dec<C.CEv>}
      %ate.path(at, Wr.put_nat(n, rest), fa) : {g == FAt.get_cev.help_at(_) : Wr.Dec<C.CEv>}
      %ate.nat(n, rest, fn) : {g == FAt.get_cev.help_n(at, _) : Wr.Dec<C.CEv>}
      {==}
    case C.EvHelpSpend{+k, +n}:
      +h0 = h
      +fk = ate.and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(n), h0)
      +fn = ate.and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(n), h0)
      +g = {Wr.Got{C.EvHelpSpend{k, n}, rest} : Wr.Dec<C.CEv>}
      %ate.nat(k, Wr.put_nat(n, rest), fk) : {g == FAt.get_cev.spend_k(_) : Wr.Dec<C.CEv>}
      %ate.nat(n, rest, fn) : {g == FAt.get_cev.spend_n(k, _) : Wr.Dec<C.CEv>}
      {==}
    case C.EvHelpEnd{+k, +ok}:
      +g = {Wr.Got{C.EvHelpEnd{k, ok}, rest} : Wr.Dec<C.CEv>}
      %ate.nat(k, Wr.put_bool(ok, rest), h) : {g == FAt.get_cev.end_k(_) : Wr.Dec<C.CEv>}
      %ate.bool(ok, rest) : {g == FAt.get_cev.end_ok(k, _) : Wr.Dec<C.CEv>}
      {==}

# a spelled request that fits reads back, the rest untouched
def ate.reads(q: FAt.Req, +rest: String, h: {AgentTree.fit_req(q) == True{} : Bool}) -> {FAt.get_req(AgentTree.w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FAt.Req>}:
  match q:
    case FAt.QStep{+b, +c, +e}:
      +h0 = h
      +fb = ate.and_l(AgentTree.fit_bounds(b), Bool.and(AgentTree.fit_crown(c), AgentTree.fit_cev(e)), h0)
      +h1 = ate.and_r(AgentTree.fit_bounds(b), Bool.and(AgentTree.fit_crown(c), AgentTree.fit_cev(e)), h0)
      +fc = ate.and_l(AgentTree.fit_crown(c), AgentTree.fit_cev(e), h1)
      +fe = ate.and_r(AgentTree.fit_crown(c), AgentTree.fit_cev(e), h1)
      +s2 = AgentTree.w_cev(e, rest)
      +s1 = AgentTree.w_crown(c, s2)
      +g = {Wr.Got{FAt.QStep{b, c, e}, rest} : Wr.Dec<FAt.Req>}
      %ate.bounds(b, s1, fb) : {FAt.get_req.step(_) == g : Wr.Dec<FAt.Req>}
      %ate.crown(c, s2, fc) : {FAt.get_req.step_crown(b, _) == g : Wr.Dec<FAt.Req>}
      %ate.cev(e, rest, fe) : {FAt.get_req.step_ev(b, c, _) == g : Wr.Dec<FAt.Req>}
      {==}
    case FAt.QOverlay{+cur, +a, +s}:
      +h0 = h
      +fc = ate.and_l(AgentTree.fit_patch(cur), Bool.and(AgentTree.fit_patch(a), AgentTree.fit_bools(s)), h0)
      +h1 = ate.and_r(AgentTree.fit_patch(cur), Bool.and(AgentTree.fit_patch(a), AgentTree.fit_bools(s)), h0)
      +fa = ate.and_l(AgentTree.fit_patch(a), AgentTree.fit_bools(s), h1)
      +fs = ate.and_r(AgentTree.fit_patch(a), AgentTree.fit_bools(s), h1)
      +s2 = AgentTree.w_bools(s, rest)
      +s1 = AgentTree.w_patch(a, s2)
      +g = {Wr.Got{FAt.QOverlay{cur, a, s}, rest} : Wr.Dec<FAt.Req>}
      %ate.patch(cur, s1, fc) : {FAt.get_req.overlay(_) == g : Wr.Dec<FAt.Req>}
      %ate.patch(a, s2, fa) : {FAt.get_req.overlay_a(cur, _) == g : Wr.Dec<FAt.Req>}
      %ate.bools(s, rest, fs) : {FAt.get_req.overlay_s(cur, a, _) == g : Wr.Dec<FAt.Req>}
      {==}
    case FAt.QNext{+v}:
      %ate.view(v, rest, h) : {FAt.get_req.next(_) == Wr.Got{FAt.QNext{v}, rest} : Wr.Dec<FAt.Req>}
      {==}
    case FAt.QFree{+c, +p}:
      +h0 = h
      +fc = ate.and_l(AgentTree.fit_crown(c), AgentTree.fit_path(p), h0)
      +fp = ate.and_r(AgentTree.fit_crown(c), AgentTree.fit_path(p), h0)
      +g = {Wr.Got{FAt.QFree{c, p}, rest} : Wr.Dec<FAt.Req>}
      %ate.crown(c, AgentTree.w_path(p, rest), fc) : {FAt.get_req.free(_) == g : Wr.Dec<FAt.Req>}
      %ate.path(p, rest, fp) : {FAt.get_req.free_path(c, _) == g : Wr.Dec<FAt.Req>}
      {==}

# The reply: each encoder is the spec's speller
# ---------------------------------------------

def ate.w_mnat(m: Maybe<&2, Nat>, rest: String) -> {FAt.put_mnat(m, rest) == AgentTree.w_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def ate.w_lim(l: T.Lim, rest: String) -> {FAt.put_lim(l, rest) == AgentTree.w_lim(l, rest) : String}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{n}:
      {==}

def ate.w_status(st: T.Status) -> {FAt.status_tag(st) == AgentTree.status_tag(st) : Nat}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

def ate.w_refusal(w: T.Refusal) -> {FAt.refusal_tag(w) == AgentTree.refusal_tag(w) : Nat}:
  match w:
    case T.NoNode{}:
      {==}
    case T.NotRunning{}:
      {==}
    case T.NotLeaf{}:
      {==}
    case T.TooDeep{}:
      {==}
    case T.TooMany{}:
      {==}
    case T.BadScopes{}:
      {==}
    case T.NoBudget{}:
      {==}
    case T.Unsettled{}:
      {==}
    case T.NotRedoable{}:
      {==}

def ate.w_action(a: T.Action) -> {FAt.action_tag(a) == AgentTree.action_tag(a) : Nat}:
  match a:
    case T.ReadMessage{}:
      {==}
    case T.Integrate{}:
      {==}
    case T.WorkOwn{}:
      {==}
    case T.Waits{}:
      {==}

# the list writer's loop answers the count and the spec's items
def ate.bools_go(xs: List<&2, Bool>, -rest: String) -> {Wr.put_list.go(~Bool, ~Wr.put_bool, xs, rest) == (List.length(&2, Bool, xs), AgentTree.w_bools.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, t, rest), (List.length(&2, Bool, t), AgentTree.w_bools.items(t, rest)), ate.bools_go(t, rest)) : {Wr.put_list.step(~Bool, ~Wr.put_bool, x, _) == (1n+List.length(&2, Bool, t), Wr.put_bool(x, AgentTree.w_bools.items(t, rest))) : Nat & String}
      {==}

def ate.w_bools(+xs: List<&2, Bool>, -rest: String) -> {FAt.put_bools(xs, rest) == AgentTree.w_bools(xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, xs, rest), (List.length(&2, Bool, xs), AgentTree.w_bools.items(xs, rest)), ate.bools_go(xs, rest)) : {Wr.put_list.fin(_) == AgentTree.w_bools(xs, rest) : String}
  {==}

def ate.patch_go(xs: List<&2, Maybe<&2, Nat>>, +rest: String) -> {Wr.put_list.go(~Maybe<&2, Nat>, ~FAt.put_mnat, xs, rest) == (List.length(&2, Maybe<&2, Nat>, xs), AgentTree.w_patch.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +n = List.length(&2, Maybe<&2, Nat>, t)
      +it = AgentTree.w_patch.items(t, rest)
      %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, Nat>, ~FAt.put_mnat, t, rest), (n, it), ate.patch_go(t, rest)) : {Wr.put_list.step(~Maybe<&2, Nat>, ~FAt.put_mnat, x, _) == (1n+n, AgentTree.w_mnat(x, it)) : Nat & String}
      %Equal.sym(String, FAt.put_mnat(x, it), AgentTree.w_mnat(x, it), ate.w_mnat(x, it)) : {(1n+n, _) == (1n+n, AgentTree.w_mnat(x, it)) : Nat & String}
      {==}

def ate.w_patch(+xs: List<&2, Maybe<&2, Nat>>, +rest: String) -> {FAt.put_patch(xs, rest) == AgentTree.w_patch(xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Maybe<&2, Nat>, ~FAt.put_mnat, xs, rest), (List.length(&2, Maybe<&2, Nat>, xs), AgentTree.w_patch.items(xs, rest)), ate.patch_go(xs, rest)) : {Wr.put_list.fin(_) == AgentTree.w_patch(xs, rest) : String}
  {==}

def ate.w_info(i: T.Info, +rest: String) -> {FAt.put_info(i, rest) == AgentTree.w_info(i, rest) : String}:
  match i:
    case T.Info{+st, +sc, +lim, +sp, +dl, +p}:
      +s5 = AgentTree.w_patch(p, rest)
      +s4 = AgentTree.w_lim(dl, s5)
      +s3 = Wr.put_nat(sp, s4)
      +s2 = AgentTree.w_lim(lim, s3)
      +s1 = AgentTree.w_bools(sc, s2)
      +w = AgentTree.w_info(T.Info{st, sc, lim, sp, dl, p}, rest)
      %Equal.sym(String, FAt.put_patch(p, rest), s5, ate.w_patch(p, rest)) : {Wr.put_nat(FAt.status_tag(st), FAt.put_bools(sc, FAt.put_lim(lim, Wr.put_nat(sp, FAt.put_lim(dl, _))))) == w : String}
      %Equal.sym(String, FAt.put_lim(dl, s5), s4, ate.w_lim(dl, s5)) : {Wr.put_nat(FAt.status_tag(st), FAt.put_bools(sc, FAt.put_lim(lim, Wr.put_nat(sp, _)))) == w : String}
      %Equal.sym(String, FAt.put_lim(lim, s3), s2, ate.w_lim(lim, s3)) : {Wr.put_nat(FAt.status_tag(st), FAt.put_bools(sc, _)) == w : String}
      %Equal.sym(String, FAt.put_bools(sc, s2), s1, ate.w_bools(sc, s2)) : {Wr.put_nat(FAt.status_tag(st), _) == w : String}
      %Equal.sym(Nat, FAt.status_tag(st), AgentTree.status_tag(st), ate.w_status(st)) : {Wr.put_nat(_, s1) == w : String}
      {==}

def ate.w_node(t: T.Node, +rest: String) -> {FAt.put_node(t, rest) == AgentTree.w_node(t, rest) : String}:
  match t:
    case T.Leaf{+i}:
      %Equal.sym(String, FAt.put_info(i, rest), AgentTree.w_info(i, rest), ate.w_info(i, rest)) : {Wr.put_nat(0n, _) == AgentTree.w_node(T.Leaf{i}, rest) : String}
      {==}
    case T.Split{+i, +own, +l, +r}:
      +rr = AgentTree.w_node(r, rest)
      +y = AgentTree.w_node(l, rr)
      +w = AgentTree.w_node(T.Split{i, own, l, r}, rest)
      %Equal.sym(String, FAt.put_node(r, rest), rr, ate.w_node(r, rest)) : {Wr.put_nat(1n, FAt.put_info(i, FAt.put_bools(own, FAt.put_node(l, _)))) == w : String}
      %Equal.sym(String, FAt.put_node(l, rr), y, ate.w_node(l, rr)) : {Wr.put_nat(1n, FAt.put_info(i, FAt.put_bools(own, _))) == w : String}
      %Equal.sym(String, FAt.put_bools(own, y), AgentTree.w_bools(own, y), ate.w_bools(own, y)) : {Wr.put_nat(1n, FAt.put_info(i, _)) == w : String}
      %Equal.sym(String, FAt.put_info(i, AgentTree.w_bools(own, y)), AgentTree.w_info(i, AgentTree.w_bools(own, y)), ate.w_info(i, AgentTree.w_bools(own, y))) : {Wr.put_nat(1n, _) == w : String}
      {==}

def ate.w_dir(d: T.Dir) -> {FAt.dir_tag(d) == AgentTree.dir_tag(d) : Nat}:
  match d:
    case T.GoL{}:
      {==}
    case T.GoR{}:
      {==}

def ate.path_go(ps: List<&2, T.Dir>, +rest: String) -> {Wr.put_list.go(~T.Dir, ~FAt.put_dir, ps, rest) == (List.length(&2, T.Dir, ps), AgentTree.w_path.items(ps, rest)) : Nat & String}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +n = List.length(&2, T.Dir, t)
      +it = AgentTree.w_path.items(t, rest)
      %Equal.sym(Nat & String, Wr.put_list.go(~T.Dir, ~FAt.put_dir, t, rest), (n, it), ate.path_go(t, rest)) : {Wr.put_list.step(~T.Dir, ~FAt.put_dir, x, _) == (1n+n, Wr.put_nat(AgentTree.dir_tag(x), it)) : Nat & String}
      %Equal.sym(Nat, FAt.dir_tag(x), AgentTree.dir_tag(x), ate.w_dir(x)) : {(1n+n, Wr.put_nat(_, it)) == (1n+n, Wr.put_nat(AgentTree.dir_tag(x), it)) : Nat & String}
      {==}

def ate.w_path(+ps: List<&2, T.Dir>, +rest: String) -> {FAt.put_path(ps, rest) == AgentTree.w_path(ps, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~T.Dir, ~FAt.put_dir, ps, rest), (List.length(&2, T.Dir, ps), AgentTree.w_path.items(ps, rest)), ate.path_go(ps, rest)) : {Wr.put_list.fin(_) == AgentTree.w_path(ps, rest) : String}
  {==}

def ate.w_help(h: C.Help, +rest: String) -> {FAt.put_help(h, rest) == AgentTree.w_help(h, rest) : String}:
  match h:
    case C.Help{+at, +st, +lim, +sp, +dl}:
      +s3 = AgentTree.w_lim(dl, rest)
      +s2 = Wr.put_nat(sp, s3)
      +s1 = AgentTree.w_lim(lim, s2)
      +s0 = Wr.put_nat(AgentTree.status_tag(st), s1)
      +w = AgentTree.w_help(C.Help{at, st, lim, sp, dl}, rest)
      %Equal.sym(String, FAt.put_lim(dl, rest), s3, ate.w_lim(dl, rest)) : {FAt.put_path(at, Wr.put_nat(FAt.status_tag(st), FAt.put_lim(lim, Wr.put_nat(sp, _)))) == w : String}
      %Equal.sym(String, FAt.put_lim(lim, s2), s1, ate.w_lim(lim, s2)) : {FAt.put_path(at, Wr.put_nat(FAt.status_tag(st), _)) == w : String}
      %Equal.sym(Nat, FAt.status_tag(st), AgentTree.status_tag(st), ate.w_status(st)) : {FAt.put_path(at, Wr.put_nat(_, s1)) == w : String}
      %Equal.sym(String, FAt.put_path(at, s0), AgentTree.w_path(at, s0), ate.w_path(at, s0)) : {_ == w : String}
      {==}

def ate.helps_go(hs: List<&2, C.Help>, +rest: String) -> {Wr.put_list.go(~C.Help, ~FAt.put_help, hs, rest) == (List.length(&2, C.Help, hs), AgentTree.w_helps.items(hs, rest)) : Nat & String}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +n = List.length(&2, C.Help, t)
      +it = AgentTree.w_helps.items(t, rest)
      %Equal.sym(Nat & String, Wr.put_list.go(~C.Help, ~FAt.put_help, t, rest), (n, it), ate.helps_go(t, rest)) : {Wr.put_list.step(~C.Help, ~FAt.put_help, x, _) == (1n+n, AgentTree.w_help(x, it)) : Nat & String}
      %Equal.sym(String, FAt.put_help(x, it), AgentTree.w_help(x, it), ate.w_help(x, it)) : {(1n+n, _) == (1n+n, AgentTree.w_help(x, it)) : Nat & String}
      {==}

def ate.w_helps(+hs: List<&2, C.Help>, +rest: String) -> {FAt.put_helps(hs, rest) == AgentTree.w_helps(hs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~C.Help, ~FAt.put_help, hs, rest), (List.length(&2, C.Help, hs), AgentTree.w_helps.items(hs, rest)), ate.helps_go(hs, rest)) : {Wr.put_list.fin(_) == AgentTree.w_helps(hs, rest) : String}
  {==}

def ate.w_crown(c: C.Crown, +rest: String) -> {FAt.put_crown(c, rest) == AgentTree.w_crown(c, rest) : String}:
  match c:
    case C.Crown{+t, +hs}:
      +s1 = AgentTree.w_helps(hs, rest)
      %Equal.sym(String, FAt.put_helps(hs, rest), s1, ate.w_helps(hs, rest)) : {FAt.put_node(t, _) == AgentTree.w_crown(C.Crown{t, hs}, rest) : String}
      ate.w_node(t, s1)

def ate.w_cstep(s: C.CStep) -> {FAt.put_cstep(s) == AgentTree.w_cstep(s) : String}:
  match s:
    case C.CTook{+c}:
      %Equal.sym(String, FAt.put_crown(c, ""), AgentTree.w_crown(c, ""), ate.w_crown(c, "")) : {Wr.put_nat(0n, _) == AgentTree.w_cstep(C.CTook{c}) : String}
      {==}
    case C.CRefused{+w}:
      %Equal.sym(Nat, FAt.refusal_tag(w), AgentTree.refusal_tag(w), ate.w_refusal(w)) : {Wr.put_nat(1n, Wr.put_nat(_, "")) == AgentTree.w_cstep(C.CRefused{w}) : String}
      {==}

def ate.w_mlim(m: Maybe<&2, T.Lim>) -> {FAt.put_mlim(m) == AgentTree.w_mlim(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+l}:
      %Equal.sym(String, FAt.put_lim(l, ""), AgentTree.w_lim(l, ""), ate.w_lim(l, "")) : {Wr.put_nat(1n, _) == AgentTree.w_mlim(Some{l}) : String}
      {==}

# the entry's answer is the spec's spelling of the model's decision
def ate.reply(q: FAt.Req) -> {FAt.answer(q) == AgentTree.w_reply(q) : String}:
  match q:
    case FAt.QStep{+b, +c, +e}:
      ate.w_cstep(C.hstep(b, c, e))
    case FAt.QOverlay{+cur, +a, +s}:
      +o = T.overlay(cur, a, s)
      +c = T.conflicts(a, s)
      +w = AgentTree.w_reply(FAt.QOverlay{cur, a, s})
      %Equal.sym(String, FAt.put_bools(c, ""), AgentTree.w_bools(c, ""), ate.w_bools(c, "")) : {FAt.put_patch(o, _) == w : String}
      %Equal.sym(String, FAt.put_patch(o, AgentTree.w_bools(c, "")), AgentTree.w_patch(o, AgentTree.w_bools(c, "")), ate.w_patch(o, AgentTree.w_bools(c, ""))) : {_ == w : String}
      {==}
    case FAt.QNext{+v}:
      %Equal.sym(Nat, FAt.action_tag(T.next(v)), AgentTree.action_tag(T.next(v)), ate.w_action(T.next(v))) : {Wr.put_nat(_, "") == AgentTree.w_reply(FAt.QNext{v}) : String}
      {==}
    case FAt.QFree{+c, +p}:
      ate.w_mlim(C.cfree(c, p))

# no spelled decision opens with 'E'
def ate.cstep_ok(s: C.CStep) -> {LawsBase.wire_opens_err(AgentTree.w_cstep(s)) == False{} : Bool}:
  match s:
    case C.CTook{c}:
      Wire.wire_nat_not_err(0n, AgentTree.w_crown(c, ""))
    case C.CRefused{w}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(AgentTree.refusal_tag(w), ""))

def ate.mlim_ok(m: Maybe<&2, T.Lim>) -> {LawsBase.wire_opens_err(AgentTree.w_mlim(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{l}:
      Wire.wire_nat_not_err(1n, AgentTree.w_lim(l, ""))

def ate.reply_ok(q: FAt.Req) -> {LawsBase.wire_opens_err(AgentTree.w_reply(q)) == False{} : Bool}:
  match q:
    case FAt.QStep{+b, +c, +e}:
      ate.cstep_ok(C.hstep(b, c, e))
    case FAt.QOverlay{+cur, +a, +s}:
      +o = T.overlay(cur, a, s)
      Wire.wire_nat_not_err(List.length(&2, Maybe<&2, Nat>, o), AgentTree.w_patch.items(o, AgentTree.w_bools(T.conflicts(a, s), "")))
    case FAt.QNext{v}:
      Wire.wire_nat_not_err(AgentTree.action_tag(T.next(v)), "")
    case FAt.QFree{+c, +p}:
      ate.mlim_ok(C.cfree(c, p))

def ate.answer_ok(+q: FAt.Req) -> {LawsBase.wire_opens_err(FAt.answer(q)) == False{} : Bool}:
  %Equal.sym(String, FAt.answer(q), AgentTree.w_reply(q), ate.reply(q)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  ate.reply_ok(q)
