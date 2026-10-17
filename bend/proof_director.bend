# proof_director: the Director stack laws (S5), about bend/director.bend.
#
# The bound: a decision under `above` layers keeps above + len(stack) at
# most cap (`pd.go_bounded`). A layer that keeps its place keeps the
# length; a deferring layer goes back on the stack of the layers below
# (`pd.under_ok`), which is bounded under one more layer; a Leave drops
# it (`pd.le_pred`); a Stack checks room in the whole stack (`pd.push_ok`).
# Each loop step is one decision (`pd.tick_bounded`).
#
# The loop: `pd.ok(l, k)` says the loop has ended, or has fewer than k
# global steps left. A tick takes one step off (`pd.tick_ok`), so after k
# steps the loop has ended (`pd.ends_go`). An ended loop never changes.
#
# The tree: layer i of a stack (0 = bottom) is the nodes 2i + 1 and
# 2i + 2, appended after the nodes of the layers below. So every key of
# encode(s) is at most 2 len(s) (`pd.enc_lt`), the nodes stay sorted
# (`pd.enc_sorted`), and each kind node hangs under the root or the kind
# node of the layer below (`pd.parent_ok`), each budget node under its
# kind node (`pd.enc_rooted`). decode reads the pairs back in order
# (`pd.dec_go`), and a rewind reaches the encoded tree (proof_tree's
# `rewind_reaches`), so it restores the stack.

import Base
import ./director.bend as Dr
import ./tree.bend as Tr
import ./proof_tree.bend as Pt

# Numbers
# -------

def pd.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_succ(p)

def pd.lt_add2(n: Nat) -> {Nat.is_lt(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_add2(p)

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

# The loop
# --------

# the loop has ended, or has fewer than k steps left
def pd.ok(l: Dr.Loop, k: Nat) -> Bool:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          Nat.is_lt(n, k)
        case Some{x}:
          True{}

def pd.cont_ok(n: Nat, +s: List<&2, Dr.Layer>, +k: Nat, h: {Nat.is_lt(n, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.cont(n, s), k) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      h

def pd.after_ok(+n: Nat, d: Dr.Dec, +k: Nat, h: {Nat.is_lt(n, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.after(n, d), k) == True{} : Bool}:
  match d:
    case Dr.Dec{o, s}:
      match o:
        case Dr.Cont{}:
          pd.cont_ok(n, s, k, h)
        case Dr.Hand{}:
          {==}
        case Dr.Failed{}:
          {==}

# a tick takes one step off the loop
def pd.tick_ok(+cap: Nat, l: Dr.Loop, vs: List<&2, Dr.Verdict>, +k: Nat, h: {pd.ok(l, 1n+k) == True{} : Bool}) -> {pd.ok(Dr.tick(cap, l, vs), k) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, s, e}:
      match e:
        case None{}:
          pd.after_ok(n, Dr.decide(s, vs, cap), k, h)
        case Some{x}:
          {==}

def pd.ok_zero(l: Dr.Loop, h: {pd.ok(l, 0n) == True{} : Bool}) -> {Dr.ended(l) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          Pt.pt.lt_zero({Dr.ended(Dr.Loop{n, s, None{}}) == True{} : Bool}, n, h)
        case Some{x}:
          {==}

# a loop with fewer steps left than verdict lists has ended after them
def pd.ends_go(vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, +l: Dr.Loop, h: {pd.ok(l, List.length(&2, List<&2, Dr.Verdict>, vss)) == True{} : Bool}) -> {Dr.ended(Dr.run(vss, cap, l)) == True{} : Bool}:
  match vss:
    case Nil{}:
      pd.ok_zero(l, h)
    case +vs <> +rest:
      pd.ends_go(rest, cap, Dr.tick(cap, l, vs), pd.tick_ok(cap, l, vs, List.length(&2, List<&2, Dr.Verdict>, rest), h))

def pd.lt_len(+n: Nat, +k: Nat, e: {k == 1n+n : Nat}) -> {Nat.is_lt(n, k) == True{} : Bool}:
  %Equal.sym(Nat, k, 1n+n, e) : {Nat.is_lt(n, _) == True{} : Bool}
  pd.lt_succ(n)

def pd.dir_loop_ends(+n: Nat, +s: List<&2, Dr.Layer>, +vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, long: {List.length(&2, List<&2, Dr.Verdict>, vss) == 1n+n : Nat}) -> {Dr.ended(Dr.run(vss, cap, Dr.Loop{n, s, None{}})) == True{} : Bool}:
  pd.ends_go(vss, cap, Dr.Loop{n, s, None{}}, pd.lt_len(n, List.length(&2, List<&2, Dr.Verdict>, vss), long))

def pd.dir_end_is_final(+cap: Nat, +l: Dr.Loop, done: {Dr.ended(l) == True{} : Bool}, vs: List<&2, Dr.Verdict>) -> {Dr.tick(cap, l, vs) == l : Dr.Loop}:
  match l:
    case Dr.Loop{n, s, e}:
      match e:
        case None{}:
          Pt.pt.absurdF({Dr.tick(cap, Dr.Loop{n, s, None{}}, vs) == Dr.Loop{n, s, None{}} : Dr.Loop}, done)
        case Some{x}:
          {==}

# The stack in the tree: order
# ----------------------------

# every key of t is less than m
def pd.lt_all(t: List<&2, Tr.Ent>, +m: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(rest, m))

def pd.lt_all_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +m: Nat, +ha: {pd.lt_all(A, m) == True{} : Bool}, hb: {pd.lt_all(B, m) == True{} : Bool}) -> {pd.lt_all(List.append(&2, Tr.Ent, A, B), m) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case +e <> +r:
      Pt.pt.and_t(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(List.append(&2, Tr.Ent, r, B), m), Pt.pt.and_l(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(r, m), ha), pd.lt_all_app(r, B, m, Pt.pt.and_r(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(r, m), ha), hb))

# every key of encode(s) is at most twice the layers of s
def pd.enc_lt(s: List<&2, Dr.Layer>, +m: Nat, +h: {Nat.is_lt(Nat.double(List.length(&2, Dr.Layer, s)), m) == True{} : Bool}) -> {pd.lt_all(Dr.encode(s), m) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +hr = Pt.pt.lt_trans(Nat.double(n), 2n+Nat.double(n), m, pd.lt_add2(Nat.double(n)), h)
          +hx = Pt.pt.lt_trans(1n+Nat.double(n), 2n+Nat.double(n), m, pd.lt_succ(1n+Nat.double(n)), h)
          +hxy = Pt.pt.and_t(Nat.is_lt(1n+Nat.double(n), m), Bool.and(Nat.is_lt(2n+Nat.double(n), m), True{}), hx, Pt.pt.and_t(Nat.is_lt(2n+Nat.double(n), m), True{}, h, {==}))
          pd.lt_all_app(Dr.encode(rest), [x, y], m, pd.enc_lt(rest, m, hr), hxy)

def pd.above_app(+e: Tr.Ent, r: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, sa: {Tr.sorted(e <> r) == True{} : Bool}, la: {pd.lt_all(e <> r, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)) == True{} : Bool}:
  match r:
    case Nil{}:
      Pt.pt.and_l(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), True{}, la)
    case +h <> +t:
      Pt.pt.and_l(Tr.above(Tr.Ent.k(e), h <> t), Tr.sorted(h <> t), sa)

# a sorted list, then sorted nodes above all its keys, is sorted
def pd.sorted_snoc(A: List<&2, Tr.Ent>, +x: Tr.Ent, +C: List<&2, Tr.Ent>, +sa: {Tr.sorted(A) == True{} : Bool}, sc: {Tr.sorted(x <> C) == True{} : Bool}, +la: {pd.lt_all(A, Tr.Ent.k(x)) == True{} : Bool}) -> {Tr.sorted(List.append(&2, Tr.Ent, A, x <> C)) == True{} : Bool}:
  match A:
    case Nil{}:
      sc
    case +e <> +r:
      +sr = Pt.pt.and_r(Tr.above(Tr.Ent.k(e), r), Tr.sorted(r), sa)
      +lr = Pt.pt.and_r(Nat.is_lt(Tr.Ent.k(e), Tr.Ent.k(x)), pd.lt_all(r, Tr.Ent.k(x)), la)
      Pt.pt.and_t(Tr.above(Tr.Ent.k(e), List.append(&2, Tr.Ent, r, x <> C)), Tr.sorted(List.append(&2, Tr.Ent, r, x <> C)), pd.above_app(e, r, x, C, sa, la), pd.sorted_snoc(r, x, C, sr, sc, lr))

def pd.enc_sorted(s: List<&2, Dr.Layer>) -> {Tr.sorted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +sxy = Pt.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Tr.sorted([y]), pd.lt_succ(1n+Nat.double(n)), {==})
          pd.sorted_snoc(Dr.encode(rest), x, [y], pd.enc_sorted(rest), sxy, pd.enc_lt(rest, 1n+Nat.double(n), pd.lt_succ(Nat.double(n))))

# The stack in the tree: parents
# ------------------------------

def pd.or_has_app(c: Bool, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +p: Nat, o: {Bool.or(c, Tr.has(all, p)) == True{} : Bool}) -> {Bool.or(c, Tr.has(List.append(&2, Tr.Ent, all, C), p)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Pt.pt.has_app_l(all, C, p, o)

# a parent stays a parent when nodes come after
def pd.ok_app(+all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +k: Nat, +p: Nat, +h: {Tr.ok(all, k, p) == True{} : Bool}) -> {Tr.ok(List.append(&2, Tr.Ent, all, C), k, p) == True{} : Bool}:
  +o = Pt.pt.and_r(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h)
  Pt.pt.and_t(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(List.append(&2, Tr.Ent, all, C), p)), Pt.pt.and_l(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), Tr.has(all, p)), h), pd.or_has_app(Nat.is_eq(p, 0n), all, C, p, o))

def pd.rooted_app_all(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +C: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {Tr.rooted.go(s, List.append(&2, Tr.Ent, all, C)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +r:
      +he = Pt.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      +hr = Pt.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), rs)
      Pt.pt.and_t(Tr.ok(List.append(&2, Tr.Ent, all, C), Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, List.append(&2, Tr.Ent, all, C)), pd.ok_app(all, C, Tr.Ent.k(e), Tr.Ent.p(e), he), pd.rooted_app_all(r, all, C, hr))

def pd.rooted_go_app(A: List<&2, Tr.Ent>, +B: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +ra: {Tr.rooted.go(A, all) == True{} : Bool}, rb: {Tr.rooted.go(B, all) == True{} : Bool}) -> {Tr.rooted.go(List.append(&2, Tr.Ent, A, B), all) == True{} : Bool}:
  match A:
    case Nil{}:
      rb
    case +e <> +r:
      +he = Pt.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      +hr = Pt.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(r, all), ra)
      Pt.pt.and_t(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(List.append(&2, Tr.Ent, r, B), all), he, pd.rooted_go_app(r, B, all, hr, rb))

# the kind node of the layer above rest hangs under the root (no layer
# below) or the kind node of the layer below
def pd.parent_ok(rest: List<&2, Dr.Layer>, +C: List<&2, Tr.Ent>) -> {Tr.ok(List.append(&2, Tr.Ent, Dr.encode(rest), C), Dr.kind.key(List.length(&2, Dr.Layer, rest)), Dr.kind.parent(List.length(&2, Dr.Layer, rest))) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case l2 <> +r2:
      match l2:
        case Dr.Layer{+k2, +b2}:
          +m = List.length(&2, Dr.Layer, r2)
          +E2 = Dr.encode(r2)
          +x2 = {Tr.Ent{1n+Nat.double(m), Dr.kind.parent(m), k2} : Tr.Ent}
          +y2 = {Tr.Ent{2n+Nat.double(m), 1n+Nat.double(m), b2} : Tr.Ent}
          +X2 = {[x2, y2] : List<&2, Tr.Ent>}
          +hh = Pt.pt.has_app_l(List.append(&2, Tr.Ent, E2, X2), C, 1n+Nat.double(m), Pt.pt.has_app_r(E2, X2, 1n+Nat.double(m), Pt.pt.has_head(x2, [y2])))
          Pt.pt.and_t(Nat.is_lt(1n+Nat.double(m), 3n+Nat.double(m)), Bool.or(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m))), pd.lt_add2(1n+Nat.double(m)), Pt.pt.or_tr(Nat.is_eq(1n+Nat.double(m), 0n), Tr.has(List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E2, X2), C), 1n+Nat.double(m)), hh))

def pd.enc_rooted(s: List<&2, Dr.Layer>) -> {Tr.rooted(Dr.encode(s)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +E = Dr.encode(rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +X = {[x, y] : List<&2, Tr.Ent>}
          +T = List.append(&2, Tr.Ent, E, X)
          +ra = pd.rooted_app_all(E, E, X, pd.enc_rooted(rest))
          +hy = Pt.pt.and_t(Nat.is_lt(1n+Nat.double(n), 2n+Nat.double(n)), Bool.or(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n))), pd.lt_succ(1n+Nat.double(n)), Pt.pt.or_tr(Nat.is_eq(1n+Nat.double(n), 0n), Tr.has(T, 1n+Nat.double(n)), Pt.pt.has_app_r(E, X, 1n+Nat.double(n), Pt.pt.has_head(x, [y]))))
          +rb = Pt.pt.and_t(Tr.ok(T, 1n+Nat.double(n), Dr.kind.parent(n)), Bool.and(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}), pd.parent_ok(rest, X), Pt.pt.and_t(Tr.ok(T, 2n+Nat.double(n), 1n+Nat.double(n)), True{}, hy, {==}))
          pd.rooted_go_app(E, X, T, ra, rb)

def pd.dir_encode_sound(+s: List<&2, Dr.Layer>) -> {Tr.sound(Dr.encode(s)) == True{} : Bool}:
  Pt.pt.and_t(Tr.sorted(Dr.encode(s)), Tr.rooted(Dr.encode(s)), pd.enc_sorted(s), pd.enc_rooted(s))

# Resume and rewind
# -----------------

# decode reads the layers of encode(s) back onto acc, then goes on
def pd.dec_go(s: List<&2, Dr.Layer>, +B: List<&2, Tr.Ent>, +acc: List<&2, Dr.Layer>) -> {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), B), acc) == Dr.decode.go(B, List.append(&2, Dr.Layer, s, acc)) : List<&2, Dr.Layer>}:
  match s:
    case Nil{}:
      {==}
    case l <> +rest:
      match l:
        case Dr.Layer{+k, +b}:
          +n = List.length(&2, Dr.Layer, rest)
          +x = {Tr.Ent{1n+Nat.double(n), Dr.kind.parent(n), k} : Tr.Ent}
          +y = {Tr.Ent{2n+Nat.double(n), 1n+Nat.double(n), b} : Tr.Ent}
          +E = Dr.encode(rest)
          %Equal.sym(List<&2, Tr.Ent>, List.append(&2, Tr.Ent, List.append(&2, Tr.Ent, E, [x, y]), B), List.append(&2, Tr.Ent, E, x <> y <> B), pd.app_assoc(Tr.Ent, E, [x, y], B)) : {Dr.decode.go(_, acc) == Dr.decode.go(B, Dr.Layer{k, b} <> List.append(&2, Dr.Layer, rest, acc)) : List<&2, Dr.Layer>}
          pd.dec_go(rest, x <> y <> B, acc)

def pd.dir_resume_restores(+s: List<&2, Dr.Layer>) -> {Dr.decode(Dr.encode(s)) == s : List<&2, Dr.Layer>}:
  %pd.app_nil(Tr.Ent, Dr.encode(s)) : {Dr.decode.go(_, Nil{}) == s : List<&2, Dr.Layer>}
  %pd.app_nil(Dr.Layer, s) : {Dr.decode.go(List.append(&2, Tr.Ent, Dr.encode(s), Nil{}), Nil{}) == _ : List<&2, Dr.Layer>}
  pd.dec_go(s, Nil{}, Nil{})

def pd.dir_rewind_restores(+a: List<&2, Tr.Ent>, +s: List<&2, Dr.Layer>, good: {Tr.sound(a) == True{} : Bool}) -> {Dr.decode(Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))})) == s : List<&2, Dr.Layer>}:
  %Equal.sym(List<&2, Tr.Ent>, Tr.apply(a, Tr.Rewind{Tr.diff(a, Dr.encode(s))}), Dr.encode(s), Pt.rewind_reaches(a, Dr.encode(s), good, pd.dir_encode_sound(s))) : {Dr.decode(_) == s : List<&2, Dr.Layer>}
  pd.dir_resume_restores(s)

# The bound
# ---------

def pd.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pd.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def pd.le_zero(q: Nat) -> {Nat.is_le(0n, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def pd.le_pred(x: Nat, cap: Nat, h: {Nat.is_le(1n+x, cap) == True{} : Bool}) -> {Nat.is_le(x, cap) == True{} : Bool}:
  match x cap:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Pt.pt.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pd.le_pred(p, q, h)

def pd.lt_le(x: Nat, cap: Nat, h: {Nat.is_lt(x, cap) == True{} : Bool}) -> {Nat.is_le(1n+x, cap) == True{} : Bool}:
  match x cap:
    case 0n 0n:
      Pt.pt.absurdF({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      pd.le_zero(q)
    case 1n+p 0n:
      Pt.pt.absurdF({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      pd.lt_le(p, q, h)

# one more layer above, one fewer below
def pd.shift(+above: Nat, +r: Nat, +cap: Nat, h: {Nat.is_le(Nat.add(above, 1n+r), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+above, r), cap) == True{} : Bool}:
  %pd.add_succ(above, r) : {Nat.is_le(_, cap) == True{} : Bool}
  h

# a layer put back on the stack below it
def pd.under_ok(+l: Dr.Layer, d: Dr.Dec, +above: Nat, +cap: Nat, ih: {Nat.is_le(Nat.add(1n+above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.under(l, d)))), cap) == True{} : Bool}:
  match d:
    case Dr.Dec{o, +s}:
      +r = List.length(&2, Dr.Layer, s)
      %Equal.sym(Nat, Nat.add(above, 1n+r), 1n+Nat.add(above, r), pd.add_succ(above, r)) : {Nat.is_le(_, cap) == True{} : Bool}
      ih

# a Stack with room adds one layer to a stack with room for it
def pd.push_ok(+cap: Nat, +above: Nat, +rest: List<&2, Dr.Layer>, room: Bool, er: {Nat.is_lt(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == room : Bool}, +l: Dr.Layer, +n: Dr.Layer, h: {Nat.is_le(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.push.at(room, l, n, rest)))), cap) == True{} : Bool}:
  match room:
    case True{}:
      +r = List.length(&2, Dr.Layer, rest)
      %Equal.sym(Nat, Nat.add(above, 2n+r), 1n+Nat.add(above, 1n+r), pd.add_succ(above, 1n+r)) : {Nat.is_le(_, cap) == True{} : Bool}
      pd.lt_le(Nat.add(above, 1n+r), cap, er)
    case False{}:
      h

def pd.pick_ok(v: Dr.Verdict, +l: Dr.Layer, +rest: List<&2, Dr.Layer>, +cap: Nat, +above: Nat, d: Dr.Dec, +h: {Nat.is_le(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap) == True{} : Bool}, ih: {Nat.is_le(Nat.add(1n+above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.pick(v, l, rest, cap, above, d)))), cap) == True{} : Bool}:
  match v:
    case Dr.Defer{}:
      pd.under_ok(l, d, above, cap, ih)
    case Dr.Again{}:
      match l:
        case Dr.Layer{k, b}:
          match b:
            case 0n:
              h
            case 1n+c:
              h
    case Dr.Yield{}:
      h
    case Dr.Stack{n}:
      match l:
        case Dr.Layer{+k, b}:
          match b:
            case 0n:
              h
            case 1n+c:
              pd.push_ok(cap, above, rest, Nat.is_lt(Nat.add(above, 1n+List.length(&2, Dr.Layer, rest)), cap), {==}, Dr.Layer{k, c}, n, h)
    case Dr.Leave{}:
      pd.le_pred(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(d))), cap, ih)
    case Dr.Abort{}:
      h

# a decision under `above` layers keeps above + len(stack) within cap
def pd.go_bounded(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, +above: Nat, +h: {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, s)), cap) == True{} : Bool}) -> {Nat.is_le(Nat.add(above, List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide.go(s, vs, cap, above)))), cap) == True{} : Bool}:
  match s:
    case Nil{}:
      h
    case +l <> +rest:
      match vs:
        case Nil{}:
          pd.under_ok(l, Dr.decide.go(rest, Nil{}, cap, 1n+above), above, cap, pd.go_bounded(rest, Nil{}, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h)))
        case +v <> +vr:
          pd.pick_ok(v, l, rest, cap, above, Dr.decide.go(rest, vr, cap, 1n+above), h, pd.go_bounded(rest, vr, cap, 1n+above, pd.shift(above, List.length(&2, Dr.Layer, rest), cap, h)))

def pd.dir_stack_bounded(+s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +cap: Nat, fits: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(Dr.decide(s, vs, cap))), cap) == True{} : Bool}:
  pd.go_bounded(s, vs, cap, 0n, fits)

def pd.cont_bounded(n: Nat, +s: List<&2, Dr.Layer>, +cap: Nat, h: {Nat.is_le(List.length(&2, Dr.Layer, s), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.cont(n, s))), cap) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      h

def pd.after_bounded(+n: Nat, d: Dr.Dec, +cap: Nat, h: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Dec.stack(d)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.after(n, d))), cap) == True{} : Bool}:
  match d:
    case Dr.Dec{o, +s}:
      match o:
        case Dr.Cont{}:
          pd.cont_bounded(n, s, cap, h)
        case Dr.Hand{}:
          h
        case Dr.Failed{}:
          h

# one loop step keeps the stack within cap
def pd.tick_bounded(+cap: Nat, l: Dr.Loop, +vs: List<&2, Dr.Verdict>, h: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.tick(cap, l, vs))), cap) == True{} : Bool}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case None{}:
          pd.after_bounded(n, Dr.decide(s, vs, cap), cap, pd.dir_stack_bounded(s, vs, cap, h))
        case Some{x}:
          h

def pd.dir_loop_stack_bounded(vss: List<&2, List<&2, Dr.Verdict>>, +cap: Nat, +l: Dr.Loop, fits: {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(l)), cap) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Dr.Layer, Dr.Loop.stack(Dr.run(vss, cap, l))), cap) == True{} : Bool}:
  match vss:
    case Nil{}:
      fits
    case +vs <> rest:
      pd.dir_loop_stack_bounded(rest, cap, Dr.tick(cap, l, vs), pd.tick_bounded(cap, l, vs, fits))
