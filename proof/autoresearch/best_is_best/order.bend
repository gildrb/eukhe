# eukhe: lemmas of LAW best_is_best (prefix ah.): the order of the kept
# metrics of a segment (each kept metric better than every earlier one),
# kept by rows that keep nothing, by a keep that beats every kept metric,
# and by a flag; the segment bound of the rows, kept by every step.

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../base/history.bend as AH

# The predicates
# --------------

def ah.isnone(k: Maybe<&2, ArD.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      False{}

# no row of rs is kept in segment seg
def ah.nk(rs: List<&2, ArS.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(ah.isnone(ArS.kept(r, seg)), ah.nk(t, seg))

# a kept metric k is better than y (or there is none)
def ah.bt(+d: ArS.Dir, +y: ArD.Dec, k: Maybe<&2, ArD.Dec>) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{x}:
      ArS.better(d, x, y)

# every kept metric of rs is better than y
def ah.allb(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg))

def ah.above(+d: ArS.Dir, k: Maybe<&2, ArD.Dec>, rs: List<&2, ArS.Row>, +seg: Nat) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{y}:
      ah.allb(d, y, rs, seg)

# every kept metric of rs is better than every earlier one
def ah.ord(+d: ArS.Dir, rs: List<&2, ArS.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> +t:
      Bool.and(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg))

def ah.below.at(r: ArS.Row, +seg: Nat) -> Bool:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      Nat.is_le(sg, seg)

# every row of rs is of segment seg or an earlier one
def ah.below(rs: List<&2, ArS.Row>, +seg: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      Bool.and(ah.below.at(r, seg), ah.below(t, seg))

def ah.fst(p: List<&2, ArS.Row> & Bool) -> List<&2, ArS.Row>:
  (a, b) = p
  a

# Nat facts
# ---------

def ah.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      ah.le_refl(k)

def ah.le_up(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      AH.ah.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      ah.le_up(p, q, h)

def ah.le_ne(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_eq(a, 1n+b) == False{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      AH.ah.absurd({Nat.is_eq(1n+p, 1n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      ah.le_ne(p, q, h)

# Kept metrics of single rows
# ---------------------------

def ah.kof2(b1: Bool, b2: Bool, -m: Maybe<&2, ArD.Dec>) -> {ArS.kept.of(Bool.and(b1, Bool.and(b2, False{})), m) == None{} : Maybe<&2, ArD.Dec>}:
  match b1:
    case True{}:
      AH.ah.kof(b2, m)
    case False{}:
      {==}

# a flagged row keeps nothing
def ah.kept_set(r: ArS.Row, +seg: Nat) -> {ArS.kept(ArP.flag.set(r), seg) == None{} : Maybe<&2, ArD.Dec>}:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      ah.kof2(Nat.is_eq(sg, seg), ArS.kept.st(st), m)

def ah.nk1(b: Bool, -m: Maybe<&2, ArD.Dec>) -> {Bool.and(ah.isnone(ArS.kept.of(Bool.and(b, False{}), m)), True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ah.nk_ab(+m: String, +sg: Nat, p: Maybe<&2, ArS.Pend>, +seg: Nat) -> {ah.nk(ArS.abandon(m, sg, p), seg) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          ah.nk1(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))

def ah.nk_row(+m: String, +sg: Nat, p: ArS.Pend, st: ArS.Status, -desc: String, +seg: Nat, h: {ArS.kept.st(Some{st}) == False{} : Bool}) -> {ah.nk([ArS.row(m, sg, p, Some{st}, desc)], seg) == True{} : Bool}:
  match p:
    case ArS.Pend{id, kvs, fin}:
      match st:
        case ArS.Keep{}:
          AH.ah.absurdT({ah.nk([ArS.row(m, sg, ArS.Pend{id, kvs, fin}, Some{ArS.Keep{}}, desc)], seg) == True{} : Bool}, h)
        case ArS.Discard{}:
          ah.nk1(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))
        case ArS.Crash{}:
          ah.nk1(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))
        case ArS.Checks{}:
          ah.nk1(Nat.is_eq(sg, seg), ArS.lookup(kvs, m))

# Rows that keep nothing
# ----------------------

def ah.none_above(+d: ArS.Dir, k: Maybe<&2, ArD.Dec>, -t: List<&2, ArS.Row>, +seg: Nat, h: {ah.isnone(k) == True{} : Bool}) -> {ah.above(d, k, t, seg) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{x}:
      AH.ah.absurd({ah.above(d, Some{x}, t, seg) == True{} : Bool}, h)

def ah.none_bt(+d: ArS.Dir, +y: ArD.Dec, k: Maybe<&2, ArD.Dec>, h: {ah.isnone(k) == True{} : Bool}) -> {ah.bt(d, y, k) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{x}:
      AH.ah.absurd({ah.bt(d, y, Some{x}) == True{} : Bool}, h)

def ah.nk_ord(+d: ArS.Dir, rs: List<&2, ArS.Row>, +seg: Nat, +h: {ah.nk(rs, seg) == True{} : Bool}) -> {ah.ord(d, rs, seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      AH.ah.and_i(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), ah.none_above(d, ArS.kept(r, seg), t, seg, AH.ah.and_l(ah.isnone(ArS.kept(r, seg)), ah.nk(t, seg), h)), ah.nk_ord(d, t, seg, AH.ah.and_r(ah.isnone(ArS.kept(r, seg)), ah.nk(t, seg), h)))

def ah.allb_nk(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +seg: Nat, +h: {ah.nk(rs, seg) == True{} : Bool}) -> {ah.allb(d, y, rs, seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      AH.ah.and_i(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), ah.none_bt(d, y, ArS.kept(r, seg), AH.ah.and_l(ah.isnone(ArS.kept(r, seg)), ah.nk(t, seg), h)), ah.allb_nk(d, y, t, seg, AH.ah.and_r(ah.isnone(ArS.kept(r, seg)), ah.nk(t, seg), h)))

def ah.allb_snoc(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, +h1: {ah.allb(d, y, rs, seg) == True{} : Bool}, +h2: {ah.allb(d, y, ys, seg) == True{} : Bool}) -> {ah.allb(d, y, ArS.snoc(rs, ys), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      h2
    case +r <> +t:
      AH.ah.and_i(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, ArS.snoc(t, ys), seg), AH.ah.and_l(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), h1), ah.allb_snoc(d, y, t, ys, seg, AH.ah.and_r(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), h1), h2))

def ah.above_snoc_nk(+d: ArS.Dir, k: Maybe<&2, ArD.Dec>, +t: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, h: {ah.above(d, k, t, seg) == True{} : Bool}, hn: {ah.nk(ys, seg) == True{} : Bool}) -> {ah.above(d, k, ArS.snoc(t, ys), seg) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{+y}:
      ah.allb_snoc(d, y, t, ys, seg, h, ah.allb_nk(d, y, ys, seg, hn))

# rows that keep nothing keep the order
def ah.ord_snoc_nk(+d: ArS.Dir, rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, +h: {ah.ord(d, rs, seg) == True{} : Bool}, +hn: {ah.nk(ys, seg) == True{} : Bool}) -> {ah.ord(d, ArS.snoc(rs, ys), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      ah.nk_ord(d, ys, seg, hn)
    case +r <> +t:
      AH.ah.and_i(ah.above(d, ArS.kept(r, seg), ArS.snoc(t, ys), seg), ah.ord(d, ArS.snoc(t, ys), seg), ah.above_snoc_nk(d, ArS.kept(r, seg), t, ys, seg, AH.ah.and_l(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), h), hn), ah.ord_snoc_nk(d, t, ys, seg, AH.ah.and_r(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), h), hn))

# A keep
# ------

def ah.allb1(+d: ArS.Dir, +y: ArD.Dec, -x: ArD.Dec, -r: ArS.Row, -seg: Nat, hk: {ArS.kept(r, seg) == Some{x} : Maybe<&2, ArD.Dec>}, hb: {ArS.better(d, x, y) == True{} : Bool}) -> {ah.allb(d, y, [r], seg) == True{} : Bool}:
  %Equal.sym(Maybe<&2, ArD.Dec>, ArS.kept(r, seg), Some{x}, hk) : {Bool.and(ah.bt(d, y, _), True{}) == True{} : Bool}
  %Equal.sym(Bool, ArS.better(d, x, y), True{}, hb) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def ah.above_keep(+d: ArS.Dir, +x: ArD.Dec, k: Maybe<&2, ArD.Dec>, +t: List<&2, ArS.Row>, +r: ArS.Row, +seg: Nat, ha: {ah.above(d, k, t, seg) == True{} : Bool}, hb: {ArS.beats.at(d, x, k) == True{} : Bool}, hk: {ArS.kept(r, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ah.above(d, k, ArS.snoc(t, [r]), seg) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{+y}:
      ah.allb_snoc(d, y, t, [r], seg, ha, ah.allb1(d, y, x, r, seg, hk, hb))

# a keep that beats every kept metric keeps the order
def ah.ord_snoc_keep(+d: ArS.Dir, +x: ArD.Dec, rs: List<&2, ArS.Row>, +r: ArS.Row, +seg: Nat, +h: {ah.ord(d, rs, seg) == True{} : Bool}, +hb: {ArS.beats(d, x, rs, seg) == True{} : Bool}, +hk: {ArS.kept(r, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ah.ord(d, ArS.snoc(rs, [r]), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      %Equal.sym(Maybe<&2, ArD.Dec>, ArS.kept(r, seg), Some{x}, hk) : {Bool.and(ah.above(d, _, Nil{}, seg), True{}) == True{} : Bool}
      {==}
    case +r0 <> +t:
      AH.ah.and_i(ah.above(d, ArS.kept(r0, seg), ArS.snoc(t, [r]), seg), ah.ord(d, ArS.snoc(t, [r]), seg), ah.above_keep(d, x, ArS.kept(r0, seg), t, r, seg, AH.ah.and_l(ah.above(d, ArS.kept(r0, seg), t, seg), ah.ord(d, t, seg), h), AH.ah.and_l(ArS.beats.at(d, x, ArS.kept(r0, seg)), ArS.beats(d, x, t, seg), hb), hk), ah.ord_snoc_keep(d, x, t, r, seg, AH.ah.and_r(ah.above(d, ArS.kept(r0, seg), t, seg), ah.ord(d, t, seg), h), AH.ah.and_r(ArS.beats.at(d, x, ArS.kept(r0, seg)), ArS.beats(d, x, t, seg), hb), hk))

# A flag
# ------

def ah.fa_at(b: Bool, +d: ArS.Dir, +y: ArD.Dec, +r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +seg: Nat, +h: {ah.allb(d, y, r <> t, seg) == True{} : Bool}, hq: {ah.allb(d, y, ah.fst(q), seg) == True{} : Bool}) -> {ah.allb(d, y, ah.fst(ArP.flag.at(b, r, t, q)), seg) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, ArD.Dec>, ArS.kept(ArP.flag.set(r), seg), None{}, ah.kept_set(r, seg)) : {Bool.and(ah.bt(d, y, _), ah.allb(d, y, t, seg)) == True{} : Bool}
      AH.ah.and_r(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), h)
    case False{}:
      (a, f) = q
      AH.ah.and_i(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, a, seg), AH.ah.and_l(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), h), hq)

# a flag keeps every kept metric better than y
def ah.flag_allb(+d: ArS.Dir, +y: ArD.Dec, rs: List<&2, ArS.Row>, +n: Nat, +seg: Nat, +h: {ah.allb(d, y, rs, seg) == True{} : Bool}) -> {ah.allb(d, y, ah.fst(ArP.flag.rows(rs, n)), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.fa_at(ArP.flag.hit(r, n), d, y, r, t, ArP.flag.rows(t, n), seg, h, ah.flag_allb(d, y, t, n, seg, AH.ah.and_r(ah.bt(d, y, ArS.kept(r, seg)), ah.allb(d, y, t, seg), h)))

def ah.flag_above(+d: ArS.Dir, k: Maybe<&2, ArD.Dec>, +t: List<&2, ArS.Row>, +n: Nat, +seg: Nat, h: {ah.above(d, k, t, seg) == True{} : Bool}) -> {ah.above(d, k, ah.fst(ArP.flag.rows(t, n)), seg) == True{} : Bool}:
  match k:
    case None{}:
      {==}
    case Some{+y}:
      ah.flag_allb(d, y, t, n, seg, h)

def ah.fo_at(b: Bool, +d: ArS.Dir, +r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +seg: Nat, +h: {ah.ord(d, r <> t, seg) == True{} : Bool}, hq: {ah.ord(d, ah.fst(q), seg) == True{} : Bool}, ha: {ah.above(d, ArS.kept(r, seg), ah.fst(q), seg) == True{} : Bool}) -> {ah.ord(d, ah.fst(ArP.flag.at(b, r, t, q)), seg) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, ArD.Dec>, ArS.kept(ArP.flag.set(r), seg), None{}, ah.kept_set(r, seg)) : {Bool.and(ah.above(d, _, t, seg), ah.ord(d, t, seg)) == True{} : Bool}
      AH.ah.and_r(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), h)
    case False{}:
      (a, f) = q
      AH.ah.and_i(ah.above(d, ArS.kept(r, seg), a, seg), ah.ord(d, a, seg), ha, hq)

# a flag keeps the order
def ah.flag_ord(+d: ArS.Dir, rs: List<&2, ArS.Row>, +n: Nat, +seg: Nat, +h: {ah.ord(d, rs, seg) == True{} : Bool}) -> {ah.ord(d, ah.fst(ArP.flag.rows(rs, n)), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.fo_at(ArP.flag.hit(r, n), d, r, t, ArP.flag.rows(t, n), seg, h, ah.flag_ord(d, t, n, seg, AH.ah.and_r(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), h)), ah.flag_above(d, ArS.kept(r, seg), t, n, seg, AH.ah.and_l(ah.above(d, ArS.kept(r, seg), t, seg), ah.ord(d, t, seg), h)))

def ah.fb_at(b: Bool, +r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +seg: Nat, +h: {ah.below(r <> t, seg) == True{} : Bool}, hq: {ah.below(ah.fst(q), seg) == True{} : Bool}) -> {ah.below(ah.fst(ArP.flag.at(b, r, t, q)), seg) == True{} : Bool}:
  match b:
    case True{}:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          h
    case False{}:
      (a, f) = q
      AH.ah.and_i(ah.below.at(r, seg), ah.below(a, seg), AH.ah.and_l(ah.below.at(r, seg), ah.below(t, seg), h), hq)

# a flag keeps the segments
def ah.flag_below(rs: List<&2, ArS.Row>, +n: Nat, +seg: Nat, +h: {ah.below(rs, seg) == True{} : Bool}) -> {ah.below(ah.fst(ArP.flag.rows(rs, n)), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.fb_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), seg, h, ah.flag_below(t, n, seg, AH.ah.and_r(ah.below.at(r, seg), ah.below(t, seg), h)))

# The segment bound
# -----------------

def ah.below_snoc(rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, +h1: {ah.below(rs, seg) == True{} : Bool}, +h2: {ah.below(ys, seg) == True{} : Bool}) -> {ah.below(ArS.snoc(rs, ys), seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      h2
    case +r <> +t:
      AH.ah.and_i(ah.below.at(r, seg), ah.below(ArS.snoc(t, ys), seg), AH.ah.and_l(ah.below.at(r, seg), ah.below(t, seg), h1), ah.below_snoc(t, ys, seg, AH.ah.and_r(ah.below.at(r, seg), ah.below(t, seg), h1), h2))

def ah.below_ab(-m: String, +seg: Nat, p: Maybe<&2, ArS.Pend>) -> {ah.below(ArS.abandon(m, seg, p), seg) == True{} : Bool}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          %Equal.sym(Bool, Nat.is_le(seg, seg), True{}, ah.le_refl(seg)) : {Bool.and(_, True{}) == True{} : Bool}
          {==}

def ah.below_row(-m: String, +seg: Nat, p: ArS.Pend, -st: Maybe<&2, ArS.Status>, -desc: String) -> {ah.below([ArS.row(m, seg, p, st, desc)], seg) == True{} : Bool}:
  match p:
    case ArS.Pend{id, kvs, fin}:
      %Equal.sym(Bool, Nat.is_le(seg, seg), True{}, ah.le_refl(seg)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def ah.below_up(rs: List<&2, ArS.Row>, +seg: Nat, +h: {ah.below(rs, seg) == True{} : Bool}) -> {ah.below(rs, 1n+seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case ArS.Row{i, +sg, st, m, ms, ps, fn, fl, desc}:
          AH.ah.and_i(Nat.is_le(sg, 1n+seg), ah.below(t, 1n+seg), ah.le_up(sg, seg, AH.ah.and_l(Nat.is_le(sg, seg), ah.below(t, seg), h)), ah.below_up(t, seg, AH.ah.and_r(Nat.is_le(sg, seg), ah.below(t, seg), h)))

# no row of an earlier segment is kept in the next one
def ah.below_nk(rs: List<&2, ArS.Row>, +seg: Nat, +h: {ah.below(rs, seg) == True{} : Bool}) -> {ah.nk(rs, 1n+seg) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case ArS.Row{i, +sg, st, m, ms, ps, fn, fl, desc}:
          %Equal.sym(Bool, Nat.is_eq(sg, 1n+seg), False{}, ah.le_ne(sg, seg, AH.ah.and_l(Nat.is_le(sg, seg), ah.below(t, seg), h))) : {Bool.and(ah.isnone(ArS.kept.of(Bool.and(_, Bool.and(ArS.kept.st(st), Bool.not(fl))), m)), ah.nk(t, 1n+seg)) == True{} : Bool}
          ah.below_nk(t, seg, AH.ah.and_r(Nat.is_le(sg, seg), ah.below(t, seg), h))

# Directions
# ----------

def ah.dir_eq_sound(a: ArS.Dir, b: ArS.Dir, h: {ArP.dir_eq(a, b) == True{} : Bool}) -> {a == b : ArS.Dir}:
  match a b:
    case ArS.Lower{} ArS.Lower{}:
      {==}
    case ArS.Lower{} ArS.Higher{}:
      AH.ah.absurd({ArS.Lower{} == ArS.Higher{} : ArS.Dir}, h)
    case ArS.Higher{} ArS.Lower{}:
      AH.ah.absurd({ArS.Higher{} == ArS.Lower{} : ArS.Dir}, h)
    case ArS.Higher{} ArS.Higher{}:
      {==}

# an init on the same segment keeps the direction
def ah.same_dir(+o: ArS.Cfg, +c: ArS.Cfg, h: {ArP.same(o, c) == True{} : Bool}) -> {ArS.Cfg.dir(o) == ArS.Cfg.dir(c) : ArS.Dir}:
  ah.dir_eq_sound(ArS.Cfg.dir(o), ArS.Cfg.dir(c), AH.ah.and_r(String.eq(ArS.Cfg.metric(o), ArS.Cfg.metric(c)), ArP.dir_eq(ArS.Cfg.dir(o), ArS.Cfg.dir(c)), h))
