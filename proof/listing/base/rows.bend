# eukhe: lemmas of area listing: the rows and their sort
#
# Ls.rows makes the row of each listed entry (rows.go: place k for the
# k-th entry), then sorts them by insertion (Ls.sort, Ls.ins). Insertion
# keeps the count of every place (lr.count_ins, lr.count_sort); it keeps
# the rows in order when every place is fresh (lr.sorted_ins, by the
# strict order of proof/listing/base/order.bend). rows.go makes one row
# per listed entry (lr.count_go), at places from k on (lr.below_go).

import Base
import ../../../bend/staging.bend as Sg
import ../../../bend/listing.bend as Ls
import ../../../laws/listing.bend as Listing
import ./order.bend as LO
import ./scan.bend as LS

# Bool and Nat
# ------------

def lr.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def lr.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def lr.and_swap(a: Bool, +b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Bool, Bool.and(b, False{}), False{}, lr.and_f(b))

def lr.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LO.lo.ft({False{} == True{} : Bool}, e)

def lr.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LO.lo.ft({b == True{} : Bool}, e)

def lr.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def lr.or_false(a: Bool, -b: Bool, e: {Bool.or(a, b) == True{} : Bool}, f: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), e)

# a place below k is no place k or above
def lr.lt_eq(i: Nat, k: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Nat.is_eq(k, i) == False{} : Bool}:
  match i k:
    case 0n 0n:
      LO.lo.ft({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LO.lo.ft({Nat.is_eq(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      lr.lt_eq(p, q, h)

def lr.lt_succ(i: Nat, k: Nat, h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Nat.is_lt(i, 1n+k) == True{} : Bool}:
  match i k:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LO.lo.ft({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lr.lt_succ(p, q, h)

def lr.lt_self(k: Nat) -> {Nat.is_lt(k, 1n+k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      lr.lt_self(p)

# a place not below k + 1 is not k and not below k
def lr.ge_succ_eq(i: Nat, k: Nat, h: {Nat.is_lt(i, 1n+k) == False{} : Bool}) -> {Nat.is_eq(k, i) == False{} : Bool}:
  match i k:
    case 0n 0n:
      LO.lo.tf({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      LO.lo.tf({Nat.is_eq(1n+q, 0n) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lr.ge_succ_eq(p, q, h)

def lr.ge_succ_lt(i: Nat, k: Nat, h: {Nat.is_lt(i, 1n+k) == False{} : Bool}) -> {Nat.is_lt(i, k) == False{} : Bool}:
  match i k:
    case 0n 0n:
      LO.lo.tf({Nat.is_lt(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      LO.lo.tf({Nat.is_lt(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lr.ge_succ_lt(p, q, h)

def lr.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      lr.eq_refl(p)

# Places and counts
# -----------------

# how many entries of os from place k on are listed at the place i below k
def lr.below(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat, +i: Nat, +h: {Nat.is_lt(i, k) == True{} : Bool}) -> {Listing.sp_count_listed(os, all, k, i) == 0n : Nat}:
  match os:
    case Nil{}:
      {==}
    case o <> rest:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, lr.lt_eq(i, k, h)) : {Nat.add(Listing.sp_bit(Bool.and(_, Listing.sp_listed(o, all))), Listing.sp_count_listed(rest, all, 1n+k, i)) == 0n : Nat}
      lr.below(rest, all, 1n+k, i, lr.lt_succ(i, k, h))

def lr.bit_swap(a: Bool, b: Bool, -c: Nat) -> {Nat.add(Listing.sp_bit(a), Nat.add(Listing.sp_bit(b), c)) == Nat.add(Listing.sp_bit(b), Nat.add(Listing.sp_bit(a), c)) : Nat}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def lr.count_ins(ys: List<&2, Ls.Row>, +ix: Nat, +px: Ls.Pick, +tx: Sg.Time, h: Bool, +i: Nat) -> {Listing.sp_count(i, Listing.sp_ats(Ls.ins(ys, Ls.Row{ix, px, tx}, h))) == Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Listing.sp_count(i, Listing.sp_ats(ys))) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Ls.Row{+iy, +py, +ty} <> +rest:
      match h:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Nat, Listing.sp_count(i, Listing.sp_ats(Ls.ins(rest, Ls.Row{ix, px, tx}, Ls.ins.head(Ls.Row{ix, px, tx}, rest)))), Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Listing.sp_count(i, Listing.sp_ats(rest))), lr.count_ins(rest, ix, px, tx, Ls.ins.head(Ls.Row{ix, px, tx}, rest), i)) : {Nat.add(Listing.sp_bit(Nat.is_eq(iy, i)), _) == Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Nat.add(Listing.sp_bit(Nat.is_eq(iy, i)), Listing.sp_count(i, Listing.sp_ats(rest)))) : Nat}
          lr.bit_swap(Nat.is_eq(iy, i), Nat.is_eq(ix, i), Listing.sp_count(i, Listing.sp_ats(rest)))

def lr.count_sort(xs: List<&2, Ls.Row>, +i: Nat) -> {Listing.sp_count(i, Listing.sp_ats(Ls.sort(xs))) == Listing.sp_count(i, Listing.sp_ats(xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Ls.Row{+ix, +px, +tx} <> +rest:
      %Equal.sym(Nat, Listing.sp_count(i, Listing.sp_ats(Ls.ins(Ls.sort(rest), Ls.Row{ix, px, tx}, Ls.ins.head(Ls.Row{ix, px, tx}, Ls.sort(rest))))), Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Listing.sp_count(i, Listing.sp_ats(Ls.sort(rest)))), lr.count_ins(Ls.sort(rest), ix, px, tx, Ls.ins.head(Ls.Row{ix, px, tx}, Ls.sort(rest)), i)) : {_ == Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Listing.sp_count(i, Listing.sp_ats(rest))) : Nat}
      %Equal.sym(Nat, Listing.sp_count(i, Listing.sp_ats(Ls.sort(rest))), Listing.sp_count(i, Listing.sp_ats(rest)), lr.count_sort(rest, i)) : {Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), _) == Nat.add(Listing.sp_bit(Nat.is_eq(ix, i)), Listing.sp_count(i, Listing.sp_ats(rest))) : Nat}
      {==}

# The rows of the entries
# -----------------------

# what the row of an entry says: none, when it is not listed; else one at
# its place
def lr.MRow(m: Maybe<&2, Ls.Row>, k: Nat, b: Bool) -> Type:
  match m:
    case None{}:
      {b == False{} : Bool}
    case Some{r}:
      {LO.lo.at(r) == k : Nat} & {b == True{} : Bool}

def lr.rt(+p: Ls.Pick, +k: Nat, ts: List<&2, Sg.Time>) -> lr.MRow(Ls.row.times(p, k, ts), k, Listing.sp_some(ts)):
  match ts:
    case Nil{}:
      {==}
    case t <> rest:
      ({==}, {==})

def lr.rc(ok: Bool, +p: Ls.Pick, +k: Nat, ts: List<&2, Sg.Time>) -> lr.MRow(Ls.row.cwd(ok, p, k, ts), k, Bool.and(ok, Listing.sp_some(ts))):
  match ok:
    case True{}:
      lr.rt(p, k, ts)
    case False{}:
      {==}

def lr.rp(p: Ls.Pick, +k: Nat, ok: Bool, ts: List<&2, Sg.Time>) -> lr.MRow(Ls.row.pick(p, k, ok, ts), k, Bool.and(Bool.not(Listing.sp_skip(p)), Bool.and(ok, Listing.sp_some(ts)))):
  match p:
    case Ls.PSkip{}:
      {==}
    case Ls.PStore{s}:
      lr.rc(ok, Ls.PStore{s}, k, ts)
    case Ls.PLegacy{s}:
      lr.rc(ok, Ls.PLegacy{s}, k, ts)

def lr.cwd(c: Maybe<&2, String>) -> {Ls.cwd_ok(c) == Listing.sp_cwd(c) : Bool}:
  match c:
    case None{}:
      {==}
    case Some{s}:
      {==}

def lr.row_rel(o: Ls.Obs, +all: List<&2, Sg.Seen>, +k: Nat) -> lr.MRow(Ls.row(o, all, k), k, Listing.sp_listed(o, all)):
  match o:
    case Ls.Obs{+e, +c, +ts}:
      %LS.ls.pick(e, all) : lr.MRow(Ls.row(Ls.Obs{e, c, ts}, all, k), k, Bool.and(Bool.not(Listing.sp_skip(_)), Bool.and(Listing.sp_cwd(c), Listing.sp_some(ts))))
      %lr.cwd(c) : lr.MRow(Ls.row(Ls.Obs{e, c, ts}, all, k), k, Bool.and(Bool.not(Listing.sp_skip(Ls.pick(e, all))), Bool.and(_, Listing.sp_some(ts))))
      lr.rp(Ls.pick(e, all), k, Ls.cwd_ok(c), ts)

def lr.put_count(m: Maybe<&2, Ls.Row>, -R: List<&2, Ls.Row>, +k: Nat, +i: Nat, -b: Bool, rel: lr.MRow(m, k, b)) -> {Listing.sp_count(i, Listing.sp_ats(Ls.row.put(m, R))) == Nat.add(Listing.sp_bit(Bool.and(Nat.is_eq(k, i), b)), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}:
  match m:
    case None{}:
      %Equal.sym(Bool, b, False{}, rel) : {Listing.sp_count(i, Listing.sp_ats(R)) == Nat.add(Listing.sp_bit(Bool.and(Nat.is_eq(k, i), _)), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}
      %Equal.sym(Bool, Bool.and(Nat.is_eq(k, i), False{}), False{}, lr.and_f(Nat.is_eq(k, i))) : {Listing.sp_count(i, Listing.sp_ats(R)) == Nat.add(Listing.sp_bit(_), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}
      {==}
    case Some{r}:
      match r:
        case Ls.Row{ir, pr, tr}:
          (ea, eb) = rel
          %Equal.sym(Bool, b, True{}, eb) : {Listing.sp_count(i, Listing.sp_ats(Ls.row.put(Some{Ls.Row{ir, pr, tr}}, R))) == Nat.add(Listing.sp_bit(Bool.and(Nat.is_eq(k, i), _)), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}
          %Equal.sym(Bool, Bool.and(Nat.is_eq(k, i), True{}), Nat.is_eq(k, i), lr.and_t(Nat.is_eq(k, i))) : {Listing.sp_count(i, Listing.sp_ats(Ls.row.put(Some{Ls.Row{ir, pr, tr}}, R))) == Nat.add(Listing.sp_bit(_), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}
          %ea : {Listing.sp_count(i, Listing.sp_ats(Ls.row.put(Some{Ls.Row{ir, pr, tr}}, R))) == Nat.add(Listing.sp_bit(Nat.is_eq(_, i)), Listing.sp_count(i, Listing.sp_ats(R))) : Nat}
          {==}

# one row per listed entry, at its place
def lr.count_go(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat, +i: Nat) -> {Listing.sp_count(i, Listing.sp_ats(Ls.rows.go(os, all, k))) == Listing.sp_count_listed(os, all, k, i) : Nat}:
  match os:
    case Nil{}:
      {==}
    case +o <> +rest:
      %lr.count_go(rest, all, 1n+k, i) : {Listing.sp_count(i, Listing.sp_ats(Ls.rows.go(o <> rest, all, k))) == Nat.add(Listing.sp_bit(Bool.and(Nat.is_eq(k, i), Listing.sp_listed(o, all))), _) : Nat}
      lr.put_count(Ls.row(o, all, k), Ls.rows.go(rest, all, 1n+k), k, i, Listing.sp_listed(o, all), lr.row_rel(o, all, k))

# The sort keeps the rows in order
# --------------------------------

# no place of a row comes again later
def lr.Dist(xs: List<&2, Ls.Row>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> +rest:
      match x:
        case Ls.Row{+ix, px, tx}:
          Bool.and(Nat.is_eq(Listing.sp_count(ix, Listing.sp_ats(rest)), 0n), lr.Dist(rest))

def lr.is_eq_zero(c: Nat, e: {Nat.is_eq(c, 0n) == True{} : Bool}) -> {c == 0n : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      LO.lo.ft({1n+p == 0n : Nat}, e)

def lr.abz_b(b: Bool, -n: Nat, e: {Nat.add(Listing.sp_bit(b), n) == 0n : Nat}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LO.lo.gt_eq({True{} == False{} : Bool}, Equal.cong(Nat, Cmp, m => Nat.cmp(m, 0n), 1n+n, 0n, e))
    case False{}:
      {==}

def lr.abz_n(b: Bool, -n: Nat, e: {Nat.add(Listing.sp_bit(b), n) == 0n : Nat}) -> {n == 0n : Nat}:
  match b:
    case True{}:
      LO.lo.gt_eq({n == 0n : Nat}, Equal.cong(Nat, Cmp, m => Nat.cmp(m, 0n), 1n+n, 0n, e))
    case False{}:
      e

def lr.sb_fr(+a: Ls.Row, +b: Ls.Row, e: {Listing.sp_before(a, b) == True{} : Bool}) -> {LO.lo.Fr(a, b) == True{} : Bool}:
  Equal.trans(Bool, LO.lo.Fr(a, b), Listing.sp_before(a, b), True{}, Equal.sym(Bool, Listing.sp_before(a, b), LO.lo.Fr(a, b), LO.lo.before_spec(a, b)), e)

def lr.fr_sb(+a: Ls.Row, +b: Ls.Row, e: {LO.lo.Fr(a, b) == True{} : Bool}) -> {Listing.sp_before(a, b) == True{} : Bool}:
  Equal.trans(Bool, Listing.sp_before(a, b), LO.lo.Fr(a, b), True{}, LO.lo.before_spec(a, b), e)

def lr.cb_fr(+a: Ls.Row, +b: Ls.Row, -v: Bool, e: {Ls.before(a, b) == v : Bool}) -> {LO.lo.Fr(a, b) == v : Bool}:
  Equal.trans(Bool, LO.lo.Fr(a, b), Ls.before(a, b), v, Equal.sym(Bool, Ls.before(a, b), LO.lo.Fr(a, b), LO.lo.before_code(a, b)), e)

# x before y, y before every row of rest: x before every row of rest
def lr.ab_trans(+x: Ls.Row, +y: Ls.Row, rest: List<&2, Ls.Row>, +hxy: {LO.lo.Fr(x, y) == True{} : Bool}, +hy: {Listing.sp_all_before(y, rest) == True{} : Bool}) -> {Listing.sp_all_before(x, rest) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case +z <> +r:
      +hyz = lr.and_l(Listing.sp_before(y, z), Listing.sp_all_before(y, r), hy)
      +hyr = lr.and_r(Listing.sp_before(y, z), Listing.sp_all_before(y, r), hy)
      lr.and_tt(Listing.sp_before(x, z), Listing.sp_all_before(x, r), lr.fr_sb(x, z, LO.lo.Fr_trans(x, y, z, hxy, lr.sb_fr(y, z, hyz))), lr.ab_trans(x, y, r, hxy, hyr))

# z before every row of x inserted into ys: z before x and every row of ys
def lr.ab_ins(+z: Ls.Row, ys: List<&2, Ls.Row>, +x: Ls.Row, h: Bool) -> {Listing.sp_all_before(z, Ls.ins(ys, x, h)) == Bool.and(Listing.sp_before(z, x), Listing.sp_all_before(z, ys)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      match h:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Bool, Listing.sp_all_before(z, Ls.ins(rest, x, Ls.ins.head(x, rest))), Bool.and(Listing.sp_before(z, x), Listing.sp_all_before(z, rest)), lr.ab_ins(z, rest, x, Ls.ins.head(x, rest))) : {Bool.and(Listing.sp_before(z, y), _) == Bool.and(Listing.sp_before(z, x), Bool.and(Listing.sp_before(z, y), Listing.sp_all_before(z, rest))) : Bool}
          lr.and_swap(Listing.sp_before(z, y), Listing.sp_before(z, x), Listing.sp_all_before(z, rest))

def lr.sorted_ins(ys: List<&2, Ls.Row>, +ix: Nat, +px: Ls.Pick, +tx: Sg.Time, h: Bool, eh: {Ls.ins.head(Ls.Row{ix, px, tx}, ys) == h : Bool},
  +s: {Listing.sp_sorted(ys) == True{} : Bool}, +f: {Listing.sp_count(ix, Listing.sp_ats(ys)) == 0n : Nat}) ->
  {Listing.sp_sorted(Ls.ins(ys, Ls.Row{ix, px, tx}, h)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Ls.Row{+iy, +py, +ty} <> +rest:
      match h:
        case True{}:
          +x = {Ls.Row{ix, px, tx} : Ls.Row}
          +y = {Ls.Row{iy, py, ty} : Ls.Row}
          +sy = lr.and_l(Listing.sp_all_before(y, rest), Listing.sp_sorted(rest), s)
          +sr = lr.and_r(Listing.sp_all_before(y, rest), Listing.sp_sorted(rest), s)
          +hxy = lr.cb_fr(x, y, True{}, eh)
          lr.and_tt(Listing.sp_all_before(x, y <> rest), Listing.sp_sorted(y <> rest),
            lr.and_tt(Listing.sp_before(x, y), Listing.sp_all_before(x, rest), lr.fr_sb(x, y, hxy), lr.ab_trans(x, y, rest, hxy, sy)), s)
        case False{}:
          +x = {Ls.Row{ix, px, tx} : Ls.Row}
          +y = {Ls.Row{iy, py, ty} : Ls.Row}
          +sy = lr.and_l(Listing.sp_all_before(y, rest), Listing.sp_sorted(rest), s)
          +sr = lr.and_r(Listing.sp_all_before(y, rest), Listing.sp_sorted(rest), s)
          +nyx = lr.abz_b(Nat.is_eq(iy, ix), Listing.sp_count(ix, Listing.sp_ats(rest)), f)
          +fr = lr.abz_n(Nat.is_eq(iy, ix), Listing.sp_count(ix, Listing.sp_ats(rest)), f)
          +fyx = lr.or_false(LO.lo.Fr(y, x), LO.lo.Fr(x, y), LO.lo.Fr_total(y, x, nyx), lr.cb_fr(x, y, False{}, eh))
          +h2 = Ls.ins.head(x, rest)
          %Equal.sym(Bool, Listing.sp_all_before(y, Ls.ins(rest, x, h2)), Bool.and(Listing.sp_before(y, x), Listing.sp_all_before(y, rest)), lr.ab_ins(y, rest, x, h2)) : {Bool.and(_, Listing.sp_sorted(Ls.ins(rest, x, h2))) == True{} : Bool}
          lr.and_tt(Bool.and(Listing.sp_before(y, x), Listing.sp_all_before(y, rest)), Listing.sp_sorted(Ls.ins(rest, x, h2)),
            lr.and_tt(Listing.sp_before(y, x), Listing.sp_all_before(y, rest), lr.fr_sb(y, x, fyx), sy),
            lr.sorted_ins(rest, ix, px, tx, h2, {==}, sr, fr))

def lr.sorted_sort(xs: List<&2, Ls.Row>, +d: {lr.Dist(xs) == True{} : Bool}) -> {Listing.sp_sorted(Ls.sort(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Ls.Row{+ix, +px, +tx} <> +rest:
      +d0 = lr.and_l(Nat.is_eq(Listing.sp_count(ix, Listing.sp_ats(rest)), 0n), lr.Dist(rest), d)
      +dr = lr.and_r(Nat.is_eq(Listing.sp_count(ix, Listing.sp_ats(rest)), 0n), lr.Dist(rest), d)
      +f = Equal.trans(Nat, Listing.sp_count(ix, Listing.sp_ats(Ls.sort(rest))), Listing.sp_count(ix, Listing.sp_ats(rest)), 0n, lr.count_sort(rest, ix), lr.is_eq_zero(Listing.sp_count(ix, Listing.sp_ats(rest)), d0))
      lr.sorted_ins(Ls.sort(rest), ix, px, tx, Ls.ins.head(Ls.Row{ix, px, tx}, Ls.sort(rest)), {==}, lr.sorted_sort(rest, dr), f)

# rows.go: places fresh, from k on
# --------------------------------

def lr.dist_put(m: Maybe<&2, Ls.Row>, -R: List<&2, Ls.Row>, +k: Nat, -b: Bool, rel: lr.MRow(m, k, b), dR: {lr.Dist(R) == True{} : Bool}, fr: {Listing.sp_count(k, Listing.sp_ats(R)) == 0n : Nat}) -> {lr.Dist(Ls.row.put(m, R)) == True{} : Bool}:
  match m:
    case None{}:
      dR
    case Some{r}:
      match r:
        case Ls.Row{ir, pr, tr}:
          (ea, eb) = rel
          %Equal.sym(Nat, ir, k, ea) : {Bool.and(Nat.is_eq(Listing.sp_count(_, Listing.sp_ats(R)), 0n), lr.Dist(R)) == True{} : Bool}
          %Equal.sym(Nat, Listing.sp_count(k, Listing.sp_ats(R)), 0n, fr) : {Bool.and(Nat.is_eq(_, 0n), lr.Dist(R)) == True{} : Bool}
          dR

def lr.dist_go(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat) -> {lr.Dist(Ls.rows.go(os, all, k)) == True{} : Bool}:
  match os:
    case Nil{}:
      {==}
    case +o <> +rest:
      +fr = Equal.trans(Nat, Listing.sp_count(k, Listing.sp_ats(Ls.rows.go(rest, all, 1n+k))), Listing.sp_count_listed(rest, all, 1n+k, k), 0n, lr.count_go(rest, all, 1n+k, k), lr.below(rest, all, 1n+k, k, lr.lt_self(k)))
      lr.dist_put(Ls.row(o, all, k), Ls.rows.go(rest, all, 1n+k), k, Listing.sp_listed(o, all), lr.row_rel(o, all, k), lr.dist_go(rest, all, 1n+k), fr)

# The entries the scan skips
# --------------------------

def lr.seens(os: List<&2, Ls.Obs>) -> {Ls.seens(os) == Listing.sp_seens(os) : List<&2, Sg.Seen>}:
  match os:
    case Nil{}:
      {==}
    case o <> rest:
      match o:
        case Ls.Obs{+e, c, ts}:
          %lr.seens(rest) : {e <> Ls.seens(rest) == e <> _ : List<&2, Sg.Seen>}
          {==}

def lr.sb_o(b: Bool, +e: Sg.Seen, c: Maybe<&2, String>, ts: List<&2, Sg.Time>, -R: List<&2, Ls.Obs>) -> {Ls.seens(Listing.sp_blank.o(b, e, c, ts) <> R) == e <> Ls.seens(R) : List<&2, Sg.Seen>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lr.seens_blank(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>) -> {Ls.seens(Listing.sp_blank(os, all)) == Ls.seens(os) : List<&2, Sg.Seen>}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Ls.Obs{+e, c, ts}:
          Equal.trans(List<&2, Sg.Seen>, Ls.seens(Listing.sp_blank.o(Listing.sp_skip(Listing.sp_pick(e, all)), e, c, ts) <> Listing.sp_blank(rest, all)), e <> Ls.seens(Listing.sp_blank(rest, all)), e <> Ls.seens(rest),
            lr.sb_o(Listing.sp_skip(Listing.sp_pick(e, all)), e, c, ts, Listing.sp_blank(rest, all)),
            Equal.cong(List<&2, Sg.Seen>, List<&2, Sg.Seen>, l => e <> l, Ls.seens(Listing.sp_blank(rest, all)), Ls.seens(rest), lr.seens_blank(rest, all)))

def lr.rb(p: Ls.Pick, +e: Sg.Seen, c: Maybe<&2, String>, ts: List<&2, Sg.Time>, +A: List<&2, Sg.Seen>, +k: Nat, ep: {Ls.pick(e, A) == p : Ls.Pick}) -> {Ls.row(Listing.sp_blank.o(Listing.sp_skip(p), e, c, ts), A, k) == Ls.row(Ls.Obs{e, c, ts}, A, k) : Maybe<&2, Ls.Row>}:
  match p:
    case Ls.PSkip{}:
      %Equal.sym(Ls.Pick, Ls.pick(e, A), Ls.PSkip{}, ep) : {Ls.row.pick(_, k, Ls.cwd_ok(None{}), Nil{}) == Ls.row.pick(_, k, Ls.cwd_ok(c), ts) : Maybe<&2, Ls.Row>}
      {==}
    case Ls.PStore{s}:
      {==}
    case Ls.PLegacy{s}:
      {==}

def lr.row_blank(+e: Sg.Seen, c: Maybe<&2, String>, ts: List<&2, Sg.Time>, +A: List<&2, Sg.Seen>, +k: Nat) -> {Ls.row(Listing.sp_blank.o(Listing.sp_skip(Listing.sp_pick(e, A)), e, c, ts), A, k) == Ls.row(Ls.Obs{e, c, ts}, A, k) : Maybe<&2, Ls.Row>}:
  %LS.ls.pick(e, A) : {Ls.row(Listing.sp_blank.o(Listing.sp_skip(_), e, c, ts), A, k) == Ls.row(Ls.Obs{e, c, ts}, A, k) : Maybe<&2, Ls.Row>}
  lr.rb(Ls.pick(e, A), e, c, ts, A, k, {==})

def lr.go_blank(os: List<&2, Ls.Obs>, +A: List<&2, Sg.Seen>, +k: Nat) -> {Ls.rows.go(Listing.sp_blank(os, A), A, k) == Ls.rows.go(os, A, k) : List<&2, Ls.Row>}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Ls.Obs{+e, +c, +ts}:
          %Equal.sym(Maybe<&2, Ls.Row>, Ls.row(Listing.sp_blank.o(Listing.sp_skip(Listing.sp_pick(e, A)), e, c, ts), A, k), Ls.row(Ls.Obs{e, c, ts}, A, k), lr.row_blank(e, c, ts, A, k)) : {Ls.row.put(_, Ls.rows.go(Listing.sp_blank(rest, A), A, 1n+k)) == Ls.row.put(Ls.row(Ls.Obs{e, c, ts}, A, k), Ls.rows.go(rest, A, 1n+k)) : List<&2, Ls.Row>}
          %Equal.sym(List<&2, Ls.Row>, Ls.rows.go(Listing.sp_blank(rest, A), A, 1n+k), Ls.rows.go(rest, A, 1n+k), lr.go_blank(rest, A, 1n+k)) : {Ls.row.put(Ls.row(Ls.Obs{e, c, ts}, A, k), _) == Ls.row.put(Ls.row(Ls.Obs{e, c, ts}, A, k), Ls.rows.go(rest, A, 1n+k)) : List<&2, Ls.Row>}
          {==}
