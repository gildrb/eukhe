# eukhe: lemmas of LAW rows_are_entries: the newest time
#
# Ls.newest folds the times keeping the later of two (Ls.later); what it
# answers is one of the times (lra.in) and no time is later than it
# (lra.nlc): the order of times is lo.lcmp on their keys, LT transitive
# and EQ only on equal keys (lo.lrel, proof/listing/base/order.bend).

import Base
import ../../../bend/staging.bend as Sg
import ../../../bend/listing.bend as Ls
import ../../../laws/listing.bend as Listing
import ../base/order.bend as LO
import ../base/scan.bend as LA
import ../base/rows.bend as LR

# One of the times
# ----------------

def lra.ts_refl(t: Sg.Time) -> {Listing.sp_time_same(t, t) == True{} : Bool}:
  match t:
    case Sg.Time{+s, +n}:
      %Equal.sym(Bool, Nat.is_eq(s, s), True{}, LR.lr.eq_refl(s)) : {Bool.and(_, Nat.is_eq(n, n)) == True{} : Bool}
      LR.lr.eq_refl(n)

def lra.or3(a: Bool, +b: Bool, -c: Bool, h: {Bool.or(a, c) == True{} : Bool}) -> {Bool.or(a, Bool.or(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, c, True{}, h) : {Bool.or(b, _) == True{} : Bool}
      LA.ls.or_true(b)

def lra.in.step(b: Bool, +r: Sg.Time, +t: Sg.Time, +u: Sg.Time, -rest: List<&2, Sg.Time>, h: {Bool.or(Listing.sp_time_same(r, Ls.later.pick(b, t, u)), Listing.sp_time_in(r, rest)) == True{} : Bool}) -> {Bool.or(Listing.sp_time_same(r, t), Bool.or(Listing.sp_time_same(r, u), Listing.sp_time_in(r, rest))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.or(Listing.sp_time_same(r, u), Listing.sp_time_in(r, rest)), True{}, h) : {Bool.or(Listing.sp_time_same(r, t), _) == True{} : Bool}
      LA.ls.or_true(Listing.sp_time_same(r, t))
    case False{}:
      lra.or3(Listing.sp_time_same(r, t), Listing.sp_time_same(r, u), Listing.sp_time_in(r, rest), h)

# the newest is one of the times
def lra.in(ts: List<&2, Sg.Time>, +t: Sg.Time) -> {Listing.sp_time_in(Ls.newest(ts, t), t <> ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      %Equal.sym(Bool, Listing.sp_time_same(t, t), True{}, lra.ts_refl(t)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case +u <> +rest:
      lra.in.step(Ls.lex(Ls.tkey(t), Ls.tkey(u)), Ls.newest(rest, Ls.later(t, u)), t, u, rest, lra.in(rest, Ls.later(t, u)))

# None later
# ----------

def lra.K(t: Sg.Time) -> List<&2, Nat>:
  Ls.tkey(t)

# no time of ts has a key above r's, by lo.lcmp
def lra.nl(+r: Sg.Time, ts: List<&2, Sg.Time>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case u <> rest:
      Bool.and(Bool.not(Cmp.is_lt(LO.lo.lcmp(Ls.tkey(r), Ls.tkey(u)))), lra.nl(r, rest))

def lra.ear(a: Sg.Time, b: Sg.Time) -> {Listing.sp_earlier(a, b) == Cmp.is_lt(LO.lo.lcmp(Ls.tkey(a), Ls.tkey(b))) : Bool}:
  match a b:
    case Sg.Time{+s1, +n1} Sg.Time{+s2, +n2}:
      LO.lo.splex([s1, n1], [s2, n2])

def lra.nl_eq(+r: Sg.Time, ts: List<&2, Sg.Time>) -> {Listing.sp_none_later(r, ts) == lra.nl(r, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +u <> +rest:
      %lra.ear(r, u) : {Bool.and(Bool.not(Listing.sp_earlier(r, u)), Listing.sp_none_later(r, rest)) == Bool.and(Bool.not(_), lra.nl(r, rest)) : Bool}
      %lra.nl_eq(r, rest) : {Bool.and(Bool.not(Listing.sp_earlier(r, u)), Listing.sp_none_later(r, rest)) == Bool.and(Bool.not(Listing.sp_earlier(r, u)), _) : Bool}
      {==}

def lra.sel(b: Bool, c1: Cmp, c3: Cmp) -> Cmp:
  match b:
    case True{}:
      c3
    case False{}:
      c1

def lra.selK(b: Bool, +r: Sg.Time, +t: Sg.Time, +u: Sg.Time) -> {LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later.pick(b, t, u))) == lra.sel(b, LO.lo.lcmp(Ls.tkey(r), Ls.tkey(t)), LO.lo.lcmp(Ls.tkey(r), Ls.tkey(u))) : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# what the compares say: the newest so far is no earlier than t nor u
def lra.pick(b: Bool, c1: Cmp, c2: Cmp, c3: Cmp, -N: Bool, eb: {Cmp.is_lt(c2) == b : Bool}, rel: LO.lo.Rel(c1, c2, c3), h: {Bool.and(Bool.not(Cmp.is_lt(lra.sel(b, c1, c3))), N) == True{} : Bool}) -> {Bool.and(Bool.not(Cmp.is_lt(c1)), Bool.and(Bool.not(Cmp.is_lt(c3)), N)) == True{} : Bool}:
  match b:
    case True{}:
      match c1:
        case LT{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, h)
                case EQ{}:
                  LO.lo.eq_lt({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  LO.lo.gt_lt({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, rel)
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
        case EQ{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, h)
                case EQ{}:
                  LO.lo.eq_lt({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  LO.lo.gt_lt({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, rel)
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
        case GT{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, h)
                case EQ{}:
                  h
                case GT{}:
                  h
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
    case False{}:
      match c1:
        case LT{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, h)
                case EQ{}:
                  LO.lo.eq_lt({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  LO.lo.gt_lt({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, rel)
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, h)
                case EQ{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, h)
                case GT{}:
                  LO.lo.ft({Bool.and(Bool.not(Cmp.is_lt(LT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, h)
        case EQ{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.lt_eq({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, rel)
                case EQ{}:
                  h
                case GT{}:
                  LO.lo.gt_eq({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, rel)
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.lt_gt({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, rel)
                case EQ{}:
                  LO.lo.eq_gt({Bool.and(Bool.not(Cmp.is_lt(EQ{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  h
        case GT{}:
          match c2:
            case LT{}:
              match c3:
                case LT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, eb)
                case EQ{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, eb)
                case GT{}:
                  LO.lo.tf({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(GT{})), N)) == True{} : Bool}, eb)
            case EQ{}:
              match c3:
                case LT{}:
                  LO.lo.lt_gt({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, rel)
                case EQ{}:
                  LO.lo.eq_gt({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  h
            case GT{}:
              match c3:
                case LT{}:
                  LO.lo.lt_gt({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(LT{})), N)) == True{} : Bool}, rel)
                case EQ{}:
                  LO.lo.eq_gt({Bool.and(Bool.not(Cmp.is_lt(GT{})), Bool.and(Bool.not(Cmp.is_lt(EQ{})), N)) == True{} : Bool}, rel)
                case GT{}:
                  h

# no time is later than the newest
def lra.nlc(ts: List<&2, Sg.Time>, +t: Sg.Time) -> {lra.nl(Ls.newest(ts, t), t <> ts) == True{} : Bool}:
  match ts:
    case Nil{}:
      %Equal.sym(Cmp, LO.lo.lcmp(Ls.tkey(t), Ls.tkey(t)), EQ{}, LO.lo.lrefl(Ls.tkey(t))) : {Bool.and(Bool.not(Cmp.is_lt(_)), True{}) == True{} : Bool}
      {==}
    case +u <> +rest:
      +r = Ls.newest(rest, Ls.later(t, u))
      +N = lra.nl(r, rest)
      +b = Cmp.is_lt(LO.lo.lcmp(Ls.tkey(t), Ls.tkey(u)))
      +c1 = LO.lo.lcmp(Ls.tkey(r), Ls.tkey(t))
      +c3 = LO.lo.lcmp(Ls.tkey(r), Ls.tkey(u))
      +e1 = Equal.cong(Bool, Sg.Time, z => Ls.later.pick(z, t, u), Ls.lex(Ls.tkey(t), Ls.tkey(u)), b, LO.lo.lex(Ls.tkey(t), Ls.tkey(u)))
      +e2 = Equal.trans(Cmp, LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later(t, u))), LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later.pick(b, t, u))), lra.sel(b, c1, c3),
        Equal.cong(Sg.Time, Cmp, x => LO.lo.lcmp(Ls.tkey(r), Ls.tkey(x)), Ls.later(t, u), Ls.later.pick(b, t, u), e1), lra.selK(b, r, t, u))
      +e3 = Equal.cong(Cmp, Bool, y => Bool.and(Bool.not(Cmp.is_lt(y)), N), LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later(t, u))), lra.sel(b, c1, c3), e2)
      +h = Equal.trans(Bool, Bool.and(Bool.not(Cmp.is_lt(lra.sel(b, c1, c3))), N), Bool.and(Bool.not(Cmp.is_lt(LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later(t, u))))), N), True{},
        Equal.sym(Bool, Bool.and(Bool.not(Cmp.is_lt(LO.lo.lcmp(Ls.tkey(r), Ls.tkey(Ls.later(t, u))))), N), Bool.and(Bool.not(Cmp.is_lt(lra.sel(b, c1, c3))), N), e3), lra.nlc(rest, Ls.later(t, u)))
      lra.pick(b, c1, LO.lo.lcmp(Ls.tkey(t), Ls.tkey(u)), c3, N, {==}, LO.lo.lrel(Ls.tkey(r), Ls.tkey(t), Ls.tkey(u)), h)

# the newest of the times is one of them, and none is later
def lra.newest_ok(+ts: List<&2, Sg.Time>, +t: Sg.Time) -> {Listing.sp_newest_ok(Ls.newest(ts, t), t <> ts) == True{} : Bool}:
  +r = Ls.newest(ts, t)
  %Equal.sym(Bool, Listing.sp_none_later(r, t <> ts), lra.nl(r, t <> ts), lra.nl_eq(r, t <> ts)) : {Bool.and(Listing.sp_time_in(r, t <> ts), _) == True{} : Bool}
  LR.lr.and_tt(Listing.sp_time_in(r, t <> ts), lra.nl(r, t <> ts), lra.in(ts, t), lra.nlc(ts, t))
