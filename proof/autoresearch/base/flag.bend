# eukhe: lemmas for the flag laws of area autoresearch: the code's walk
# over the rows (flag.rows) finds a logged run exactly when the law's
# ar_logged_id does, changes no row but for its flag, and flags no run
# but the one named

import Base
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../laws/autoresearch/model.bend as ArM
import ../../../laws/autoresearch/events.bend as AutoresearchEvents
import ./step.bend as AS
import ./events.bend as AE

# Found
# -----

def fl.found_at(hit: Bool, -r: ArS.Row, -t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, -x: Bool, hq: {AE.ev.snd(q) == x : Bool}) -> {AE.ev.snd(ArP.flag.at(hit, r, t, q)) == Bool.or(hit, x) : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      match q:
        case (a, f):
          hq

# the walk finds a run exactly when some logged row has its id
def fl.found(rs: List<&2, ArS.Row>, +n: Nat) -> {AE.ev.snd(ArP.flag.rows(rs, n)) == ArM.ar_logged_id(rs, n) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{+i, +sg, +st, +m, +ms, +ps, +fn, +fl, +desc} <> +t:
      fl.found_at(Bool.and(Nat.is_eq(i, n), ArS.has(st)), ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}, t, ArP.flag.rows(t, n), ArM.ar_logged_id(t, n), fl.found(t, n))

# Rows but their flags
# --------------------

def fl.unmark_at(hit: Bool, r: ArS.Row, -t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, hq: {AutoresearchEvents.ar_unmark(AE.ev.fst(q)) == AutoresearchEvents.ar_unmark(t) : List<&2, ArS.Row>}) -> {AutoresearchEvents.ar_unmark(AE.ev.fst(ArP.flag.at(hit, r, t, q))) == AutoresearchEvents.ar_unmark(r <> t) : List<&2, ArS.Row>}:
  match hit:
    case True{}:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          {==}
    case False{}:
      match r:
        case ArS.Row{+i, +sg, +st, +m, +ms, +ps, +fn, fl, +desc}:
          match q:
            case (a, f):
              Equal.cong(List<&2, ArS.Row>, List<&2, ArS.Row>, y => ArS.Row{i, sg, st, m, ms, ps, fn, False{}, desc} <> y, AutoresearchEvents.ar_unmark(a), AutoresearchEvents.ar_unmark(t), hq)

def fl.unmark(rs: List<&2, ArS.Row>, +n: Nat) -> {AutoresearchEvents.ar_unmark(AE.ev.fst(ArP.flag.rows(rs, n))) == AutoresearchEvents.ar_unmark(rs) : List<&2, ArS.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      fl.unmark_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), fl.unmark(t, n))

# Other runs' flags
# -----------------

def fl.other_at(hit: Bool, r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +n: Nat, +k: Nat, ne: {Nat.is_eq(n, k) == False{} : Bool}, eh: {ArP.flag.hit(r, n) == hit : Bool}, hq: {ArM.ar_flagged(AE.ev.fst(q), k) == ArM.ar_flagged(t, k) : Bool}) -> {ArM.ar_flagged(AE.ev.fst(ArP.flag.at(hit, r, t, q)), k) == ArM.ar_flagged(r <> t, k) : Bool}:
  match hit:
    case True{}:
      match r:
        case ArS.Row{+i, sg, +st, m, ms, ps, fn, fl, desc}:
          +hi = AS.as.nat_eq(i, n, AS.as.and_l(Nat.is_eq(i, n), ArS.has(st), eh))
          +ek = Equal.trans(Bool, Nat.is_eq(i, k), Nat.is_eq(n, k), False{}, Equal.cong(Nat, Bool, y => Nat.is_eq(y, k), i, n, hi), ne)
          %Equal.sym(Bool, Nat.is_eq(i, k), False{}, ek) : {Bool.or(Bool.and(_, True{}), ArM.ar_flagged(t, k)) == Bool.or(Bool.and(_, fl), ArM.ar_flagged(t, k)) : Bool}
          {==}
    case False{}:
      match q:
        case (a, f):
          Equal.cong(Bool, Bool, y => Bool.or(ArM.ar_flagged.at(r, k), y), ArM.ar_flagged(a, k), ArM.ar_flagged(t, k), hq)

def fl.other(rs: List<&2, ArS.Row>, +n: Nat, +k: Nat, +ne: {Nat.is_eq(n, k) == False{} : Bool}) -> {ArM.ar_flagged(AE.ev.fst(ArP.flag.rows(rs, n)), k) == ArM.ar_flagged(rs, k) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      fl.other_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), n, k, ne, {==}, fl.other(t, n, k, ne))
