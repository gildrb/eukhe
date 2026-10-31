# eukhe: lemmas of LAW run_conservation (prefix ah.): the ids and the
# count of the runs over appended rows, a flag and the next start; the
# logged and abandoned rows add up to all rows.

import Base
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../laws/autoresearch/model.bend as ArM
import ../../../laws/autoresearch/history.bend as AutoresearchHistory
import ../base/history.bend as AH
import ../best_is_best/order.bend as AO

# how many runs started
def ah.K(s: ArS.St) -> Nat:
  ArS.St.started(s)

# the id of the pending run, if any
def ah.tl(p: Maybe<&2, ArS.Pend>) -> List<&2, Nat>:
  match p:
    case None{}:
      Nil{}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          [id]

def ah.ids_tl(-cfg: Maybe<&2, ArS.Cfg>, -seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>) -> {AutoresearchHistory.ar_ids(ArS.St{cfg, seg, mode, runs, pend}) == AutoresearchHistory.ar_ids.rows(runs, ah.tl(pend)) : List<&2, Nat>}:
  match pend:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          {==}

# Appended rows
# -------------

def ah.rlen_snoc(rs: List<&2, ArS.Row>, -ys: List<&2, ArS.Row>) -> {ArS.rlen(ArS.snoc(rs, ys)) == Nat.add(ArS.rlen(rs), ArS.rlen(ys)) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      Equal.cong(Nat, Nat, x => 1n+x, ArS.rlen(ArS.snoc(t, ys)), Nat.add(ArS.rlen(t), ArS.rlen(ys)), ah.rlen_snoc(t, ys))

def ah.ids_snoc(rs: List<&2, ArS.Row>, -ys: List<&2, ArS.Row>, -tl: List<&2, Nat>) -> {AutoresearchHistory.ar_ids.rows(ArS.snoc(rs, ys), tl) == AutoresearchHistory.ar_ids.rows(rs, AutoresearchHistory.ar_ids.rows(ys, tl)) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => i <> x, AutoresearchHistory.ar_ids.rows(ArS.snoc(t, ys), tl), AutoresearchHistory.ar_ids.rows(t, AutoresearchHistory.ar_ids.rows(ys, tl)), ah.ids_snoc(t, ys, tl))

def ah.ids_app(rs: List<&2, ArS.Row>, -tl: List<&2, Nat>, -ys: List<&2, Nat>) -> {AutoresearchHistory.ar_ids.rows(rs, List.append(&2, Nat, tl, ys)) == List.append(&2, Nat, AutoresearchHistory.ar_ids.rows(rs, tl), ys) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => i <> x, AutoresearchHistory.ar_ids.rows(t, List.append(&2, Nat, tl, ys)), List.append(&2, Nat, AutoresearchHistory.ar_ids.rows(t, tl), ys), ah.ids_app(t, tl, ys))

def ah.upto_app(n: Nat, acc: List<&2, Nat>, -ys: List<&2, Nat>) -> {AutoresearchHistory.ar_upto.go(n, List.append(&2, Nat, acc, ys)) == List.append(&2, Nat, AutoresearchHistory.ar_upto.go(n, acc), ys) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      ah.upto_app(k, (1n+k) <> acc, ys)

def ah.rlen_ab(-m: String, -sg: Nat, p: Maybe<&2, ArS.Pend>) -> {ArS.rlen(ArS.abandon(m, sg, p)) == ArS.pcount(p) : Nat}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      {==}

def ah.ids_ab(-m: String, -sg: Nat, p: Maybe<&2, ArS.Pend>, -tl: List<&2, Nat>) -> {AutoresearchHistory.ar_ids.rows(ArS.abandon(m, sg, p), tl) == List.append(&2, Nat, ah.tl(p), tl) : List<&2, Nat>}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          {==}

def ah.ids_ab0(-m: String, -sg: Nat, p: Maybe<&2, ArS.Pend>) -> {AutoresearchHistory.ar_ids.rows(ArS.abandon(m, sg, p), Nil{}) == ah.tl(p) : List<&2, Nat>}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          {==}

def ah.add_one(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  Equal.trans(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), 1n+n, AH.ah.add_succ(n, 0n), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(n, 0n), n, AH.ah.add_zero(n)))

# A flag
# ------

def ah.fr_at(b: Bool, -r: ArS.Row, -t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, hq: {ArS.rlen(AO.ah.fst(q)) == ArS.rlen(t) : Nat}) -> {ArS.rlen(AO.ah.fst(ArP.flag.at(b, r, t, q))) == ArS.rlen(r <> t) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      (a, f) = q
      Equal.cong(Nat, Nat, x => 1n+x, ArS.rlen(a), ArS.rlen(t), hq)

# a flag keeps the number of rows
def ah.flag_rlen(rs: List<&2, ArS.Row>, +n: Nat) -> {ArS.rlen(AO.ah.fst(ArP.flag.rows(rs, n))) == ArS.rlen(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.fr_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), ah.flag_rlen(t, n))

def ah.fi_at(b: Bool, r: ArS.Row, -t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, -tl: List<&2, Nat>, hq: {AutoresearchHistory.ar_ids.rows(AO.ah.fst(q), tl) == AutoresearchHistory.ar_ids.rows(t, tl) : List<&2, Nat>}) -> {AutoresearchHistory.ar_ids.rows(AO.ah.fst(ArP.flag.at(b, r, t, q)), tl) == AutoresearchHistory.ar_ids.rows(r <> t, tl) : List<&2, Nat>}:
  match b:
    case True{}:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          {==}
    case False{}:
      match r:
        case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
          (a, f) = q
          Equal.cong(List<&2, Nat>, List<&2, Nat>, x => i <> x, AutoresearchHistory.ar_ids.rows(a, tl), AutoresearchHistory.ar_ids.rows(t, tl), hq)

# a flag keeps the ids of the rows
def ah.flag_ids(rs: List<&2, ArS.Row>, +n: Nat, +tl: List<&2, Nat>) -> {AutoresearchHistory.ar_ids.rows(AO.ah.fst(ArP.flag.rows(rs, n)), tl) == AutoresearchHistory.ar_ids.rows(rs, tl) : List<&2, Nat>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      ah.fi_at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), tl, ah.flag_ids(t, n, tl))

# The count
# ---------

# the logged and the abandoned rows are all rows
def ah.cnt(rs: List<&2, ArS.Row>, +x: Nat) -> {Nat.add(AutoresearchHistory.ar_status_n(rs, True{}), Nat.add(AutoresearchHistory.ar_status_n(rs, False{}), x)) == Nat.add(ArS.rlen(rs), x) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc} <> +t:
      match st:
        case None{}:
          Equal.trans(Nat, Nat.add(AutoresearchHistory.ar_status_n(t, True{}), 1n+Nat.add(AutoresearchHistory.ar_status_n(t, False{}), x)), 1n+Nat.add(AutoresearchHistory.ar_status_n(t, True{}), Nat.add(AutoresearchHistory.ar_status_n(t, False{}), x)), 1n+Nat.add(ArS.rlen(t), x), AH.ah.add_succ(AutoresearchHistory.ar_status_n(t, True{}), Nat.add(AutoresearchHistory.ar_status_n(t, False{}), x)), Equal.cong(Nat, Nat, y => 1n+y, Nat.add(AutoresearchHistory.ar_status_n(t, True{}), Nat.add(AutoresearchHistory.ar_status_n(t, False{}), x)), Nat.add(ArS.rlen(t), x), ah.cnt(t, x)))
        case Some{k}:
          Equal.cong(Nat, Nat, y => 1n+y, Nat.add(AutoresearchHistory.ar_status_n(t, True{}), Nat.add(AutoresearchHistory.ar_status_n(t, False{}), x)), Nat.add(ArS.rlen(t), x), ah.cnt(t, x))

def ah.count(s: ArS.St) -> {Nat.add(AutoresearchHistory.ar_status_n(ArM.ar_runs(s), True{}), Nat.add(AutoresearchHistory.ar_status_n(ArM.ar_runs(s), False{}), AutoresearchHistory.ar_pending_n(s))) == ah.K(s) : Nat}:
  match s:
    case ArS.St{c, seg, mode, +runs, pend}:
      match pend:
        case None{}:
          ah.cnt(runs, 0n)
        case Some{p}:
          ah.cnt(runs, 1n)

def ah.swap(b: Bool, g: Nat, -k: Nat) -> {Nat.add(g, Nat.add(ArM.ar_one(b), k)) == Nat.add(Nat.add(ArM.ar_one(b), g), k) : Nat}:
  match b:
    case True{}:
      AH.ah.add_succ(g, k)
    case False{}:
      {==}
