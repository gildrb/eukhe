# eukhe: the proof of LAW cron_heartbeat_flags

import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron_beats.bend as CronBeats

# Every change of a record (a stop, a move to another session, a per-job
# decision) keeps its flag; so the flags of a list of records stay, record
# by record.

# two lists alike head by head and tail by tail are alike
def fl.cons(-x: Bool, -y: Bool, -xs: List<&2, Bool>, -ys: List<&2, Bool>, ex: {x == y : Bool}, et: {xs == ys : List<&2, Bool>}) -> {x <> xs == y <> ys : List<&2, Bool>}:
  %ex : {x <> xs == _ <> ys : List<&2, Bool>}
  %et : {x <> xs == x <> _ : List<&2, Bool>}
  {==}

# Records
# -------

def fl.stop_row(+s: Nat, r: CB.Row) -> {CronBeats.flag_spec(CB.stop_row(s, r)) == CronBeats.flag_spec(r) : Bool}:
  match r:
    case CB.Row{s2, fl, hb, f}:
      {==}

def fl.go(b: Bool, -s: Nat, -file: Nat, -s2: Nat, -fl: Nat, -hb: Bool, -f: CS.Fact) -> {CronBeats.flag_spec(CB.relabel.go(b, s, file, s2, fl, hb, f)) == hb : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fl.relabel_row(+s: Nat, +file: Nat, r: CB.Row) -> {CronBeats.flag_spec(CB.relabel_row(s, file, r)) == CronBeats.flag_spec(r) : Bool}:
  match r:
    case CB.Row{+s2, +fl, hb, f}:
      fl.go(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), s, file, s2, fl, hb, f)

def fl.on_row(-op: CB.Op, r: CB.Row) -> {CronBeats.flag_spec(CB.on_row(op, r)) == CronBeats.flag_spec(r) : Bool}:
  match r:
    case CB.Row{s2, fl, hb, f}:
      {==}

# Lists
# -----

def fl.stop(+s: Nat, rs: List<&2, CB.Row>) -> {CronBeats.flags_spec(CB.stop_beats(s, rs)) == CronBeats.flags_spec(rs) : List<&2, Bool>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      fl.cons(CronBeats.flag_spec(CB.stop_row(s, r)), CronBeats.flag_spec(r), CronBeats.flags_spec(CB.stop_beats(s, t)), CronBeats.flags_spec(t), fl.stop_row(s, r), fl.stop(s, t))

def fl.but(+s: Nat, k: Nat, rs: List<&2, CB.Row>) -> {CronBeats.flags_spec(CB.stop_but(s, k, rs)) == CronBeats.flags_spec(rs) : List<&2, Bool>}:
  match k:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case r <> t:
          fl.cons(CronBeats.flag_spec(r), CronBeats.flag_spec(r), CronBeats.flags_spec(CB.stop_beats(s, t)), CronBeats.flags_spec(t), {==}, fl.stop(s, t))
    case 1n+q:
      match rs:
        case Nil{}:
          {==}
        case r <> t:
          fl.cons(CronBeats.flag_spec(CB.stop_row(s, r)), CronBeats.flag_spec(r), CronBeats.flags_spec(CB.stop_but(s, q, t)), CronBeats.flags_spec(t), fl.stop_row(s, r), fl.but(s, q, t))

def fl.relabel(+s: Nat, +file: Nat, rs: List<&2, CB.Row>) -> {CronBeats.flags_spec(CB.relabel(s, file, rs)) == CronBeats.flags_spec(rs) : List<&2, Bool>}:
  match rs:
    case Nil{}:
      {==}
    case r <> t:
      fl.cons(CronBeats.flag_spec(CB.relabel_row(s, file, r)), CronBeats.flag_spec(r), CronBeats.flags_spec(CB.relabel(s, file, t)), CronBeats.flags_spec(t), fl.relabel_row(s, file, r), fl.relabel(s, file, t))

def fl.on(i: Nat, +op: CB.Op, rs: List<&2, CB.Row>) -> {CronBeats.flags_spec(CB.on(i, op, rs)) == CronBeats.flags_spec(rs) : List<&2, Bool>}:
  match i:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case r <> t:
          fl.cons(CronBeats.flag_spec(CB.on_row(op, r)), CronBeats.flag_spec(r), CronBeats.flags_spec(t), CronBeats.flags_spec(t), fl.on_row(op, r), {==})
    case 1n+q:
      match rs:
        case Nil{}:
          {==}
        case r <> t:
          fl.cons(CronBeats.flag_spec(r), CronBeats.flag_spec(r), CronBeats.flags_spec(CB.on(q, op, t)), CronBeats.flags_spec(t), {==}, fl.on(q, op, t))

# CronBeats

def CronBeats.cron_heartbeat_flags(a, rs):
  match a:
    case CB.AHeartbeat{+s, file, p, at}:
      fl.cons(True{}, True{}, CronBeats.flags_spec(CB.stop_beats(s, rs)), CronBeats.flags_spec(rs), {==}, fl.stop(s, rs))
    case CB.AJob{s, file, p, at}:
      {==}
    case CB.AOn{i, op}:
      fl.on(i, op, rs)
    case CB.ARebind{+s, +file, keep}:
      Equal.trans(List<&2, Bool>, CronBeats.flags_spec(CB.stop_but(s, keep, CB.relabel(s, file, rs))), CronBeats.flags_spec(CB.relabel(s, file, rs)), CronBeats.flags_spec(rs), fl.but(s, keep, CB.relabel(s, file, rs)), fl.relabel(s, file, rs))
    case CB.ALose{}:
      {==}
