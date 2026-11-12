# eukhe: the proof of LAW cron_beats_step_exact
# A new job's facts are make_spec's; the user's stop the code applies is
# halt_spec's stop, on the `/heartbeat` records of the session alone; a
# decision is the spec's (LCb.de.on); a rebind counts the kept record
# down where the spec counts the index up (bs.keep_at: the kept record is
# at index k + i; bs.past: past it no record is kept).

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_beats.bend as CronBeats
import ./base.bend as LCb

# Numbers
# -------

def bs.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      bs.eq_refl(p)

def bs.add_zero(k: Nat) -> {Nat.add(k, 0n) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %bs.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def bs.add_succ(q: Nat, +i: Nat) -> {Nat.add(q, 1n+i) == 1n+Nat.add(q, i) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      %bs.add_succ(p, i) : {1n+Nat.add(p, 1n+i) == 1n+_ : Nat}
      {==}

def bs.lt_self(i: Nat) -> {Nat.is_lt(i, 1n+i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      bs.lt_self(p)

def bs.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a claim that False is True proves anything
def bs.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : bs.If(_, G)
  Unit{}

def bs.lt_succ(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      bs.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      bs.lt_succ(p, q, h)

def bs.lt_add(q: Nat, +i: Nat) -> {Nat.is_lt(i, 1n+Nat.add(q, i)) == True{} : Bool}:
  match q:
    case 0n:
      bs.lt_self(i)
    case 1n++p:
      bs.lt_succ(i, 1n+Nat.add(p, i), bs.lt_add(p, i))

# a < b: a is not b, nor b a
def bs.ne_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      bs.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      bs.ne_lt(p, q, h)

def bs.ne_gt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      bs.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      bs.ne_gt(p, q, h)

def bs.and_true(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bs.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bs.and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# One record
# ----------

# the code's stop is the spec's
def bs.stopped(f: CS.Fact) -> {CB.stopped(f) == CronBeats.stopped_spec(f) : CS.Fact}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          {==}
        case Cr.Paused{}:
          {==}
        case Cr.Finished{}:
          {==}
        case Cr.Cancelled{}:
          {==}

def bs.stop_if(b: Bool, +f: CS.Fact) -> {CB.stop_if(b, f) == CronBeats.stop_when_spec(b, f) : CS.Fact}:
  match b:
    case True{}:
      bs.stopped(f)
    case False{}:
      {==}

def bs.beat_row(+s: Nat, r: CB.Row) -> {CB.stop_row(s, r) == CronBeats.beat_row_spec(s, r) : CB.Row}:
  match r:
    case CB.Row{+s2, fl, +hb, +f}:
      %bs.and_comm(Nat.is_eq(s2, s), hb) : {CB.Row{s2, fl, hb, CB.stop_if(Bool.and(Nat.is_eq(s2, s), hb), f)} == CB.Row{s2, fl, hb, CronBeats.stop_when_spec(_, f)} : CB.Row}
      %bs.stop_if(Bool.and(Nat.is_eq(s2, s), hb), f) : {CB.Row{s2, fl, hb, CB.stop_if(Bool.and(Nat.is_eq(s2, s), hb), f)} == CB.Row{s2, fl, hb, _} : CB.Row}
      {==}

def bs.beat_rows(+s: Nat, rs: List<&2, CB.Row>) -> {CB.stop_beats(s, rs) == CronBeats.beat_rows_spec(s, rs) : List<&2, CB.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %bs.beat_row(s, r) : {CB.stop_row(s, r) <> CB.stop_beats(s, t) == _ <> CronBeats.beat_rows_spec(s, t) : List<&2, CB.Row>}
      %bs.beat_rows(s, t) : {CB.stop_row(s, r) <> CB.stop_beats(s, t) == CB.stop_row(s, r) <> _ : List<&2, CB.Row>}
      {==}

# A rebind
# --------

# a record the rebind keeps (the moved one keeps its facts)
def bs.kept_go(m: Bool, +s: Nat, +file: Nat, s2: Nat, fl: Nat, hb: Bool, f: CS.Fact) -> {CB.relabel.go(m, s, file, s2, fl, hb, f) == CronBeats.moved_row_spec(m, True{}, s, file, s2, fl, hb, f) : CB.Row}:
  match m:
    case True{}:
      match hb:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def bs.kept_row(+s: Nat, +file: Nat, +i: Nat, r: CB.Row) -> {CB.relabel_row(s, file, r) == CronBeats.rebound_row_spec(s, file, i, i, r) : CB.Row}:
  match r:
    case CB.Row{+s2, +fl, +hb, +f}:
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, bs.eq_refl(i)) : {CB.relabel.go(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), s, file, s2, fl, hb, f) == CronBeats.moved_row_spec(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), _, s, file, s2, fl, hb, f) : CB.Row}
      bs.kept_go(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), s, file, s2, fl, hb, f)

# a heartbeat moved to session s and not kept stops; any other record moved stays
def bs.stop_hb(hb: Bool, +f: CS.Fact) -> {CB.stop_if(hb, f) == CronBeats.stop_when_spec(Bool.and(hb, True{}), f) : CS.Fact}:
  match hb:
    case True{}:
      bs.stopped(f)
    case False{}:
      {==}

def bs.stop_moved(+s: Nat, +file: Nat, +hb: Bool, +f: CS.Fact) -> {CB.stop_row(s, CB.Row{s, file, hb, f}) == CronBeats.moved_row_spec(True{}, False{}, s, file, s, file, hb, f) : CB.Row}:
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, bs.eq_refl(s)) : {CB.Row{s, file, hb, CB.stop_if(Bool.and(_, hb), f)} == CB.Row{s, file, hb, CronBeats.stop_when_spec(Bool.and(hb, True{}), f)} : CB.Row}
  %bs.stop_hb(hb, f) : {CB.Row{s, file, hb, CB.stop_if(hb, f)} == CB.Row{s, file, hb, _} : CB.Row}
  {==}

def bs.stop_go(b1: Bool, b2: Bool, +s: Nat, +file: Nat, +s2: Nat, +fl: Nat, +hb: Bool, +f: CS.Fact, h: {Nat.is_eq(s2, s) == b1 : Bool}) -> {CB.stop_row(s, CB.relabel.go(Bool.or(b1, b2), s, file, s2, fl, hb, f)) == CronBeats.moved_row_spec(Bool.or(b1, b2), False{}, s, file, s2, fl, hb, f) : CB.Row}:
  match b1:
    case True{}:
      bs.stop_moved(s, file, hb, f)
    case False{}:
      match b2:
        case True{}:
          bs.stop_moved(s, file, hb, f)
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(s2, s), False{}, h) : {CB.Row{s2, fl, hb, CB.stop_if(Bool.and(_, hb), f)} == CB.Row{s2, fl, hb, f} : CB.Row}
          {==}

def bs.stop_row(+s: Nat, +file: Nat, -keep: Nat, -i: Nat, r: CB.Row, ne: {Nat.is_eq(i, keep) == False{} : Bool}) -> {CB.stop_row(s, CB.relabel_row(s, file, r)) == CronBeats.rebound_row_spec(s, file, keep, i, r) : CB.Row}:
  match r:
    case CB.Row{+s2, +fl, +hb, +f}:
      %Equal.sym(Bool, Nat.is_eq(i, keep), False{}, ne) : {CB.stop_row(s, CB.relabel.go(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), s, file, s2, fl, hb, f)) == CronBeats.moved_row_spec(Bool.or(Nat.is_eq(s2, s), Nat.is_eq(fl, file)), _, s, file, s2, fl, hb, f) : CB.Row}
      bs.stop_go(Nat.is_eq(s2, s), Nat.is_eq(fl, file), s, file, s2, fl, hb, f, {==})

# past the kept record, every moved heartbeat stops
def bs.past(rs: List<&2, CB.Row>, +s: Nat, +file: Nat, +keep: Nat, +j: Nat, +lt: {Nat.is_lt(keep, j) == True{} : Bool}) -> {CB.stop_beats(s, CB.relabel(s, file, rs)) == CronBeats.rebound_spec(rs, s, file, keep, j) : List<&2, CB.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %bs.stop_row(s, file, keep, j, r, bs.ne_gt(keep, j, lt)) : {CB.stop_row(s, CB.relabel_row(s, file, r)) <> CB.stop_beats(s, CB.relabel(s, file, t)) == _ <> CronBeats.rebound_spec(t, s, file, keep, 1n+j) : List<&2, CB.Row>}
      %bs.past(t, s, file, keep, 1n+j, bs.lt_succ(keep, j, lt)) : {CB.stop_row(s, CB.relabel_row(s, file, r)) <> CB.stop_beats(s, CB.relabel(s, file, t)) == CB.stop_row(s, CB.relabel_row(s, file, r)) <> _ : List<&2, CB.Row>}
      {==}

# the code counts the kept record down: it is the one at index k + i
def bs.keep_at(rs: List<&2, CB.Row>, k: Nat, +s: Nat, +file: Nat, +i: Nat) -> {CB.stop_but(s, k, CB.relabel(s, file, rs)) == CronBeats.rebound_spec(rs, s, file, Nat.add(k, i), i) : List<&2, CB.Row>}:
  match rs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case +r <> t:
      match k:
        case 0n:
          %bs.kept_row(s, file, i, r) : {CB.relabel_row(s, file, r) <> CB.stop_beats(s, CB.relabel(s, file, t)) == _ <> CronBeats.rebound_spec(t, s, file, i, 1n+i) : List<&2, CB.Row>}
          %bs.past(t, s, file, i, 1n+i, bs.lt_self(i)) : {CB.relabel_row(s, file, r) <> CB.stop_beats(s, CB.relabel(s, file, t)) == CB.relabel_row(s, file, r) <> _ : List<&2, CB.Row>}
          {==}
        case 1n++q:
          %bs.stop_row(s, file, 1n+Nat.add(q, i), i, r, bs.ne_lt(i, 1n+Nat.add(q, i), bs.lt_add(q, i))) : {CB.stop_row(s, CB.relabel_row(s, file, r)) <> CB.stop_but(s, q, CB.relabel(s, file, t)) == _ <> CronBeats.rebound_spec(t, s, file, 1n+Nat.add(q, i), 1n+i) : List<&2, CB.Row>}
          %bs.add_succ(q, i) : {CB.stop_row(s, CB.relabel_row(s, file, r)) <> CB.stop_but(s, q, CB.relabel(s, file, t)) == CB.stop_row(s, CB.relabel_row(s, file, r)) <> CronBeats.rebound_spec(t, s, file, _, 1n+i) : List<&2, CB.Row>}
          %bs.keep_at(t, q, s, file, 1n+i) : {CB.stop_row(s, CB.relabel_row(s, file, r)) <> CB.stop_but(s, q, CB.relabel(s, file, t)) == CB.stop_row(s, CB.relabel_row(s, file, r)) <> _ : List<&2, CB.Row>}
          {==}

# CronBeats

def CronBeats.cron_beats_step_exact(a, rs):
  match a:
    case CB.AHeartbeat{+s, +file, +p, +at}:
      %bs.beat_rows(s, rs) : {CronBeats.new_row_spec(s, file, True{}, p, at) <> CB.stop_beats(s, rs) == CronBeats.new_row_spec(s, file, True{}, p, at) <> _ : List<&2, CB.Row>}
      {==}
    case CB.AJob{s, file, p, at}:
      {==}
    case CB.AOn{i, op}:
      LCb.de.on(i, op, rs)
    case CB.ARebind{+s, +file, +keep}:
      %bs.add_zero(keep) : {CB.stop_but(s, keep, CB.relabel(s, file, rs)) == CronBeats.rebound_spec(rs, s, file, _, 0n) : List<&2, CB.Row>}
      bs.keep_at(rs, keep, s, file, 0n)
    case CB.ALose{}:
      {==}
