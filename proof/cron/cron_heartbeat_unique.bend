# eukhe: the proof of LAW cron_heartbeat_unique

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron.bend as Cron
import ./base/logic.bend as LALogic

# Every store action keeps at most one live heartbeat of session s: a new
# heartbeat of s stops every other first; a rebind onto s stops all of
# them but one; every other action only ends heartbeats of s or moves them
# to another session (a record that is a live heartbeat of s after it was
# one before).

# Bools
# -----

def hu.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def hu.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LALogic.cron.pc.absurdF({b == True{} : Bool}, h)

def hu.and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      LALogic.cron.pc.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

def hu.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def hu.or_not_l(b: Bool, -x: Bool, e: {b == False{} : Bool}) -> {Bool.or(Bool.not(b), x) == True{} : Bool}:
  match b:
    case True{}:
      LALogic.cron.pc.absurd({Bool.or(Bool.not(True{}), x) == True{} : Bool}, e)
    case False{}:
      {==}

def hu.not_and(b: Bool, -n: Bool, e: {b == False{} : Bool}, h: {n == True{} : Bool}) -> {Bool.and(Bool.not(b), n) == True{} : Bool}:
  match b:
    case True{}:
      LALogic.cron.pc.absurd({Bool.and(Bool.not(True{}), n) == True{} : Bool}, e)
    case False{}:
      h

def hu.and_false(-G: Type, a: Bool, -x: Bool, ne: {a == False{} : Bool}, h: {Bool.and(a, x) == True{} : Bool}) -> G:
  match a:
    case True{}:
      LALogic.cron.pc.absurd(G, ne)
    case False{}:
      LALogic.cron.pc.absurdF(G, h)

# a live heartbeat after a change of its facts that only ends jobs was one
# before: the session and the source stay
def hu.and_mono(e: Bool, h: Bool, -a2: Bool, -a: Bool, imp: {a2 == True{} : Bool} -> {a == True{} : Bool}, H: {Bool.and(e, Bool.and(h, a2)) == True{} : Bool}) -> {Bool.and(e, Bool.and(h, a)) == True{} : Bool}:
  match e:
    case False{}:
      H
    case True{}:
      match h:
        case False{}:
          H
        case True{}:
          imp(H)

# a record that is a live heartbeat of s after the change was one before;
# the lists of records stay alike: no live heartbeat, at most one
def hu.cons_no(by: Bool, bx: Bool, -ny: Bool, -nx: Bool, imp: {by == True{} : Bool} -> {bx == True{} : Bool}, hx: {Bool.and(Bool.not(bx), nx) == True{} : Bool}, ih: {nx == True{} : Bool} -> {ny == True{} : Bool}) -> {Bool.and(Bool.not(by), ny) == True{} : Bool}:
  match by:
    case True{}:
      match bx:
        case True{}:
          LALogic.cron.pc.absurdF({Bool.and(Bool.not(True{}), ny) == True{} : Bool}, hx)
        case False{}:
          LALogic.cron.pc.absurdF({Bool.and(Bool.not(True{}), ny) == True{} : Bool}, imp({==}))
    case False{}:
      match bx:
        case True{}:
          LALogic.cron.pc.absurdF({Bool.and(Bool.not(False{}), ny) == True{} : Bool}, hx)
        case False{}:
          ih(hx)

def hu.cons_one(by: Bool, bx: Bool, +ny: Bool, +nx: Bool, +oy: Bool, +ox: Bool, imp: {by == True{} : Bool} -> {bx == True{} : Bool}, +hx: {Bool.and(Bool.or(Bool.not(bx), nx), ox) == True{} : Bool}, ihn: {nx == True{} : Bool} -> {ny == True{} : Bool}, iho: {ox == True{} : Bool} -> {oy == True{} : Bool}) -> {Bool.and(Bool.or(Bool.not(by), ny), oy) == True{} : Bool}:
  match by:
    case True{}:
      match bx:
        case True{}:
          hu.and_intro(ny, oy, ihn(hu.and_l(nx, ox, hx)), iho(hu.and_r(nx, ox, hx)))
        case False{}:
          LALogic.cron.pc.absurdF({Bool.and(Bool.or(Bool.not(True{}), ny), oy) == True{} : Bool}, imp({==}))
    case False{}:
      match bx:
        case True{}:
          iho(hu.and_r(nx, ox, hx))
        case False{}:
          iho(hx)

# Statuses
# --------

def hu.live_stop(b: Bool, f: CS.Fact) -> {Cron.live_fact_spec(CB.stop_if(b, f)) == True{} : Bool} -> {Cron.live_fact_spec(f) == True{} : Bool}:
  match b:
    case False{}:
      h => h
    case True{}:
      match f:
        case CS.Fact{st, p, nx, k}:
          match st:
            case Cr.Active{}:
              h => {==}
            case Cr.Paused{}:
              h => {==}
            case Cr.Finished{}:
              h => h
            case Cr.Cancelled{}:
              h => h

def hu.dead_h(b: Bool, hb: Bool, f: CS.Fact) -> {Bool.and(b, Bool.and(hb, Cron.live_fact_spec(CB.stop_if(Bool.and(b, hb), f)))) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      match hb:
        case False{}:
          {==}
        case True{}:
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

# a decision on a finished or cancelled job leaves it ended
def hu.ended_apply(st: Cr.Status, op: CB.Op, +p: CS.Plan, +nx: Maybe<&2, Nat>, +k: Nat, e: {Cron.live_spec(st) == False{} : Bool}) -> {Cron.live_fact_spec(CB.apply(op, CS.Fact{st, p, nx, k})) == True{} : Bool} -> {False{} == True{} : Bool}:
  match st:
    case Cr.Active{}:
      LALogic.cron.pc.absurd({Cron.live_fact_spec(CB.apply(op, CS.Fact{Cr.Active{}, p, nx, k})) == True{} : Bool} -> {False{} == True{} : Bool}, e)
    case Cr.Paused{}:
      LALogic.cron.pc.absurd({Cron.live_fact_spec(CB.apply(op, CS.Fact{Cr.Paused{}, p, nx, k})) == True{} : Bool} -> {False{} == True{} : Bool}, e)
    case Cr.Finished{}:
      match op:
        case CB.OTake{c, d, n, r}:
          h => h
        case CB.ORecover{c}:
          match c:
            case True{}:
              h => h
            case False{}:
              h => h
        case CB.OFinish{u, a, b, n, r}:
          h => h
        case CB.OCancel{}:
          h => h
        case CB.OResume{n, r}:
          h => h
        case CB.OHalt{how}:
          match how:
            case CS.HPause{}:
              h => h
            case CS.HStop{}:
              h => h
            case CS.HDelete{}:
              h => h
        case CB.OEdit{at}:
          h => h
    case Cr.Cancelled{}:
      match op:
        case CB.OTake{c, d, n, r}:
          h => h
        case CB.ORecover{c}:
          match c:
            case True{}:
              h => h
            case False{}:
              h => h
        case CB.OFinish{u, a, b, n, r}:
          h => h
        case CB.OCancel{}:
          h => h
        case CB.OResume{n, r}:
          h => h
        case CB.OHalt{how}:
          match how:
            case CS.HPause{}:
              h => h
            case CS.HStop{}:
              h => h
            case CS.HDelete{}:
              h => h
        case CB.OEdit{at}:
          h => h

def hu.live_apply(op: CB.Op, f: CS.Fact) -> {Cron.live_fact_spec(CB.apply(op, f)) == True{} : Bool} -> {Cron.live_fact_spec(f) == True{} : Bool}:
  match f:
    case CS.Fact{st, p, nx, k}:
      match st:
        case Cr.Active{}:
          h => {==}
        case Cr.Paused{}:
          h => {==}
        case Cr.Finished{}:
          hu.ended_apply(Cr.Finished{}, op, p, nx, k, {==})
        case Cr.Cancelled{}:
          hu.ended_apply(Cr.Cancelled{}, op, p, nx, k, {==})

# Records
# -------

def hu.stop_mono(+s: Nat, +s1: Nat, r: CB.Row) -> {Cron.beat_spec(s, CB.stop_row(s1, r)) == True{} : Bool} -> {Cron.beat_spec(s, r) == True{} : Bool}:
  match r:
    case CB.Row{+s2, fl, +hb, +f}:
      h => hu.and_mono(Nat.is_eq(s2, s), hb, Cron.live_fact_spec(CB.stop_if(Bool.and(Nat.is_eq(s2, s1), hb), f)), Cron.live_fact_spec(f), hu.live_stop(Bool.and(Nat.is_eq(s2, s1), hb), f), h)

def hu.stop_dead(+s: Nat, r: CB.Row) -> {Cron.beat_spec(s, CB.stop_row(s, r)) == False{} : Bool}:
  match r:
    case CB.Row{s2, fl, hb, f}:
      hu.dead_h(Nat.is_eq(s2, s), hb, f)

def hu.on_mono(+s: Nat, +op: CB.Op, r: CB.Row) -> {Cron.beat_spec(s, CB.on_row(op, r)) == True{} : Bool} -> {Cron.beat_spec(s, r) == True{} : Bool}:
  match r:
    case CB.Row{s2, fl, +hb, +f}:
      h => hu.and_mono(Nat.is_eq(s2, s), hb, Cron.live_fact_spec(CB.apply(op, f)), Cron.live_fact_spec(f), hu.live_apply(op, f), h)

def hu.relabel_h(b: Bool, +s: Nat, +s1: Nat, +file: Nat, +s2: Nat, +fl: Nat, +hb: Bool, +f: CS.Fact, ne: {Nat.is_eq(s1, s) == False{} : Bool}) -> {Cron.beat_spec(s, CB.relabel.go(b, s1, file, s2, fl, hb, f)) == True{} : Bool} -> {Cron.beat_spec(s, CB.Row{s2, fl, hb, f}) == True{} : Bool}:
  match b:
    case False{}:
      h => h
    case True{}:
      h => hu.and_false({Cron.beat_spec(s, CB.Row{s2, fl, hb, f}) == True{} : Bool}, Nat.is_eq(s1, s), Bool.and(hb, Cron.live_fact_spec(f)), ne, h)

# a rebind onto another session moves no record into s
def hu.relabel_mono(+s: Nat, +s1: Nat, +file: Nat, ne: {Nat.is_eq(s1, s) == False{} : Bool}, r: CB.Row) -> {Cron.beat_spec(s, CB.relabel_row(s1, file, r)) == True{} : Bool} -> {Cron.beat_spec(s, r) == True{} : Bool}:
  match r:
    case CB.Row{+s2, +fl, +hb, +f}:
      hu.relabel_h(Bool.or(Nat.is_eq(s2, s1), Nat.is_eq(fl, file)), s, s1, file, s2, fl, hb, f, ne)

# Lists
# -----

def hu.stop_no(+s: Nat, +s1: Nat, rs: List<&2, CB.Row>, h: {Cron.no_beat_spec(s, rs) == True{} : Bool}) -> {Cron.no_beat_spec(s, CB.stop_beats(s1, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      hu.cons_no(Cron.beat_spec(s, CB.stop_row(s1, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_beats(s1, t)), Cron.no_beat_spec(s, t), hu.stop_mono(s, s1, r), h, q => hu.stop_no(s, s1, t, q))

def hu.stop_one(+s: Nat, +s1: Nat, rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.stop_beats(s1, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      hu.cons_one(Cron.beat_spec(s, CB.stop_row(s1, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_beats(s1, t)), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, CB.stop_beats(s1, t)), Cron.one_beat_spec(s, t), hu.stop_mono(s, s1, r), h, q => hu.stop_no(s, s1, t, q), q => hu.stop_one(s, s1, t, q))

def hu.stop_none(+s: Nat, rs: List<&2, CB.Row>) -> {Cron.no_beat_spec(s, CB.stop_beats(s, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      hu.not_and(Cron.beat_spec(s, CB.stop_row(s, r)), Cron.no_beat_spec(s, CB.stop_beats(s, t)), hu.stop_dead(s, r), hu.stop_none(s, t))

def hu.no_one(+s: Nat, rs: List<&2, CB.Row>, h: {Cron.no_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      +nt = hu.and_r(Bool.not(Cron.beat_spec(s, r)), Cron.no_beat_spec(s, t), h)
      hu.and_intro(Bool.or(Bool.not(Cron.beat_spec(s, r)), Cron.no_beat_spec(s, t)), Cron.one_beat_spec(s, t), hu.or_r(Bool.not(Cron.beat_spec(s, r)), Cron.no_beat_spec(s, t), nt), hu.no_one(s, t, nt))

def hu.on_no(+s: Nat, i: Nat, +op: CB.Op, rs: List<&2, CB.Row>, h: {Cron.no_beat_spec(s, rs) == True{} : Bool}) -> {Cron.no_beat_spec(s, CB.on(i, op, rs)) == True{} : Bool}:
  match i:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_no(Cron.beat_spec(s, CB.on_row(op, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, t), Cron.no_beat_spec(s, t), hu.on_mono(s, op, r), h, q => q)
    case 1n++j:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_no(Cron.beat_spec(s, r), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.on(j, op, t)), Cron.no_beat_spec(s, t), q => q, h, q => hu.on_no(s, j, op, t, q))

def hu.on_one(+s: Nat, i: Nat, +op: CB.Op, rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.on(i, op, rs)) == True{} : Bool}:
  match i:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_one(Cron.beat_spec(s, CB.on_row(op, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, t), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, t), Cron.one_beat_spec(s, t), hu.on_mono(s, op, r), h, q => q, q => q)
    case 1n++j:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_one(Cron.beat_spec(s, r), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.on(j, op, t)), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, CB.on(j, op, t)), Cron.one_beat_spec(s, t), q => q, h, q => hu.on_no(s, j, op, t, q), q => hu.on_one(s, j, op, t, q))

def hu.relabel_no(+s: Nat, +s1: Nat, +file: Nat, +ne: {Nat.is_eq(s1, s) == False{} : Bool}, rs: List<&2, CB.Row>, h: {Cron.no_beat_spec(s, rs) == True{} : Bool}) -> {Cron.no_beat_spec(s, CB.relabel(s1, file, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      hu.cons_no(Cron.beat_spec(s, CB.relabel_row(s1, file, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.relabel(s1, file, t)), Cron.no_beat_spec(s, t), hu.relabel_mono(s, s1, file, ne, r), h, q => hu.relabel_no(s, s1, file, ne, t, q))

def hu.relabel_one(+s: Nat, +s1: Nat, +file: Nat, +ne: {Nat.is_eq(s1, s) == False{} : Bool}, rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.relabel(s1, file, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      hu.cons_one(Cron.beat_spec(s, CB.relabel_row(s1, file, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.relabel(s1, file, t)), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, CB.relabel(s1, file, t)), Cron.one_beat_spec(s, t), hu.relabel_mono(s, s1, file, ne, r), h, q => hu.relabel_no(s, s1, file, ne, t, q), q => hu.relabel_one(s, s1, file, ne, t, q))

def hu.but_no_mono(+s: Nat, +s1: Nat, k: Nat, rs: List<&2, CB.Row>, h: {Cron.no_beat_spec(s, rs) == True{} : Bool}) -> {Cron.no_beat_spec(s, CB.stop_but(s1, k, rs)) == True{} : Bool}:
  match k:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_no(Cron.beat_spec(s, r), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_beats(s1, t)), Cron.no_beat_spec(s, t), q => q, h, q => hu.stop_no(s, s1, t, q))
    case 1n++j:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_no(Cron.beat_spec(s, CB.stop_row(s1, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_but(s1, j, t)), Cron.no_beat_spec(s, t), hu.stop_mono(s, s1, r), h, q => hu.but_no_mono(s, s1, j, t, q))

def hu.but_one_mono(+s: Nat, +s1: Nat, k: Nat, rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.stop_but(s1, k, rs)) == True{} : Bool}:
  match k:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_one(Cron.beat_spec(s, r), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_beats(s1, t)), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, CB.stop_beats(s1, t)), Cron.one_beat_spec(s, t), q => q, h, q => hu.stop_no(s, s1, t, q), q => hu.stop_one(s, s1, t, q))
    case 1n++j:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.cons_one(Cron.beat_spec(s, CB.stop_row(s1, r)), Cron.beat_spec(s, r), Cron.no_beat_spec(s, CB.stop_but(s1, j, t)), Cron.no_beat_spec(s, t), Cron.one_beat_spec(s, CB.stop_but(s1, j, t)), Cron.one_beat_spec(s, t), hu.stop_mono(s, s1, r), h, q => hu.but_no_mono(s, s1, j, t, q), q => hu.but_one_mono(s, s1, j, t, q))

# a rebind onto s keeps one heartbeat of s at most
def hu.but_one(+s: Nat, k: Nat, rs: List<&2, CB.Row>) -> {Cron.one_beat_spec(s, CB.stop_but(s, k, rs)) == True{} : Bool}:
  match k:
    case 0n:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          +nt = hu.stop_none(s, t)
          hu.and_intro(Bool.or(Bool.not(Cron.beat_spec(s, r)), Cron.no_beat_spec(s, CB.stop_beats(s, t))), Cron.one_beat_spec(s, CB.stop_beats(s, t)), hu.or_r(Bool.not(Cron.beat_spec(s, r)), Cron.no_beat_spec(s, CB.stop_beats(s, t)), nt), hu.no_one(s, CB.stop_beats(s, t), nt))
    case 1n++j:
      match rs:
        case Nil{}:
          {==}
        case +r <> +t:
          hu.and_intro(Bool.or(Bool.not(Cron.beat_spec(s, CB.stop_row(s, r))), Cron.no_beat_spec(s, CB.stop_but(s, j, t))), Cron.one_beat_spec(s, CB.stop_but(s, j, t)), hu.or_not_l(Cron.beat_spec(s, CB.stop_row(s, r)), Cron.no_beat_spec(s, CB.stop_but(s, j, t)), hu.stop_dead(s, r)), hu.but_one(s, j, t))

# Actions
# -------

def hu.beat_new(b: Bool, +s: Nat, +s1: Nat, +rs: List<&2, CB.Row>, e: {Nat.is_eq(s1, s) == b : Bool}, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Bool.and(Bool.or(Bool.not(Bool.and(b, True{})), Cron.no_beat_spec(s, CB.stop_beats(s1, rs))), Cron.one_beat_spec(s, CB.stop_beats(s1, rs))) == True{} : Bool}:
  match b:
    case False{}:
      hu.stop_one(s, s1, rs, h)
    case True{}:
      +eq = LALogic.cron.pc.eq_of(s1, s, e)
      %Equal.sym(Nat, s1, s, eq) : {Bool.and(Bool.or(Bool.not(True{}), Cron.no_beat_spec(s, CB.stop_beats(_, rs))), Cron.one_beat_spec(s, CB.stop_beats(_, rs))) == True{} : Bool}
      +nt = hu.stop_none(s, rs)
      hu.and_intro(Cron.no_beat_spec(s, CB.stop_beats(s, rs)), Cron.one_beat_spec(s, CB.stop_beats(s, rs)), nt, hu.no_one(s, CB.stop_beats(s, rs), nt))

def hu.job_new(b: Bool, +s: Nat, +rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Bool.and(Bool.or(Bool.not(Bool.and(b, False{})), Cron.no_beat_spec(s, rs)), Cron.one_beat_spec(s, rs)) == True{} : Bool}:
  match b:
    case False{}:
      h
    case True{}:
      h

def hu.rebind(b: Bool, +s: Nat, +s1: Nat, +file: Nat, +keep: Nat, +rs: List<&2, CB.Row>, e: {Nat.is_eq(s1, s) == b : Bool}, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.stop_but(s1, keep, CB.relabel(s1, file, rs))) == True{} : Bool}:
  match b:
    case False{}:
      hu.but_one_mono(s, s1, keep, CB.relabel(s1, file, rs), hu.relabel_one(s, s1, file, e, rs, h))
    case True{}:
      +eq = LALogic.cron.pc.eq_of(s1, s, e)
      %Equal.sym(Nat, s1, s, eq) : {Cron.one_beat_spec(s, CB.stop_but(_, keep, CB.relabel(_, file, rs))) == True{} : Bool}
      hu.but_one(s, keep, CB.relabel(s, file, rs))

def hu.step_one(+s: Nat, a: CB.Act, +rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.step(a, rs)) == True{} : Bool}:
  match a:
    case CB.AHeartbeat{+s1, file, p, at}:
      hu.beat_new(Nat.is_eq(s1, s), s, s1, rs, {==}, h)
    case CB.AJob{+s1, file, p, at}:
      hu.job_new(Nat.is_eq(s1, s), s, rs, h)
    case CB.AOn{i, op}:
      hu.on_one(s, i, op, rs, h)
    case CB.ARebind{+s1, file, keep}:
      hu.rebind(Nat.is_eq(s1, s), s, s1, file, keep, rs, {==}, h)
    case CB.ALose{}:
      {==}

def hu.go_one(+s: Nat, acts: List<&2, CB.Act>, +rs: List<&2, CB.Row>, h: {Cron.one_beat_spec(s, rs) == True{} : Bool}) -> {Cron.one_beat_spec(s, CB.go(acts, rs)) == True{} : Bool}:
  match acts:
    case Nil{}:
      h
    case +a <> t:
      hu.go_one(s, t, CB.step(a, rs), hu.step_one(s, a, rs, h))

# Cron

def Cron.cron_heartbeat_unique(s, acts):
  hu.go_one(s, acts, Nil{}, {==})
