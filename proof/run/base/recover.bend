# eukhe: lemmas the proofs of laws/run/recover.bend share: what
# decide.recover does with leaked calls and a repeat, each row fed back
# (rr.*); the row lemmas of the stop area's proofs (LR.str.*) do the
# arithmetic

import Base
import ../../../bend/run/state.bend as RnState
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/decision.bend as RnDecision
import ../../../laws/run/recover.bend as RunRecover
import ../../stop/base/recover.bend as LR

# leak: under the cap, the next note
def rr.leak_under(+q: Nat, +j: Nat, +l0: Nat, +re: Nat, +rp: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, j) == RnDecision.Redoes{1n+j} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, LR.str.below_add(q, j)) : {RnDecision.Help.of(RnRecovery.rec.leak(_, j, 0n, 0n, RnRecovery.Rec{RnRecovery.Leaks{}, j, 0n, 0n})) == RnDecision.Redoes{1n+j} : RnDecision.Help}
  {==}

# leak: at the cap, or past it, the run fails
def rr.leak_past(+j: Nat, +x: Nat, +l0: Nat, +re: Nat, +rp: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, j, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, Nat.add(j, x)) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(Nat.add(j, x), j), False{}, LR.str.past(j, x)) : {RnDecision.Help.of(RnRecovery.rec.leak(_, Nat.add(j, x), 0n, 0n, RnRecovery.Rec{RnRecovery.Leaks{}, Nat.add(j, x), 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

def rr.leak_cap(+j: Nat, +l0: Nat, +re: Nat, +rp: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, j, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, j) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, LR.str.below_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.leak(_, j, 0n, 0n, RnRecovery.Rec{RnRecovery.Leaks{}, j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

# leak: from j notes with m under the cap, m notes, then the run fails
def rr.leak_go(m: Nat, +j: Nat, +l0: Nat, +re: Nat, +rp: Nat) -> {RunRecover.helps(1n+m, RnRecovery.RCfg{l0, Nat.add(m, j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, Nat.add(m, j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, j)) == RunRecover.notes_then_quit(m, j) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{l0, j, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, j), RnDecision.Quits{}, rr.leak_cap(j, l0, re, rp)) : {RunRecover.helps(1n, RnRecovery.RCfg{l0, j, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, _) == RunRecover.notes_then_quit(0n, j) : List<&2, RnDecision.Help>}
      {==}
    case 1n++q:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, j), RnDecision.Redoes{1n+j}, rr.leak_under(q, j, l0, re, rp)) : {RunRecover.helps(2n+q, RnRecovery.RCfg{l0, 1n+Nat.add(q, j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, _) == RunRecover.notes_then_quit(1n+q, j) : List<&2, RnDecision.Help>}
      %LR.str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> RunRecover.helps(1n+q, RnRecovery.RCfg{l0, _, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, _, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 1n+j)) == RnDecision.Redoes{1n+j} <> RunRecover.notes_then_quit(q, 1n+j) : List<&2, RnDecision.Help>}
      %rr.leak_go(q, 1n+j, l0, re, rp) : {RnDecision.Redoes{1n+j} <> RunRecover.helps(1n+q, RnRecovery.RCfg{l0, Nat.add(q, 1n+j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, Nat.add(q, 1n+j), re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 1n+j)) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# leak: a note of another recovery counts no leak note
def rr.leak_first(k: RnRecovery.Rk, +row: Nat, +long: Nat, le: Nat, +re: Nat, +rp: Nat, other: {RunRecover.leak_note(k) == False{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, k, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 0n) : RnDecision.Help}:
  match k:
    case RnRecovery.Free{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Longs{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Leaks{}:
      LR.str.absurd_t({RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 0n) : RnDecision.Help}, other)
    case RnRecovery.Loops{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case RnRecovery.Empties{}:
      match le:
        case 0n:
          {==}
        case 1n+z:
          {==}

# leak: after a note that is no leak note, notes 1 to the cap, then the run fails
def rr.leak_part(+k: RnRecovery.Rk, +row: Nat, +long: Nat, +le: Nat, +re: Nat, +rp: Nat, other: {RunRecover.leak_note(k) == False{} : Bool}) -> {RunRecover.helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, k, row)) == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}:
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, k, row), RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 0n), rr.leak_first(k, row, long, le, re, rp, other)) : {RunRecover.helps(1n+le, RnRecovery.RCfg{long, le, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, _) == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}
  %LR.str.add_zero(le) : {RunRecover.helps(1n+le, RnRecovery.RCfg{long, _, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, RnDecision.decide.recover(RnRecovery.RCfg{long, _, re, rp}, RnDecision.Leaked{}, RnRecovery.Leaks{}, 0n)) == RunRecover.notes_then_quit(le, 0n) : List<&2, RnDecision.Help>}
  rr.leak_go(le, 0n, long, re, rp)

# repeat: the calls of a repeat make before + 1 rounds in a row
def rr.again(+before: Nat) -> {RnRecovery.again(before, 0n, 0n) == 1n+before : Nat}:
  match before:
    case 0n:
      {==}
    case 1n+b:
      {==}

# b <= a, so a is not below b
def rr.le_not_below(+a: Nat, +b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {RnRecovery.below(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LR.str.absurd({RnRecovery.below(0n, 1n+q) == False{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rr.le_not_below(p, q, e)

# calls that would make `repeat` or more rounds in a row are no fresh calls
def rr.rep_off(+before: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp) == False{} : Bool}:
  %Equal.sym(Nat, RnRecovery.again(before, 0n, 0n), 1n+before, rr.again(before)) : {RnRecovery.below(_, rp) == False{} : Bool}
  rr.le_not_below(1n+before, rp, rep)

# calls below the cap are fresh
def rr.rep_on(+before: Nat, +rp: Nat, fresh: {Nat.is_lt(1n+before, rp) == True{} : Bool}) -> {RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp) == True{} : Bool}:
  %Equal.sym(Nat, RnRecovery.again(before, 0n, 0n), 1n+before, rr.again(before)) : {RnRecovery.below(_, rp) == True{} : Bool}
  LR.str.lt_below(1n+before, rp, fresh)

# repeat: under the redirect cap, the next redirect note
def rr.rep_under(+q: Nat, +j: Nat, +before: Nat, +l0: Nat, +le: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, j) == RnDecision.Redoes{1n+j} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp), False{}, rr.rep_off(before, rp, rep)) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, RnRecovery.again(before, 0n, 0n), 0n, j, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, j, before, 0n})) == RnDecision.Redoes{1n+j} : RnDecision.Help}
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, LR.str.below_add(q, j)) : {RnDecision.Help.of(RnRecovery.rec.ran(False{}, _, True{}, RnRecovery.again(before, 0n, 0n), 0n, j, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, j, before, 0n})) == RnDecision.Redoes{1n+j} : RnDecision.Help}
  {==}

# repeat: at the redirect cap or past it, the run fails
def rr.rep_past(+j: Nat, +x: Nat, +before: Nat, +l0: Nat, +le: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, le, j, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, Nat.add(j, x)) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp), False{}, rr.rep_off(before, rp, rep)) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(Nat.add(j, x), j), True{}, RnRecovery.again(before, 0n, 0n), 0n, Nat.add(j, x), before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(j, x), before, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  %Equal.sym(Bool, RnRecovery.below(Nat.add(j, x), j), False{}, LR.str.past(j, x)) : {RnDecision.Help.of(RnRecovery.rec.ran(False{}, _, True{}, RnRecovery.again(before, 0n, 0n), 0n, Nat.add(j, x), before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, Nat.add(j, x), before, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

def rr.rep_cap(+j: Nat, +before: Nat, +l0: Nat, +le: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, le, j, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, j) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp), False{}, rr.rep_off(before, rp, rep)) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(j, j), True{}, RnRecovery.again(before, 0n, 0n), 0n, j, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, j, before, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, LR.str.below_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.ran(False{}, _, True{}, RnRecovery.again(before, 0n, 0n), 0n, j, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, j, before, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

# repeat: from j redirect notes with m under the cap, m notes, then the run fails
def rr.rep_go(m: Nat, +j: Nat, +before: Nat, +l0: Nat, +le: Nat, +rp: Nat, +rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}) -> {RunRecover.helps(1n+m, RnRecovery.RCfg{l0, le, Nat.add(m, j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, Nat.add(m, j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, j)) == RunRecover.notes_then_quit(m, j) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, j, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, j), RnDecision.Quits{}, rr.rep_cap(j, before, l0, le, rp, rep)) : {RunRecover.helps(1n, RnRecovery.RCfg{l0, le, j, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, _) == RunRecover.notes_then_quit(0n, j) : List<&2, RnDecision.Help>}
      {==}
    case 1n++q:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, j), RnDecision.Redoes{1n+j}, rr.rep_under(q, j, before, l0, le, rp, rep)) : {RunRecover.helps(2n+q, RnRecovery.RCfg{l0, le, 1n+Nat.add(q, j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, _) == RunRecover.notes_then_quit(1n+q, j) : List<&2, RnDecision.Help>}
      %LR.str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> RunRecover.helps(1n+q, RnRecovery.RCfg{l0, le, _, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, _, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 1n+j)) == RnDecision.Redoes{1n+j} <> RunRecover.notes_then_quit(q, 1n+j) : List<&2, RnDecision.Help>}
      %rr.rep_go(q, 1n+j, before, l0, le, rp, rep) : {RnDecision.Redoes{1n+j} <> RunRecover.helps(1n+q, RnRecovery.RCfg{l0, le, Nat.add(q, 1n+j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, Nat.add(q, 1n+j), rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 1n+j)) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# with no redirect note counted, the act does not read the note's recovery
def rr.rep_ran0(-k: RnRecovery.Rk, -row: Nat, -before: Nat, re: Nat) -> {RnDecision.Help.of(RnRecovery.rec.ran(False{}, RnRecovery.below(0n, re), True{}, RnRecovery.again(before, 0n, 0n), 0n, 0n, before, 0n, RnRecovery.Rec{k, row, before, 0n})) == RnDecision.Help.of(RnRecovery.rec.ran(False{}, RnRecovery.below(0n, re), True{}, RnRecovery.again(before, 0n, 0n), 0n, 0n, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, 0n, before, 0n})) : RnDecision.Help}:
  match re:
    case 0n:
      {==}
    case 1n+z:
      {==}

# repeat: a note that counts no redirect note (loops 0) starts the row as no note does
def rr.rep_first_at(+k: RnRecovery.Rk, +row: Nat, +before: Nat, +l0: Nat, +le: Nat, re: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}, zero: {RnRecovery.Rk.loops(k, row) == 0n : Nat}) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, k, row) == RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 0n) : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(RnRecovery.again(before, 0n, 0n), rp), False{}, rr.rep_off(before, rp, rep)) : {RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(RnRecovery.Rk.loops(k, row), re), True{}, RnRecovery.again(before, 0n, 0n), 0n, RnRecovery.Rk.loops(k, row), before, 0n, RnRecovery.Rec{k, row, before, 0n})) == RnDecision.Help.of(RnRecovery.rec.ran(_, RnRecovery.below(0n, re), True{}, RnRecovery.again(before, 0n, 0n), 0n, 0n, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, 0n, before, 0n})) : RnDecision.Help}
  %Equal.sym(Nat, RnRecovery.Rk.loops(k, row), 0n, zero) : {RnDecision.Help.of(RnRecovery.rec.ran(False{}, RnRecovery.below(_, re), True{}, RnRecovery.again(before, 0n, 0n), 0n, _, before, 0n, RnRecovery.Rec{k, row, before, 0n})) == RnDecision.Help.of(RnRecovery.rec.ran(False{}, RnRecovery.below(0n, re), True{}, RnRecovery.again(before, 0n, 0n), 0n, 0n, before, 0n, RnRecovery.Rec{RnRecovery.Loops{}, 0n, before, 0n})) : RnDecision.Help}
  rr.rep_ran0(k, row, before, re)

def rr.rep_first(k: RnRecovery.Rk, +row: Nat, +before: Nat, +l0: Nat, +le: Nat, re: Nat, +rp: Nat, rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}, other: {RunRecover.loop_note(k) == False{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, k, row) == RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 0n) : RnDecision.Help}:
  match k:
    case RnRecovery.Free{}:
      rr.rep_first_at(RnRecovery.Free{}, row, before, l0, le, re, rp, rep, {==})
    case RnRecovery.Longs{}:
      rr.rep_first_at(RnRecovery.Longs{}, row, before, l0, le, re, rp, rep, {==})
    case RnRecovery.Leaks{}:
      rr.rep_first_at(RnRecovery.Leaks{}, row, before, l0, le, re, rp, rep, {==})
    case RnRecovery.Loops{}:
      LR.str.absurd_t({RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, row) == RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 0n) : RnDecision.Help}, other)
    case RnRecovery.Empties{}:
      rr.rep_first_at(RnRecovery.Empties{}, row, before, l0, le, re, rp, rep, {==})

def rr.rep_part(+k: RnRecovery.Rk, +row: Nat, +before: Nat, +l0: Nat, +le: Nat, +re: Nat, +rp: Nat, +rep: {Nat.is_le(rp, 1n+before) == True{} : Bool}, other: {RunRecover.loop_note(k) == False{} : Bool}) -> {RunRecover.helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, k, row)) == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}:
  %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, k, row), RnDecision.decide.recover(RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 0n), rr.rep_first(k, row, before, l0, le, re, rp, rep, other)) : {RunRecover.helps(1n+re, RnRecovery.RCfg{l0, le, re, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, _) == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}
  %LR.str.add_zero(re) : {RunRecover.helps(1n+re, RnRecovery.RCfg{l0, le, _, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, RnDecision.decide.recover(RnRecovery.RCfg{l0, le, _, rp}, RnDecision.Repeats{before}, RnRecovery.Loops{}, 0n)) == RunRecover.notes_then_quit(re, 0n) : List<&2, RnDecision.Help>}
  rr.rep_go(re, 0n, before, l0, le, rp, rep)
