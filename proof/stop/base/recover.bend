# eukhe: lemmas of the proofs of laws/stop/recover.bend: the model's row
# test (`below`) against Nat's order, `recover` at the rungs of the
# ladder (str.think_*), at the notes of a cut reply with text (str.cut_*),
# the window test (str.bound_*), the reply of each act
# (str.never_answers), and a row of kept rounds (str.rep_*).

import Base
import ../../../bend/run/state.bend as RnState
import ../../../bend/run/step.bend as RnStep
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/decision.bend as RnDecision
import ../../../laws/stop/recover.bend as StopRecover

# Logic
# -----

def str.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def str.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : str.BD(_, A, Unit)
  Unit{}

def str.absurd_t(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : str.BD(_, Unit, A)
  Unit{}

def str.and_and_false(a: Bool, b: Bool) -> {Bool.and(a, Bool.and(b, False{})) == False{} : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# Nat
# ---

def str.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %str.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def str.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %str.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def str.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      str.eq_refl(p)

def str.succ_not_eq(+m: Nat) -> {Nat.is_eq(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      str.succ_not_eq(q)

def str.lt_not_le(+a: Nat, +b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      str.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, e)
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      str.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, e)
    case 1n++p 1n++q:
      str.lt_not_le(p, q, e)

def str.add_not_lt(+c: Nat, +x: Nat) -> {Nat.is_lt(Nat.add(c, x), c) == False{} : Bool}:
  match c:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n++y:
          {==}
    case 1n++d:
      str.add_not_lt(d, x)

# The row test
# ------------

def str.below(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == RnRecovery.below(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      str.below(p, q)

def str.below_refl(+a: Nat) -> {RnRecovery.below(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      str.below_refl(p)

def str.succ_not_below(+m: Nat) -> {RnRecovery.below(1n+m, m) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      str.succ_not_below(q)

# j is below j plus one more
def str.below_add(+q: Nat, +j: Nat) -> {RnRecovery.below(j, 1n+Nat.add(q, j)) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      %Equal.sym(Nat, Nat.add(q, 1n+i), 1n+Nat.add(q, i), str.add_succ(q, i)) : {RnRecovery.below(i, _) == True{} : Bool}
      str.below_add(q, i)

# a row past a + x is never below a
def str.past(+a: Nat, +x: Nat) -> {RnRecovery.below(Nat.add(a, x), a) == False{} : Bool}:
  match a:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n++y:
          {==}
    case 1n++b:
      str.past(b, x)

def str.below_pred(+a: Nat, +b: Nat, h: {RnRecovery.below(1n+a, b) == True{} : Bool}) -> {RnRecovery.below(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      str.absurd({RnRecovery.below(0n, 0n) == True{} : Bool}, h)
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      str.absurd({RnRecovery.below(1n+p, 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      str.below_pred(p, q, h)

def str.below_shrink(q: Nat, +j: Nat, +b: Nat, h: {RnRecovery.below(2n+Nat.add(q, j), b) == True{} : Bool}) -> {RnRecovery.below(2n+j, b) == True{} : Bool}:
  match q:
    case 0n:
      h
    case 1n++r:
      str.below_shrink(r, j, b, str.below_pred(2n+Nat.add(r, j), b, h))

def str.below_one(q: Nat, +b: Nat, h: {RnRecovery.below(1n+q, b) == True{} : Bool}) -> {RnRecovery.below(1n, b) == True{} : Bool}:
  match q:
    case 0n:
      h
    case 1n++r:
      str.below_one(r, b, str.below_pred(1n+r, b, h))

def str.below_move(-a: Nat, -b: Nat, +rp: Nat, e: {a == b : Nat}, h: {RnRecovery.below(a, rp) == True{} : Bool}) -> {RnRecovery.below(b, rp) == True{} : Bool}:
  %e : {RnRecovery.below(_, rp) == True{} : Bool}
  h

def str.lt_below(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {RnRecovery.below(a, b) == True{} : Bool}:
  Equal.trans(Bool, RnRecovery.below(a, b), Nat.is_lt(a, b), True{}, Equal.sym(Bool, Nat.is_lt(a, b), RnRecovery.below(a, b), str.below(a, b)), h)

# The ladder (no compaction to run)
# ---------------------------------

# under the cap: the next length note
def str.think_under(+q: Nat, +j: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat, +lower: Bool) -> {RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, j) == RnDecision.Redoes{1n+j} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, str.below_add(q, j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(lower, Nat.is_eq(j, 1n+Nat.add(q, j))), j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Redoes{1n+j} : RnDecision.Help}
  {==}

# at the cap with a lower level: the next note one level lower
def str.think_lower(+j: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, True{}}, RnRecovery.Longs{}, j) == RnDecision.Lowers{1n+j} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, str.below_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(True{}, Nat.is_eq(j, j)), j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Lowers{1n+j} : RnDecision.Help}
  %Equal.sym(Bool, Nat.is_eq(j, j), True{}, str.eq_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(False{}, Bool.and(True{}, _), j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Lowers{1n+j} : RnDecision.Help}
  {==}

# at the cap with no lower level: the run fails
def str.think_quit(+j: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, j) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, str.below_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(False{}, Nat.is_eq(j, j)), j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

# past the lower rung: the run fails
def str.think_past(lower: Bool, +j: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 1n+j) == RnDecision.Quits{} : RnDecision.Help}:
  match lower:
    case True{}:
      %Equal.sym(Bool, RnRecovery.below(1n+j, j), False{}, str.succ_not_below(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(True{}, Nat.is_eq(1n+j, j)), 1n+j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
      %Equal.sym(Bool, Nat.is_eq(1n+j, j), False{}, str.succ_not_eq(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(False{}, Bool.and(True{}, _), 1n+j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
      {==}
    case False{}:
      %Equal.sym(Bool, RnRecovery.below(1n+j, j), False{}, str.succ_not_below(j)) : {RnDecision.Help.of(RnRecovery.rec.think.note(_, Bool.and(False{}, Nat.is_eq(1n+j, j)), 1n+j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, 1n+j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
      {==}

# from j notes in a row, m under the cap remain: the rest of the ladder
def str.climb_go(m: Nat, +j: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat, +lower: Bool) -> {StopRecover.climb(1n+m, RnRecovery.RCfg{Nat.add(m, j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnDecision.decide.recover(RnRecovery.RCfg{Nat.add(m, j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, j)) == StopRecover.ups(m, j, StopRecover.ladder_end(lower, Nat.add(m, j))) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      match lower:
        case True{}:
          %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, True{}}, RnRecovery.Longs{}, j), RnDecision.Lowers{1n+j}, str.think_lower(j, le, re, rp, w, c, p, o)) : {StopRecover.climb(1n, RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, True{}}, _) == StopRecover.ladder_end(True{}, j) : List<&2, RnDecision.Help>}
          %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, True{}}, RnRecovery.Longs{}, 1n+j), RnDecision.Quits{}, str.think_past(True{}, j, le, re, rp, w, c, p, o)) : {[RnDecision.Lowers{1n+j}, _] == StopRecover.ladder_end(True{}, j) : List<&2, RnDecision.Help>}
          {==}
        case False{}:
          %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, RnRecovery.Longs{}, j), RnDecision.Quits{}, str.think_quit(j, le, re, rp, w, c, p, o)) : {StopRecover.climb(1n, RnRecovery.RCfg{j, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, False{}}, _) == StopRecover.ladder_end(False{}, j) : List<&2, RnDecision.Help>}
          {==}
    case 1n++q:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, j), RnDecision.Redoes{1n+j}, str.think_under(q, j, le, re, rp, w, c, p, o, lower)) : {StopRecover.climb(2n+q, RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, _) == StopRecover.ups(1n+q, j, StopRecover.ladder_end(lower, 1n+Nat.add(q, j))) : List<&2, RnDecision.Help>}
      %str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> StopRecover.climb(1n+q, RnRecovery.RCfg{_, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnDecision.decide.recover(RnRecovery.RCfg{_, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 1n+j)) == RnDecision.Redoes{1n+j} <> StopRecover.ups(q, 1n+j, StopRecover.ladder_end(lower, _)) : List<&2, RnDecision.Help>}
      %str.climb_go(q, 1n+j, le, re, rp, w, c, p, o, lower) : {RnDecision.Redoes{1n+j} <> StopRecover.climb(1n+q, RnRecovery.RCfg{Nat.add(q, 1n+j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnDecision.decide.recover(RnRecovery.RCfg{Nat.add(q, 1n+j), le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 1n+j)) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# after a note that is no length note, the first rung is the one after
# no length note
def str.think_first(k: RnRecovery.Rk, +row: Nat, long: Nat, +le: Nat, +re: Nat, +rp: Nat, +w: Nat, +c: Nat, +p: Nat, +o: Nat, lower: Bool, other: {StopRecover.length_note(k) == False{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 0n) : RnDecision.Help}:
  match k:
    case RnRecovery.Free{}:
      match long:
        case 0n:
          match lower:
            case True{}:
              {==}
            case False{}:
              {==}
        case 1n++q:
          {==}
    case RnRecovery.Longs{}:
      str.absurd_t({RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Thought{w, c, p, o, False{}, lower}, RnRecovery.Longs{}, 0n) : RnDecision.Help}, other)
    case RnRecovery.Leaks{}:
      match long:
        case 0n:
          match lower:
            case True{}:
              {==}
            case False{}:
              {==}
        case 1n++q:
          {==}
    case RnRecovery.Loops{}:
      match long:
        case 0n:
          match lower:
            case True{}:
              {==}
            case False{}:
              {==}
        case 1n++q:
          {==}
    case RnRecovery.Empties{}:
      match long:
        case 0n:
          match lower:
            case True{}:
              {==}
            case False{}:
              {==}
        case 1n++q:
          {==}

# The length notes of a cut reply with text
# -----------------------------------------

# under the cap: the next length note
def str.cut_under(+q: Nat, +j: Nat, +le: Nat, +re: Nat, +rp: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, j) == RnDecision.Redoes{1n+j} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, 1n+Nat.add(q, j)), True{}, str.below_add(q, j)) : {RnDecision.Help.of(RnRecovery.rec.long(_, j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Redoes{1n+j} : RnDecision.Help}
  {==}

# at the cap: the run fails
def str.cut_quit(+j: Nat, +le: Nat, +re: Nat, +rp: Nat) -> {RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, j) == RnDecision.Quits{} : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.below(j, j), False{}, str.below_refl(j)) : {RnDecision.Help.of(RnRecovery.rec.long(_, j, 0n, 0n, RnRecovery.Rec{RnRecovery.Longs{}, j, 0n, 0n})) == RnDecision.Quits{} : RnDecision.Help}
  {==}

# from j notes in a row, m under the cap remain: m notes, then the failure
def str.cut_climb(m: Nat, +j: Nat, +le: Nat, +re: Nat, +rp: Nat) -> {StopRecover.climb(1n+m, RnRecovery.RCfg{Nat.add(m, j), le, re, rp}, RnDecision.Truncated{}, RnDecision.decide.recover(RnRecovery.RCfg{Nat.add(m, j), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, j)) == StopRecover.ups(m, j, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}:
  match m:
    case 0n:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{j, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, j), RnDecision.Quits{}, str.cut_quit(j, le, re, rp)) : {StopRecover.climb(1n, RnRecovery.RCfg{j, le, re, rp}, RnDecision.Truncated{}, _) == [RnDecision.Quits{}] : List<&2, RnDecision.Help>}
      {==}
    case 1n++q:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, j), RnDecision.Redoes{1n+j}, str.cut_under(q, j, le, re, rp)) : {StopRecover.climb(2n+q, RnRecovery.RCfg{1n+Nat.add(q, j), le, re, rp}, RnDecision.Truncated{}, _) == StopRecover.ups(1n+q, j, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}
      %str.add_succ(q, j) : {RnDecision.Redoes{1n+j} <> StopRecover.climb(1n+q, RnRecovery.RCfg{_, le, re, rp}, RnDecision.Truncated{}, RnDecision.decide.recover(RnRecovery.RCfg{_, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 1n+j)) == RnDecision.Redoes{1n+j} <> StopRecover.ups(q, 1n+j, [RnDecision.Quits{}]) : List<&2, RnDecision.Help>}
      %str.cut_climb(q, 1n+j, le, re, rp) : {RnDecision.Redoes{1n+j} <> StopRecover.climb(1n+q, RnRecovery.RCfg{Nat.add(q, 1n+j), le, re, rp}, RnDecision.Truncated{}, RnDecision.decide.recover(RnRecovery.RCfg{Nat.add(q, 1n+j), le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 1n+j)) == RnDecision.Redoes{1n+j} <> _ : List<&2, RnDecision.Help>}
      {==}

# after a note that is no length note, a cut reply gets what it gets
# after no length note
def str.cut_first(k: RnRecovery.Rk, +row: Nat, long: Nat, +le: Nat, +re: Nat, +rp: Nat, other: {StopRecover.length_note(k) == False{} : Bool}) -> {RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, k, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 0n) : RnDecision.Help}:
  match k:
    case RnRecovery.Free{}:
      match long:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case RnRecovery.Longs{}:
      str.absurd_t({RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, row) == RnDecision.decide.recover(RnRecovery.RCfg{long, le, re, rp}, RnDecision.Truncated{}, RnRecovery.Longs{}, 0n) : RnDecision.Help}, other)
    case RnRecovery.Leaks{}:
      match long:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case RnRecovery.Loops{}:
      match long:
        case 0n:
          {==}
        case 1n++q:
          {==}
    case RnRecovery.Empties{}:
      match long:
        case 0n:
          {==}
        case 1n++q:
          {==}

# The window test
# ---------------

def str.bound_true(+w: Nat, +c: Nat, +p: Nat, +o: Nat, below: {Nat.is_lt(o, c) == True{} : Bool}, reach: {Nat.is_le(1n+w, Nat.add(Nat.add(p, o), 8192n)) == True{} : Bool}) -> {RnRecovery.bound(1n+w, c, p, o) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(o, c), True{}, below) : {Bool.and(Nat.is_lt(0n, 1n+w), Bool.and(_, Nat.is_le(1n+w, Nat.add(Nat.add(p, o), 8192n)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+w, Nat.add(Nat.add(p, o), 8192n)), True{}, reach) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

def str.bound_cut(+w: Nat, +c: Nat, +p: Nat, +x: Nat) -> {RnRecovery.bound(w, c, p, Nat.add(c, x)) == False{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n++v:
      %Equal.sym(Bool, Nat.is_lt(Nat.add(c, x), c), False{}, str.add_not_lt(c, x)) : {Bool.and(Nat.is_lt(0n, 1n+v), Bool.and(_, Nat.is_le(1n+v, Nat.add(Nat.add(p, Nat.add(c, x)), 8192n)))) == False{} : Bool}
      {==}

def str.bound_room(+w: Nat, +c: Nat, +p: Nat, +o: Nat, room: {Nat.is_lt(Nat.add(Nat.add(p, o), 8192n), w) == True{} : Bool}) -> {RnRecovery.bound(w, c, p, o) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(w, Nat.add(Nat.add(p, o), 8192n)), False{}, str.lt_not_le(Nat.add(Nat.add(p, o), 8192n), w, room)) : {Bool.and(Nat.is_lt(0n, w), Bool.and(Nat.is_lt(o, c), _)) == False{} : Bool}
  str.and_and_false(Nat.is_lt(0n, w), Nat.is_lt(o, c))

# a window that did not run out: `recover` is the one with no compaction
def str.no_shrink(+rc: RnRecovery.RCfg, +w: Nat, +c: Nat, +p: Nat, +o: Nat, +lower: Bool, +k: RnRecovery.Rk, +row: Nat, no: {RnRecovery.bound(w, c, p, o) == False{} : Bool}) -> {RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, True{}, lower}, k, row) == RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row) : RnDecision.Help}:
  %Equal.sym(Bool, RnRecovery.bound(w, c, p, o), False{}, no) : {RnDecision.Help.of(RnRecovery.rec.go(rc, RnRecovery.Think{Bool.and(True{}, _), lower}, k, row, 0n, 0n)) == RnDecision.decide.recover(rc, RnDecision.Thought{w, c, p, o, False{}, lower}, k, row) : RnDecision.Help}
  {==}

# The acts
# --------

# the reply of an act that helps is no answer, at any counts
def str.never_answers(a: RnRecovery.Act, +q: RnState.Reply, +cfg: RnState.Cfg, +r: Nat, c: Nat, aa: Nat, n: Nat, +pp: Nat, helps: {RnRecovery.Act.helps(a) == True{} : Bool}) -> {StopRecover.is_answer(RnDecision.Then.ph(RnDecision.Reply.noted(RnRecovery.Act.reply(a, q)), RnState.St.ph(RnStep.call(cfg, RnRecovery.Act.reply(a, q), r, c, aa, n, pp)))) == False{} : Bool}:
  match a:
    case RnRecovery.Pass{}:
      str.absurd({StopRecover.is_answer(RnDecision.Then.ph(RnDecision.Reply.noted(q), RnState.St.ph(RnStep.call(cfg, q, r, c, aa, n, pp)))) == False{} : Bool}, helps)
    case RnRecovery.Exec{}:
      {==}
    case RnRecovery.Redo{}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          {==}
    case RnRecovery.Quit{}:
      match aa:
        case 0n:
          {==}
        case 1n++b:
          {==}
    case RnRecovery.Shrink{}:
      match c:
        case 0n:
          {==}
        case 1n++d:
          {==}
    case RnRecovery.Lower{}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          {==}

def str.helps_plain(a: RnRecovery.Act) -> {RnRecovery.Act.helps(a) == Bool.not(StopRecover.is_plain(RnRecovery.Act.reply(a, RnState.Plain{}))) : Bool}:
  match a:
    case RnRecovery.Pass{}:
      {==}
    case RnRecovery.Exec{}:
      {==}
    case RnRecovery.Redo{}:
      {==}
    case RnRecovery.Quit{}:
      {==}
    case RnRecovery.Shrink{}:
      {==}
    case RnRecovery.Lower{}:
      {==}

# A row of kept rounds
# --------------------

# the first round of a run runs and starts a row of 1
def str.rep_start(+h: Nat, +l: Nat, +le: Nat, +re: Nat, +rp: Nat, one: {RnRecovery.below(1n, rp) == True{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Ran{h, True{}}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 0n, 0n}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n, h}} : RnRecovery.Dec}:
  %Equal.sym(Bool, RnRecovery.below(1n, rp), True{}, one) : {RnRecovery.rec.ran(_, RnRecovery.below(0n, re), True{}, 1n, h, 0n, 0n, 0n, RnRecovery.Rec{RnRecovery.Free{}, 0n, 0n, 0n}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n, h}} : RnRecovery.Dec}
  {==}

# a kept round of the last round's calls grows the row by one
def str.rep_step(+j: Nat, +h: Nat, +l: Nat, +le: Nat, +re: Nat, +rp: Nat, two: {RnRecovery.below(2n+j, rp) == True{} : Bool}) -> {RnRecovery.Rec.step(RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Ran{h, True{}}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+j, h}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+j, h}} : RnRecovery.Dec}:
  %Equal.sym(Bool, Nat.is_eq(h, h), True{}, str.eq_refl(h)) : {RnRecovery.rec.ran(RnRecovery.below(RnRecovery.again.eq(_, j), rp), RnRecovery.below(0n, re), True{}, RnRecovery.again.eq(_, j), h, 0n, 1n+j, h, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+j, h}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+j, h}} : RnRecovery.Dec}
  %Equal.sym(Bool, RnRecovery.below(2n+j, rp), True{}, two) : {RnRecovery.rec.ran(_, RnRecovery.below(0n, re), True{}, 2n+j, h, 0n, 1n+j, h, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+j, h}) == RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+j, h}} : RnRecovery.Dec}
  {==}

# after a row of 1 + j, m more kept rounds below the cap make a row of
# 1 + m + j
def str.rep_go(m: Nat, +j: Nat, +h: Nat, +l: Nat, +le: Nat, +re: Nat, +rp: Nat, +prem: {RnRecovery.below(1n+Nat.add(m, j), rp) == True{} : Bool}) -> {RnRecovery.Rec.go(StopRecover.kept_rounds(m, h), RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+j, h}) == RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+Nat.add(m, j), h} : RnRecovery.Rec}:
  match m:
    case 0n:
      {==}
    case 1n++q:
      +two = str.below_shrink(q, j, rp, prem)
      +prem2 = str.below_move(2n+Nat.add(q, j), 1n+Nat.add(q, 1n+j), rp, Equal.cong(Nat, Nat, z => 1n+z, 1n+Nat.add(q, j), Nat.add(q, 1n+j), Equal.sym(Nat, Nat.add(q, 1n+j), 1n+Nat.add(q, j), str.add_succ(q, j))), prem)
      %Equal.sym(RnRecovery.Dec, RnRecovery.Rec.step(RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Ran{h, True{}}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+j, h}), RnRecovery.Dec{RnRecovery.Exec{}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+j, h}}, str.rep_step(j, h, l, le, re, rp, two)) : {RnRecovery.Rec.go(StopRecover.kept_rounds(q, h), RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Dec.r(_)) == RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+Nat.add(q, j), h} : RnRecovery.Rec}
      %str.add_succ(q, j) : {RnRecovery.Rec.go(StopRecover.kept_rounds(q, h), RnRecovery.RCfg{l, le, re, rp}, RnRecovery.Rec{RnRecovery.Free{}, 0n, 2n+j, h}) == RnRecovery.Rec{RnRecovery.Free{}, 0n, 1n+_, h} : RnRecovery.Rec}
      str.rep_go(q, 1n+j, h, l, le, re, rp, prem2)

# a round of other calls than the last round's runs and starts a row of 1
def str.ran_one(kept: Bool, +h2: Nat, +n: Nat, +same: Nat, +h: Nat, +rp: Nat, +ue: Bool, +r: RnRecovery.Rec, one: {RnRecovery.below(1n, rp) == True{} : Bool}) -> {RnRecovery.Dec.act(RnRecovery.rec.ran(RnRecovery.below(1n, rp), ue, kept, 1n, h2, n, same, h, r)) == RnRecovery.Exec{} : RnRecovery.Act} & {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(RnRecovery.below(1n, rp), ue, kept, 1n, h2, n, same, h, r))) == 1n : Nat}:
  match kept:
    case True{}:
      %Equal.sym(Bool, RnRecovery.below(1n, rp), True{}, one) : {RnRecovery.Dec.act(RnRecovery.rec.ran(_, ue, True{}, 1n, h2, n, same, h, r)) == RnRecovery.Exec{} : RnRecovery.Act} & {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(_, ue, True{}, 1n, h2, n, same, h, r))) == 1n : Nat}
      ({==}, {==})
    case False{}:
      %Equal.sym(Bool, RnRecovery.below(1n, rp), True{}, one) : {RnRecovery.Dec.act(RnRecovery.rec.ran(_, ue, False{}, 1n, h2, n, same, h, r)) == RnRecovery.Exec{} : RnRecovery.Act} & {RnRecovery.Rec.same(RnRecovery.Dec.r(RnRecovery.rec.ran(_, ue, False{}, 1n, h2, n, same, h, r))) == 1n : Nat}
      ({==}, {==})
