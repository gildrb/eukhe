# proof_wait: the wait laws of LAWS.bend (H6): a wait ends exactly once,
# no later than its deadline or its cancel, and with the event when the
# event comes first. Each lemma speaks of an open wait whose deadline
# passes on the (m + 1)-th tick (`pw.up` names that deadline in ticks
# from now), by induction on the signals it sees.

import Base
import ./wait.bend as W

# Logic
# -----

def pw.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pw.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pw.BD(_, Unit, A)
  Unit{}

def pw.or_true(a: Bool) -> {True{} == Bool.or(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.le0(t: Nat) -> {True{} == Nat.is_le(0n, t) : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a deadline of 0 ticks is reached, whatever came
def pw.reached0(+a: Bool, +c: Bool, t: Nat) -> {True{} == Bool.or(a, Bool.or(c, Nat.is_le(0n, t))) : Bool}:
  %pw.le0(t) : {True{} == Bool.or(a, Bool.or(c, _)) : Bool}
  %pw.or_true(c) : {True{} == Bool.or(a, _) : Bool}
  pw.or_true(a)

# the deadline, in ticks from now, of an open wait
def pw.up(l: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match l:
    case None{}:
      None{}
    case Some{m}:
      Some{1n+m}

# an ended wait reports nothing more
def pw.over(xs: List<&2, W.Sig>) -> {Nil{} == W.go(xs, W.Over{}) : List<&2, W.End>}:
  match xs:
    case Nil{}:
      {==}
    case s <> rest:
      pw.over(rest)

# Exactly once
# ------------

def pw.once(xs: List<&2, W.Sig>, +l: Maybe<&2, Nat>) -> {List.length(&2, W.End, W.go(xs, W.Open{l})) == W.once(W.exits(pw.up(l), xs)) : Nat}:
  match xs:
    case Nil{}:
      match l:
        case None{}:
          {==}
        case Some{m}:
          {==}
    case s <> +rest:
      match s:
        case W.Arrive{}:
          %pw.over(rest) : {1n+List.length(&2, W.End, _) == 1n : Nat}
          {==}
        case W.Cancel{}:
          %pw.over(rest) : {1n+List.length(&2, W.End, _) == W.once(Bool.or(W.has_arrive(rest), True{})) : Nat}
          %pw.or_true(W.has_arrive(rest)) : {1n == W.once(_) : Nat}
          {==}
        case W.Tick{}:
          match l:
            case None{}:
              pw.once(rest, None{})
            case Some{m}:
              match m:
                case 0n:
                  %pw.over(rest) : {1n+List.length(&2, W.End, _) == W.once(Bool.or(W.has_arrive(rest), Bool.or(W.has_cancel(rest), Nat.is_le(0n, W.ticks(rest))))) : Nat}
                  %pw.reached0(W.has_arrive(rest), W.has_cancel(rest), W.ticks(rest)) : {1n == W.once(_) : Nat}
                  {==}
                case 1n+q:
                  pw.once(rest, Some{q})

# No later than the deadline or the cancel
# ----------------------------------------

def pw.bound(pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, +l: Maybe<&2, Nat>, stop: {W.stops(pw.up(l), pre) == True{} : Bool}) -> {W.go(List.append(&2, W.Sig, pre, post), W.Open{l}) == W.go(pre, W.Open{l}) : List<&2, W.End>}:
  match pre:
    case Nil{}:
      match l:
        case None{}:
          pw.absurd({W.go(post, W.Open{None{}}) == Nil{} : List<&2, W.End>}, Equal.sym(Bool, False{}, True{}, stop))
        case Some{m}:
          pw.absurd({W.go(post, W.Open{Some{m}}) == Nil{} : List<&2, W.End>}, Equal.sym(Bool, False{}, True{}, stop))
    case s <> +rest:
      match s:
        case W.Arrive{}:
          %pw.over(List.append(&2, W.Sig, rest, post)) : {W.Arrived{} <> _ == W.Arrived{} <> W.go(rest, W.Over{}) : List<&2, W.End>}
          %pw.over(rest) : {[W.Arrived{}] == W.Arrived{} <> _ : List<&2, W.End>}
          {==}
        case W.Cancel{}:
          %pw.over(List.append(&2, W.Sig, rest, post)) : {W.Cancelled{} <> _ == W.Cancelled{} <> W.go(rest, W.Over{}) : List<&2, W.End>}
          %pw.over(rest) : {[W.Cancelled{}] == W.Cancelled{} <> _ : List<&2, W.End>}
          {==}
        case W.Tick{}:
          match l:
            case None{}:
              pw.bound(rest, post, None{}, stop)
            case Some{m}:
              match m:
                case 0n:
                  %pw.over(List.append(&2, W.Sig, rest, post)) : {W.Expired{} <> _ == W.Expired{} <> W.go(rest, W.Over{}) : List<&2, W.End>}
                  %pw.over(rest) : {[W.Expired{}] == W.Expired{} <> _ : List<&2, W.End>}
                  {==}
                case 1n+q:
                  pw.bound(rest, post, Some{q}, stop)

# The first exit wins
# -------------------

def pw.arrive(pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, +l: Maybe<&2, Nat>, calm: {W.exits(pw.up(l), pre) == False{} : Bool}) -> {W.go(List.append(&2, W.Sig, pre, W.Arrive{} <> post), W.Open{l}) == [W.Arrived{}] : List<&2, W.End>}:
  match pre:
    case Nil{}:
      %pw.over(post) : {W.Arrived{} <> _ == [W.Arrived{}] : List<&2, W.End>}
      {==}
    case s <> +rest:
      match s:
        case W.Arrive{}:
          pw.absurd({W.go(List.append(&2, W.Sig, W.Arrive{} <> rest, W.Arrive{} <> post), W.Open{l}) == [W.Arrived{}] : List<&2, W.End>}, calm)
        case W.Cancel{}:
          pw.absurd({W.go(List.append(&2, W.Sig, W.Cancel{} <> rest, W.Arrive{} <> post), W.Open{l}) == [W.Arrived{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(rest), True{}), False{}, pw.or_true(W.has_arrive(rest)), calm))
        case W.Tick{}:
          match l:
            case None{}:
              pw.arrive(rest, post, None{}, calm)
            case Some{m}:
              match m:
                case 0n:
                  pw.absurd({W.go(List.append(&2, W.Sig, W.Tick{} <> rest, W.Arrive{} <> post), W.Open{Some{0n}}) == [W.Arrived{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(rest), Bool.or(W.has_cancel(rest), Nat.is_le(0n, W.ticks(rest)))), False{}, pw.reached0(W.has_arrive(rest), W.has_cancel(rest), W.ticks(rest)), calm))
                case 1n+q:
                  pw.arrive(rest, post, Some{q}, calm)

def pw.cancel(pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, +l: Maybe<&2, Nat>, calm: {W.exits(pw.up(l), pre) == False{} : Bool}) -> {W.go(List.append(&2, W.Sig, pre, W.Cancel{} <> post), W.Open{l}) == [W.Cancelled{}] : List<&2, W.End>}:
  match pre:
    case Nil{}:
      %pw.over(post) : {W.Cancelled{} <> _ == [W.Cancelled{}] : List<&2, W.End>}
      {==}
    case s <> +rest:
      match s:
        case W.Arrive{}:
          pw.absurd({W.go(List.append(&2, W.Sig, W.Arrive{} <> rest, W.Cancel{} <> post), W.Open{l}) == [W.Cancelled{}] : List<&2, W.End>}, calm)
        case W.Cancel{}:
          pw.absurd({W.go(List.append(&2, W.Sig, W.Cancel{} <> rest, W.Cancel{} <> post), W.Open{l}) == [W.Cancelled{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(rest), True{}), False{}, pw.or_true(W.has_arrive(rest)), calm))
        case W.Tick{}:
          match l:
            case None{}:
              pw.cancel(rest, post, None{}, calm)
            case Some{m}:
              match m:
                case 0n:
                  pw.absurd({W.go(List.append(&2, W.Sig, W.Tick{} <> rest, W.Cancel{} <> post), W.Open{Some{0n}}) == [W.Cancelled{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(rest), Bool.or(W.has_cancel(rest), Nat.is_le(0n, W.ticks(rest)))), False{}, pw.reached0(W.has_arrive(rest), W.has_cancel(rest), W.ticks(rest)), calm))
                case 1n+q:
                  pw.cancel(rest, post, Some{q}, calm)

# The laws
# --------

def wait_ends_once(+dl: Maybe<&2, Nat>, +xs: List<&2, W.Sig>) -> {List.length(&2, W.End, W.run(dl, xs)) == W.once(W.exits(dl, xs)) : Nat}:
  match dl:
    case None{}:
      pw.once(xs, None{})
    case Some{d}:
      match d:
        case 0n:
          %pw.reached0(W.has_arrive(xs), W.has_cancel(xs), W.ticks(xs)) : {1n == W.once(_) : Nat}
          {==}
        case 1n+m:
          pw.once(xs, Some{m})

def wait_end_is_final(+dl: Maybe<&2, Nat>, +pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, stop: {W.stops(dl, pre) == True{} : Bool}) -> {W.run(dl, List.append(&2, W.Sig, pre, post)) == W.run(dl, pre) : List<&2, W.End>}:
  match dl:
    case None{}:
      pw.bound(pre, post, None{}, stop)
    case Some{d}:
      match d:
        case 0n:
          {==}
        case 1n+m:
          pw.bound(pre, post, Some{m}, stop)

def wait_arrival_wins(+dl: Maybe<&2, Nat>, +pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, calm: {W.exits(dl, pre) == False{} : Bool}) -> {W.run(dl, List.append(&2, W.Sig, pre, W.Arrive{} <> post)) == [W.Arrived{}] : List<&2, W.End>}:
  match dl:
    case None{}:
      pw.arrive(pre, post, None{}, calm)
    case Some{d}:
      match d:
        case 0n:
          pw.absurd({[W.Expired{}] == [W.Arrived{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(pre), Bool.or(W.has_cancel(pre), Nat.is_le(0n, W.ticks(pre)))), False{}, pw.reached0(W.has_arrive(pre), W.has_cancel(pre), W.ticks(pre)), calm))
        case 1n+m:
          pw.arrive(pre, post, Some{m}, calm)

def wait_cancel_wins(+dl: Maybe<&2, Nat>, +pre: List<&2, W.Sig>, +post: List<&2, W.Sig>, calm: {W.exits(dl, pre) == False{} : Bool}) -> {W.run(dl, List.append(&2, W.Sig, pre, W.Cancel{} <> post)) == [W.Cancelled{}] : List<&2, W.End>}:
  match dl:
    case None{}:
      pw.cancel(pre, post, None{}, calm)
    case Some{d}:
      match d:
        case 0n:
          pw.absurd({[W.Expired{}] == [W.Cancelled{}] : List<&2, W.End>}, Equal.trans(Bool, True{}, Bool.or(W.has_arrive(pre), Bool.or(W.has_cancel(pre), Nat.is_le(0n, W.ticks(pre)))), False{}, pw.reached0(W.has_arrive(pre), W.has_cancel(pre), W.ticks(pre)), calm))
        case 1n+m:
          pw.cancel(pre, post, Some{m}, calm)
