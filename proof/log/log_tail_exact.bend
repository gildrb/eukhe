# eukhe: the proof of LAW log_tail_exact
#
# The file of the facts has the length of the facts (lte.len) and its last
# newline where the facts put it (lte.none, lte.some): the open's decision
# on it is the spec's (log_open_cuts_the_torn_tail). A newline at or past
# the end is refused (log_open_refuses_odd_facts).

import Base
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ../base/logic/logic.bend as LLogicLogic
import ./log_open_cuts_the_torn_tail.bend as PLogOpenCutsTheTornTail
import ./log_open_refuses_odd_facts.bend as PLogOpenRefusesOddFacts

def lte.len(len: Nat, last: Maybe<&2, Nat>) -> {List.length(&2, Nat, Log.log_file(len, last)) == len : Nat}:
  match len:
    case 0n:
      {==}
    case 1n+k:
      match last:
        case None{}:
          %lte.len(k, None{}) : {1n+List.length(&2, Nat, Log.log_file(k, None{})) == 1n+_ : Nat}
          {==}
        case Some{i}:
          match i:
            case 0n:
              %lte.len(k, None{}) : {1n+List.length(&2, Nat, Log.log_file(k, None{})) == 1n+_ : Nat}
              {==}
            case 1n+j:
              %lte.len(k, Some{j}) : {1n+List.length(&2, Nat, Log.log_file(k, Some{j})) == 1n+_ : Nat}
              {==}

def lte.none(len: Nat) -> {None{} == Log.log_last(Log.log_file(len, None{})) : Maybe<&2, Nat>}:
  match len:
    case 0n:
      {==}
    case 1n+k:
      %lte.none(k) : {None{} == Log.log_last.at(1n, _) : Maybe<&2, Nat>}
      {==}

def lte.some(len: Nat, i: Nat, h: {Nat.is_lt(i, len) == True{} : Bool}) -> {Log.log_last(Log.log_file(len, Some{i})) == Some{i} : Maybe<&2, Nat>}:
  match len:
    case 0n:
      match i:
        case 0n:
          LLogicLogic.wr_absurd({Log.log_last(Log.log_file(0n, Some{0n})) == Some{0n} : Maybe<&2, Nat>}, h)
        case 1n+j:
          LLogicLogic.wr_absurd({Log.log_last(Log.log_file(0n, Some{1n+j})) == Some{1n+j} : Maybe<&2, Nat>}, h)
    case 1n+k:
      match i:
        case 0n:
          %lte.none(k) : {Log.log_last.at(0n, _) == Some{0n} : Maybe<&2, Nat>}
          {==}
        case 1n+j:
          +e = lte.some(k, j, h)
          %Equal.sym(Maybe<&2, Nat>, Log.log_last(Log.log_file(k, Some{j})), Some{j}, e) : {Log.log_last.at(1n, _) == Some{1n+j} : Maybe<&2, Nat>}
          {==}

def lte.in(b: Bool, +len: Nat, +i: Nat, h: {Nat.is_lt(i, len) == b : Bool}) -> {Lr.tail(len, Some{i}) == Log.log_tail_facts.in(b, len, i) : Lr.Tail}:
  match b:
    case True{}:
      +f = Log.log_file(len, Some{i})
      %lte.len(len, Some{i}) : {Lr.tail(_, Some{i}) == Log.log_tail_spec(f) : Lr.Tail}
      %lte.some(len, i, h) : {Lr.tail(List.length(&2, Nat, f), _) == Log.log_tail_spec(f) : Lr.Tail}
      Log.log_open_cuts_the_torn_tail(f)
    case False{}:
      Log.log_open_refuses_odd_facts(len, i, h)

def Log.log_tail_exact(len, last):
  match last:
    case None{}:
      +f = Log.log_file(len, None{})
      %lte.len(len, None{}) : {Lr.tail(_, None{}) == Log.log_tail_spec(f) : Lr.Tail}
      %Equal.sym(Maybe<&2, Nat>, None{}, Log.log_last(f), lte.none(len)) : {Lr.tail(List.length(&2, Nat, f), _) == Log.log_tail_spec(f) : Lr.Tail}
      Log.log_open_cuts_the_torn_tail(f)
    case Some{+i}:
      lte.in(Nat.is_lt(i, len), len, i, {==})
