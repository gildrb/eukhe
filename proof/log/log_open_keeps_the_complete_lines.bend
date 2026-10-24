# eukhe: the proof of LAW log_open_keeps_the_complete_lines
#
# Every file is the bytes of its complete lines, then its tail
# (pl.split); the open's decision is the spec's
# (log_open_cuts_the_torn_tail), and the spec keeps exactly the bytes of
# the lines: the whole file when the tail is empty, else the first
# length-of-the-lines bytes.

import Base
import ../../spec/log.bend as Lg
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./base.bend as LA
import ./log_open_cuts_the_torn_tail.bend as PCut

# the first |xs| bytes of xs ++ ys are xs
def pl.take_app(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {xs == List.take(&2, Nat, List.append(&2, Nat, xs, ys), List.length(&2, Nat, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> rest:
          {==}
    case +x <> rest:
      %pl.take_app(rest, ys) : {x <> rest == x <> _ : List<&2, Nat>}
      {==}

def pl.split_byte(b: Nat, p: Lg.P) -> {List.append(&2, Nat, Lg.render(Lg.P.ls(Lg.byte(b, p))), Lg.data(Lg.P.tl(Lg.byte(b, p)))) == b <> List.append(&2, Nat, Lg.render(Lg.P.ls(p)), Lg.data(Lg.P.tl(p))) : List<&2, Nat>}:
  match b:
    case 0n:
      match p:
        case Lg.P{ls, t}:
          {==}
    case 1n+c:
      match p:
        case Lg.P{ls, t}:
          match ls:
            case Nil{}:
              {==}
            case l <> r:
              {==}

# a file is the bytes of its lines, then its tail
def pl.split(f: List<&2, Nat>) -> {List.append(&2, Nat, Lg.render(Lg.P.ls(Lg.parse(f))), Lg.data(Lg.P.tl(Lg.parse(f)))) == f : List<&2, Nat>}:
  match f:
    case Nil{}:
      {==}
    case +b <> +rest:
      %pl.split(rest) : {List.append(&2, Nat, Lg.render(Lg.P.ls(Lg.byte(b, Lg.parse(rest)))), Lg.data(Lg.P.tl(Lg.byte(b, Lg.parse(rest))))) == b <> _ : List<&2, Nat>}
      pl.split_byte(b, Lg.parse(rest))

# the spec's decision on a parse keeps the bytes of its lines
def pl.kept(p: Lg.P) -> {Log.log_kept(Log.log_tail_spec.p(p), List.append(&2, Nat, Lg.render(Lg.P.ls(p)), Lg.data(Lg.P.tl(p)))) == Some{Lg.render(Lg.P.ls(p))} : Maybe<&2, List<&2, Nat>>}:
  match p:
    case Lg.P{+ls, t}:
      match t:
        case Nil{}:
          %LA.pl.app_nil(Nat, Lg.render(ls)) : {Some{_} == Some{Lg.render(ls)} : Maybe<&2, List<&2, Nat>>}
          {==}
        case x <> rest:
          %pl.take_app(Lg.render(ls), Lg.data(x <> rest)) : {Some{_} == Some{Lg.render(ls)} : Maybe<&2, List<&2, Nat>>}
          {==}

def Log.log_open_keeps_the_complete_lines(f):
  +t = Lr.tail(List.length(&2, Nat, f), Log.log_last(f))
  %Equal.sym(Lr.Tail, t, Log.log_tail_spec(f), Log.log_open_cuts_the_torn_tail(f)) : {Log.log_kept(_, f) == Some{Lg.render(Lg.recover(f))} : Maybe<&2, List<&2, Nat>>}
  %pl.split(f) : {Log.log_kept(Log.log_tail_spec(f), _) == Some{Lg.render(Lg.recover(f))} : Maybe<&2, List<&2, Nat>>}
  pl.kept(Lg.parse(f))
