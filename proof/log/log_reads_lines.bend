# eukhe: the proof of LAW log_reads_lines

import Base
import ../../bend/log.bend as Lg
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Parsing
# -------

def pl.parse_data(t: List<&2, Nat>) -> {Lg.P{Nil{}, t} == Lg.parse(Lg.data(t)) : Lg.P}:
  match t:
    case Nil{}:
      {==}
    case +x <> rest:
      %pl.parse_data(rest) : {Lg.P{Nil{}, x <> rest} == Lg.byte(1n+x, _) : Lg.P}
      {==}

# the law log_reads_lines
def pl.reads_lines(+ls: List<&2, List<&2, Nat>>, +t: List<&2, Nat>) -> {Lg.recover(List.append(&2, Nat, Lg.render(ls), Lg.data(t))) == ls : List<&2, List<&2, Nat>>}:
  %LA.pl.recover_render(ls, Lg.data(t)) : {_ == ls : List<&2, List<&2, Nat>>}
  %pl.parse_data(t) : {List.append(&2, List<&2, Nat>, ls, Lg.P.ls(_)) == ls : List<&2, List<&2, Nat>>}
  %LA.pl.app_nil(List<&2, Nat>, ls) : {_ == ls : List<&2, List<&2, Nat>>}
  {==}

# (D2) Storage and cron

def Laws.log_reads_lines(ls, t):
  pl.reads_lines(ls, t)
