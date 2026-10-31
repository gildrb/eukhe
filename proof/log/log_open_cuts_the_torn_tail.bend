# eukhe: the proof of LAW log_open_cuts_the_torn_tail
#
# A file's length and its last newline are those of its parse (the lines
# and the tail after them: proof/log/base.bend, pl.len_parse and
# pl.last_parse); on a parse, the rule and the spec agree case by case
# (pl.tail_p).

import Base
import ../../spec/durable/log.bend as Lg
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log
import ./base.bend as LA

def Log.log_open_cuts_the_torn_tail(f):
  %LA.pl.last_parse(f) : {Lr.tail(List.length(&2, Nat, f), _) == Log.log_tail_spec(f) : Lr.Tail}
  %LA.pl.len_parse(f) : {Lr.tail(_, LA.pl.lastof(Lg.P.ls(Lg.parse(f)))) == Log.log_tail_spec(f) : Lr.Tail}
  LA.pl.tail_p(Lg.parse(f))
