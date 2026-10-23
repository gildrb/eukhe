# eukhe: the proof of LAW child_entry_move

import Base
import ../../bend/child.bend as Ch
import ../../bend/wire.bend as Wr
import ../../bend/ffi_child.bend as FCh
import ../../LAWS.bend as Laws
import ../base.bend as L

def pw6.fate(f: Ch.Fate, +rest: String) -> {Wr.Got{f, rest} == FCh.get_fate(FCh.put_fate(f, rest)) : Wr.Dec<Ch.Fate>}:
  match f:
    case Ch.Queued{}:
      %L.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Queued{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}
    case Ch.Withdrawn{}:
      %L.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Withdrawn{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}
    case Ch.Placed{}:
      %L.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Placed{}, rest} == FCh.get_fate.go(_) : Wr.Dec<Ch.Fate>}
      {==}

def pw6.mfate(f: Maybe<&2, Ch.Fate>, +rest: String) -> {Wr.Got{f, rest} == FCh.get_mfate(FCh.put_mfate(f, rest)) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match f:
    case None{}:
      %L.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}
    case Some{+x}:
      %L.pw6.nat(1n, FCh.put_fate(x, rest), {==}) : {Wr.Got{Some{x}, rest} == FCh.get_mfate.go(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      %pw6.fate(x, rest) : {Wr.Got{Some{x}, rest} == FCh.get_mfate.some(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}

def Laws.child_entry_move(f, n, hn):
  +R = FCh.put_move(Ch.owe.next(f, n), "")
  %L.pw6.nat(1n, FCh.put_mfate(f, Wr.put_nat(n, "")), {==}) : {FCh.run(_) == R : String}
  %pw6.mfate(f, Wr.put_nat(n, "")) : {FCh.move.f(_) == R : String}
  %L.pw6.nat(n, "", hn) : {FCh.move.n(f, _) == R : String}
  {==}
