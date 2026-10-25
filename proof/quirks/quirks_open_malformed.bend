# eukhe: the proof of LAW quirks_open_malformed
# The entry reads every open as the laws' reader does; where that reader
# finds no open, the entry answers the error form and keeps no rulebook.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def om.pair(known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>, no: {Quirks.read_open.pair(known, m) == None{} : Maybe<&2, Quirks.QsOpen>}) -> {FQ.open.book(known, m) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}:
  match m:
    case None{}:
      {==}
    case Some{rs}:
      QP.qp.some_none(Quirks.QsOpen, Quirks.QsOpen{known, rs}, {FQ.open.book(known, Some{rs}) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}, no)

def om.end(b: Bool, +known: List<&2, Nat>, +xs: List<&2, Nat>, no: {Quirks.read_open.end(b, known, xs) == None{} : Maybe<&2, Quirks.QsOpen>}) -> {FQ.open.end(b, known, xs) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, If.Rule>>, FQ.rules(xs), Quirks.read_rules(xs), QP.qp.rules_read(xs)) : {FQ.open.book(known, _) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}
      om.pair(known, Quirks.read_rules(xs), no)
    case False{}:
      {==}

def om.rules(+known: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>, no: {Quirks.read_open.rules(known, d) == None{} : Maybe<&2, Quirks.QsOpen>}) -> {FQ.open.rules(known, d) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}:
  match d:
    case Wr.Got{xs, s}:
      om.end(Wr.end(s), known, xs, no)
    case Wr.Bad{}:
      {==}

def om.known(d: Wr.Dec<List<&2, Nat>>, no: {Quirks.read_open.known(d) == None{} : Maybe<&2, Quirks.QsOpen>}) -> {FQ.open.known(d) == (FQ.Shut{}, SCon{'E', SCon{' ', "quirks: malformed rulebook"}}) : FQ.St & String}:
  match d:
    case Wr.Got{known, s}:
      om.rules(known, Wr.get_list(~Nat, ~Wr.get_nat, s), no)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_open_malformed(s, no):
  om.known(Wr.get_list(~Nat, ~Wr.get_nat, s), no)
