# eukhe: the proof of LAW quirks_open_total
# The entry reads every open as the laws' reader does (its rules reader is
# the spec's, QP.qp.rules_read); an open read whole compiles exactly when
# every spec verdict is fine (QP.qp.fine_all) and its verdicts are spelled
# as the spec spells them (QP.qp.verdicts); anything else is the error
# form and no rulebook.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def ot.pair(+known: List<&2, Nat>, m: Maybe<&2, List<&2, If.Rule>>) -> {FQ.open.book(known, m) == Quirks.qs_open.of(Quirks.read_open.pair(known, m)) : FQ.St & String}:
  match m:
    case None{}:
      {==}
    case Some{+rs}:
      -rhs = {(Quirks.qs_kept(Quirks.qs_all_fine(rs, known), rs), Wr.put_bool(Quirks.qs_all_fine(rs, known), Quirks.spell_verdicts(known, rs))) : FQ.St & String}
      %Equal.sym(Bool, If.fine_all(If.verdicts.go(rs, known, 0n)), Quirks.qs_all_fine(rs, known), QP.qp.fine_all(rs, known, 0n)) : {FQ.open.reply(_, rs, If.verdicts(known, rs)) == rhs : FQ.St & String}
      %QP.qp.verdicts(known, rs) : {FQ.open.reply(Quirks.qs_all_fine(rs, known), rs, If.verdicts(known, rs)) == (Quirks.qs_kept(Quirks.qs_all_fine(rs, known), rs), Wr.put_bool(Quirks.qs_all_fine(rs, known), _)) : FQ.St & String}
      QP.qp.reply(Quirks.qs_all_fine(rs, known), rs, If.verdicts(known, rs))

def ot.end(b: Bool, +known: List<&2, Nat>, +xs: List<&2, Nat>) -> {FQ.open.end(b, known, xs) == Quirks.qs_open.of(Quirks.read_open.end(b, known, xs)) : FQ.St & String}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, If.Rule>>, FQ.rules(xs), Quirks.read_rules(xs), QP.qp.rules_read(xs)) : {FQ.open.book(known, _) == Quirks.qs_open.of(Quirks.read_open.pair(known, Quirks.read_rules(xs))) : FQ.St & String}
      ot.pair(known, Quirks.read_rules(xs))
    case False{}:
      {==}

def ot.rules(+known: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> {FQ.open.rules(known, d) == Quirks.qs_open.of(Quirks.read_open.rules(known, d)) : FQ.St & String}:
  match d:
    case Wr.Got{xs, s}:
      ot.end(Wr.end(s), known, xs)
    case Wr.Bad{}:
      {==}

def ot.known(d: Wr.Dec<List<&2, Nat>>) -> {FQ.open.known(d) == Quirks.qs_open.of(Quirks.read_open.known(d)) : FQ.St & String}:
  match d:
    case Wr.Got{known, s}:
      ot.rules(known, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def Quirks.quirks_open_total(s):
  ot.known(Wr.get_list(~Nat, ~Wr.get_nat, s))
