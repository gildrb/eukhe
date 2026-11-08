# eukhe: the proof of LAW lines_entry_malformed_unless_carry
#
# PROOF: spelled runs that fit read back with the rest untouched (lea_runs,
# fln_runs), so the entry goes on to the carry's decoder, which reads only
# a spelled ending (fdx_end); when it reads none the entry answers the
# carry's error, which the premise excludes.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/ffi_doc_lines/exact.bend as Fdx
import ./lines_entry_refines.bend as PLinesEntryRefines
import ./lines_entry_answers.bend as PLinesEntryAnswers

def lmc_Ex(t: String) -> Type:
  &c: Dl.End -> &rest: String -> {t == LawsBase.proj_spell_end(c, rest) : String}

# spelled runs that fit read back, the rest untouched
def lmc_read(+rs: List<&2, Dl.Run>, +t: String, +fits: {DocLines.lines.WireFits(rs) == True{} : Bool}) ->
  {Wr.get_list(~Dl.Run, ~Fdl.get_run, Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, t)) == Wr.Got{rs, t} : Wr.Dec<List<&2, Dl.Run>>}:
  %PLinesEntryAnswers.lea_runs(rs, t) : {Wr.get_list(~Dl.Run, ~Fdl.get_run, _) == Wr.Got{rs, t} : Wr.Dec<List<&2, Dl.Run>>}
  PLinesEntryRefines.fln_runs(rs, t, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), fits), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), fits))

# the premise, after the runs read back
def lmc_move(+rs: List<&2, Dl.Run>, +t: String, +fits: {DocLines.lines.WireFits(rs) == True{} : Bool},
  other: {String.eq(Fdl.ffi(Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, t)), Wr.err("doc_lines: malformed carry")) == False{} : Bool}) ->
  {String.eq(Fdl.run.carry(rs, Fdl.get_end(t)), Wr.err("doc_lines: malformed carry")) == False{} : Bool}:
  +input = Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, t)
  Equal.trans(Bool, String.eq(Fdl.run.runs(Wr.Got{rs, t}, input), Wr.err("doc_lines: malformed carry")),
    String.eq(Fdl.run.runs(Wr.get_list(~Dl.Run, ~Fdl.get_run, input), input), Wr.err("doc_lines: malformed carry")), False{},
    Equal.cong(Wr.Dec<List<&2, Dl.Run>>, Bool, d => String.eq(Fdl.run.runs(d, input), Wr.err("doc_lines: malformed carry")),
      Wr.Got{rs, t}, Wr.get_list(~Dl.Run, ~Fdl.get_run, input),
      Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list(~Dl.Run, ~Fdl.get_run, input), Wr.Got{rs, t}, lmc_read(rs, t, fits))),
    other)

def lmc_main(-rs: List<&2, Dl.Run>, -t: String, d: Wr.Dec<Dl.End>, pe: Fdx.fdx_pe(t, d),
  other: {String.eq(Fdl.run.carry(rs, d), Wr.err("doc_lines: malformed carry")) == False{} : Bool}) -> lmc_Ex(t):
  match d:
    case Wr.Got{+c, +r}:
      (c, (r, pe))
    case Wr.Bad{}:
      Fdx.fdx_absurd(lmc_Ex(t), other)

def DocLines.lines_entry_malformed_unless_carry(rs, fits, t, other):
  lmc_main(rs, t, Fdl.get_end(t), Fdx.fdx_end(t), lmc_move(rs, t, fits, other))
