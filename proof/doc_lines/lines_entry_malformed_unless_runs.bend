# eukhe: the proof of LAW lines_entry_malformed_unless_runs
#
# PROOF: the runs' decoder reads only spelled runs that fit, the rest
# after them untouched (fle_runs of lines_entry_exact); when it reads none
# the entry dispatches on the first char, and an input that opens with
# neither `L` nor `W` answers the runs' error, which the premise excludes.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../base/ffi_doc_lines/exact.bend as Fdx
import ./lines_entry_exact.bend as PLinesEntryExact

def lmr_Ex(s: String) -> Type:
  &rs: List<&2, Dl.Run> -> &t: String -> ({s == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, t) : String} & {DocLines.lines.WireFits(rs) == True{} : Bool})

# the dispatch on a char that is neither `L` (l) nor `W` (w)
def lmr_pick(l: Bool, w: Bool, -t: String, -G: Type, plain: {Bool.or(l, w) == False{} : Bool},
  other: {String.eq(Fdl.kind.pick(l, w, t), Wr.err("doc_lines: malformed runs")) == False{} : Bool}) -> G:
  match l:
    case True{}:
      Fdx.fdx_absurd(G, plain)
    case False{}:
      match w:
        case True{}:
          Fdx.fdx_absurd(G, plain)
        case False{}:
          Fdx.fdx_absurd(G, other)

# an input that is no plan and opens with neither `L` nor `W`
def lmr_kind(s: String, -G: Type, plain: {DocLines.lines.Marked(s) == False{} : Bool},
  other: {String.eq(Fdl.kind(s), Wr.err("doc_lines: malformed runs")) == False{} : Bool}) -> G:
  match s:
    case SNil{}:
      Fdx.fdx_absurd(G, other)
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          lmr_pick(U32.is_eq(x, 76), U32.is_eq(x, 87), t, G, plain, other)

def lmr_main(+s: String, d: Wr.Dec<List<&2, Dl.Run>>, pd: PLinesEntryExact.fle_pls(s, d),
  plain: {DocLines.lines.Marked(s) == False{} : Bool},
  other: {String.eq(Fdl.run.runs(d, s), Wr.err("doc_lines: malformed runs")) == False{} : Bool}) -> lmr_Ex(s):
  match d:
    case Wr.Got{+rs, +t}:
      (rs, (t, pd))
    case Wr.Bad{}:
      lmr_kind(s, lmr_Ex(s), plain, other)

def DocLines.lines_entry_malformed_unless_runs(s, plain, other):
  lmr_main(s, Wr.get_list(~Dl.Run, ~Fdl.get_run, s), PLinesEntryExact.fle_runs(s), plain, other)
