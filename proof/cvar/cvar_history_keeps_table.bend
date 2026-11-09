# eukhe: the proof of LAW cvar_history_keeps_table
#
# PROOF: a spelled table that fits opens its press state
# (cvar_open_answers_spelled); every arm of a press (a key read whole,
# input left over, a malformed key) keeps the table it was given (chk.st),
# so by induction on the inputs each reply is the one the opened table
# gives that input alone (chk.feed).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ./cvar_open_answers_spelled.bend as PCvarOpenAnswersSpelled

# a press keeps the table, whatever the decoder read
def chk.st(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, d: Wr.Dec<Nat>) -> {CvarEntry.cvar_st_of(FCv.step.key(bs, as, d)) == FCv.Table{bs, as} : FCv.St}:
  match d:
    case Wr.Got{k, r}:
      match r:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}

# from the press state of a table, the replies are the fresh ones
def chk.feed(ins: List<&2, String>, +bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>) -> {CvarEntry.cvar_feed(ins, FCv.Table{bs, as}) == CvarEntry.cvar_fresh(ins, bs, as) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case Con{+i, +rest}:
      %Equal.sym(FCv.St, CvarEntry.cvar_st_of(FCv.step(FCv.Table{bs, as}, i)), FCv.Table{bs, as}, chk.st(bs, as, Wr.get_nat(i))) : {CvarEntry.cvar_reply_of(FCv.step(FCv.Table{bs, as}, i)) <> CvarEntry.cvar_feed(rest, _) == CvarEntry.cvar_reply_of(FCv.step(FCv.Table{bs, as}, i)) <> CvarEntry.cvar_fresh(rest, bs, as) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => CvarEntry.cvar_reply_of(FCv.step(FCv.Table{bs, as}, i)) <> z, CvarEntry.cvar_feed(rest, FCv.Table{bs, as}), CvarEntry.cvar_fresh(rest, bs, as), chk.feed(rest, bs, as))

def CvarEntry.cvar_history_keeps_table(bs, as, fits, ins):
  +sp = CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, ""))
  %Equal.sym(FCv.St & String, FCv.open(sp), (FCv.Table{bs, as}, ""), CvarEntry.cvar_open_answers_spelled(bs, as, fits)) : {CvarEntry.cvar_feed(ins, CvarEntry.cvar_st_of(_)) == CvarEntry.cvar_fresh(ins, bs, as) : List<&2, String>}
  chk.feed(ins, bs, as)
