# eukhe: the proof of LAW slash_suggest_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (slash_suggest_entry_reads), so the entry answers the code's suggestion
# (pinned by slash_suggest_first_nearest), spelled.

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ./slash_suggest_entry_reads.bend as PSlashSuggestEntryReads

def ssa.put(m: Maybe<&2, Nat>) -> {FSs.put_answer(m) == SlashSuggest.sp_w_answer(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      {==}

def ssa.reply(q: FSs.Req) -> {FSs.answer(q) == SlashSuggest.sp_w_reply(q) : String}:
  match q:
    case FSs.QSuggest{+w, +cs}:
      ssa.put(Ss.suggest(w, cs))

def SlashSuggest.slash_suggest_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FSs.Req>, FSs.get_req(SlashSuggest.sp_w_req(q, "")), Wr.Got{q, ""}, SlashSuggest.slash_suggest_entry_reads(q, "", h)) : {FSs.ffi.got(_) == SlashSuggest.sp_w_reply(q) : String}
  ssa.reply(q)
