# eukhe: the proof of LAW rebase_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (fe.req_rt), and the answer to its flat edits is the spec's within the bound, spelled (fe.reply).

import Base
import ../../bend/rebase.bend as R
import ../../bend/ffi_rebase.bend as FR
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/rebase.bend as Rebase
import ./base/entry.bend as LE


def Rebase.rebase_entry_answers(b, h, es, fit):
  %Equal.sym(Wr.Dec<FR.Req>, FR.get_req(Rebase.rb_w_req(b, h, es, "")), Wr.Got{FR.Req{b, h, Rebase.rb_flat(es)}, ""}, LE.fe.req_rt(b, h, es, "", fit)) : {FR.ffi.got(_) == Rebase.rb_w_reply(Rebase.rb_answer(b, h, es)) : String}
  LE.fe.reply(b, h, es)
