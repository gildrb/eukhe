# eukhe: the proof of LAW theme_ffi_refuses
# The entry answers a decision, which never opens with 'E'
# (LTE.tx.reply_ok), or its one error form.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_theme.bend as FTh
import ../../laws/base.bend as LawsBase
import ../../laws/theme_entry.bend as ThemeEntry
import ./base.bend as LTE

def tr.refuse(d: Wr.Dec<FTh.Req>, bad: {LawsBase.wire_opens_err(FTh.run(d)) == True{} : Bool}) -> {FTh.run(d) == Wr.err("theme: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LTE.tx.absurd({FTh.reply(q) == Wr.err("theme: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTh.reply(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTh.reply(q)), True{}, bad), LTE.tx.reply_ok(q)))
        case SCon{y, z}:
          {==}
    case Wr.Bad{}:
      {==}

def ThemeEntry.theme_ffi_refuses(s, bad):
  tr.refuse(FTh.get_req.go(Wr.get_nat(s)), bad)
