# eukhe: the proof of LAW config_ffi_refuses
# The entry answers what the reader reads (LFT.pto.ffi): a refusal is the
# error form; a decision never opens with it (LFT.pto.reply_not_err).

import Base
import ../../bend/config.bend as Cf
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/config.bend as Config
import ../../spec/settings/config.bend as CS
import ../base/logic/logic.bend as LLogicLogic
import ./base/ffi_total.bend as LFT

def pcrf.go(+s: String, m: Maybe<&2, FC.Ask>, ef: {FC.ffi(s) == LFT.pto.of(m) : String}, bad: {LawsBase.wire_opens_err(FC.ffi(s)) == True{} : Bool}) -> {FC.ffi(s) == Wr.err("config: malformed request") : String}:
  match m:
    case None{}:
      ef
    case Some{+a}:
      +ft = Equal.trans(Bool, False{}, LawsBase.wire_opens_err(FC.ffi(s)), True{}, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(CS.cf_w_reply(a)), LawsBase.wire_opens_err(FC.ffi(s)), Equal.sym(Bool, LawsBase.wire_opens_err(CS.cf_w_reply(a)), False{}, LFT.pto.reply_not_err(a)), Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), CS.cf_w_reply(a), FC.ffi(s), Equal.sym(String, FC.ffi(s), CS.cf_w_reply(a), ef))), bad)
      LLogicLogic.ppr.absurdF({FC.ffi(s) == Wr.err("config: malformed request") : String}, ft)

def Config.config_ffi_refuses(s, bad):
  pcrf.go(s, CS.cf_read(s), LFT.pto.ffi(s), bad)
