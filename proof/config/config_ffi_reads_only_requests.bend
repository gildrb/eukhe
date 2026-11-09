# eukhe: the proof of LAW config_ffi_reads_only_requests
# The entry answers what the reader reads (LFT.pto.ffi). The reader
# refusing gives the error form, which the premise excludes; the reader
# reading a request whole means the input is that request spelled
# (LFX.pxe.read_exact), answered with its decision.

import Base
import ../../bend/config.bend as Cf
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/config.bend as Config
import ../../spec/settings/config.bend as CS
import ../base/logic/logic.bend as LLogicLogic
import ./base/ffi_total.bend as LFT
import ./base/ffi_exact.bend as LFX

def pcro.eq(+s: String, +a: FC.Ask, hw: {s == CS.cf_w_ask(a) : String}, ef: {FC.ffi(s) == CS.cf_w_reply(a) : String}) -> {(s, FC.ffi(s)) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}:
  %Equal.sym(String, s, CS.cf_w_ask(a), hw) : {(_, FC.ffi(s)) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}
  %Equal.sym(String, FC.ffi(s), CS.cf_w_reply(a), ef) : {(CS.cf_w_ask(a), _) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}
  {==}

def pcro.go(+s: String, m: Maybe<&2, FC.Ask>, ef: {FC.ffi(s) == LFT.pto.of(m) : String}, hw: LFX.pxe.Whole(s, m), ok: {LawsBase.wire_opens_err(FC.ffi(s)) == False{} : Bool}) -> Sigma<&1, &1, FC.Ask, a => {(s, FC.ffi(s)) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}>:
  match m:
    case None{}:
      +tf = Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FC.ffi(s)), False{}, Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), Wr.err("config: malformed request"), FC.ffi(s), Equal.sym(String, FC.ffi(s), Wr.err("config: malformed request"), ef)), ok)
      LLogicLogic.ppr.absurd(Sigma<&1, &1, FC.Ask, a => {(s, FC.ffi(s)) == (CS.cf_w_ask(a), CS.cf_w_reply(a)) : String & String}>, tf)
    case Some{+a}:
      (a, pcro.eq(s, a, hw, ef))

def Config.config_ffi_reads_only_requests(s, ok):
  pcro.go(s, CS.cf_read(s), LFT.pto.ffi(s), LFX.pxe.read_exact(s), ok)
