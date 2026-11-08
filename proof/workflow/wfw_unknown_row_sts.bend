# eukhe: the proof of LAW wfw_unknown_row_sts
#
# PROOF: the kind, the spelled prior (sp.prior, its round trip), the key,
# the count and the first row's key read back; the row's status tag reads
# as itself or Bad (ws_nat_read), and a tag of 6 or more is no status:
# the row is Bad, so are the rows (whatever the count), and the entry
# answers the malformed error form.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/workflow.bend as Workflow
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA
import ./wfw_answers_spelled/spell.bend as SP

def wurs.bad(b: Bool, c: Nat, -n: Nat, -rest: String, -m: Maybe<&2, W.Sts>, -k: Nat, -key: Nat) -> {FW.ffi.go(FW.get_req.rows(m, k, Wr.get_list.go(~W.Row, ~FW.get_row, c, FW.get_row.sts(key, FW.get_sts.go(LAWireSpell.ws_nat_answer(b, 6n+n, rest)))))) == Wr.err("workflow: malformed request") : String}:
  match b c:
    case True{} 0n:
      {==}
    case True{} 1n+x:
      {==}
    case False{} 0n:
      {==}
    case False{} 1n+x:
      {==}

def Workflow.wfw_unknown_row_sts(m, k, c, key, fits, n, rest):
  +E = Wr.err("workflow: malformed request")
  +y4 = Wr.put_nat(6n+n, rest)
  +y3 = Wr.put_nat(key, y4)
  +y2 = Wr.put_nat(1n+c, y3)
  +y1 = Wr.put_nat(k, y2)
  +h = fits
  +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(1n+c), LawsBase.wire_fits(key)), h)
  %LA.pww.nat(0n, Workflow.wfw_spell_prior(m, y1), {==}) : {FW.ffi.go(FW.get_req.go(_)) == E : String}
  %Equal.sym(String, Workflow.wfw_spell_prior(m, y1), FW.put_prior(m, y1), SP.sp.prior(m, y1)) : {FW.ffi.go(FW.get_req.admit(FW.get_prior(_))) == E : String}
  %LA.pww.prior(m, y1) : {FW.ffi.go(FW.get_req.admit(_)) == E : String}
  %LA.pww.nat(k, y2, LLogicBool.wr_and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(1n+c), LawsBase.wire_fits(key)), h)) : {FW.ffi.go(FW.get_req.key(m, _)) == E : String}
  %LA.pww.nat(1n+c, y3, LLogicBool.wr_and_l(LawsBase.wire_fits(1n+c), LawsBase.wire_fits(key), h2)) : {FW.ffi.go(FW.get_req.rows(m, k, Wr.get_list.start(~W.Row, ~FW.get_row, _))) == E : String}
  %LA.pww.nat(key, y4, LLogicBool.wr_and_r(LawsBase.wire_fits(1n+c), LawsBase.wire_fits(key), h2)) : {FW.ffi.go(FW.get_req.rows(m, k, Wr.get_list.go(~W.Row, ~FW.get_row, c, FW.get_row.go(_)))) == E : String}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(6n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(6n+n), 6n+n, rest), LAWireSpell.ws_nat_read(6n+n, rest)) : {FW.ffi.go(FW.get_req.rows(m, k, Wr.get_list.go(~W.Row, ~FW.get_row, c, FW.get_row.sts(key, FW.get_sts.go(_))))) == E : String}
  wurs.bad(LawsBase.wire_fits(6n+n), c, n, rest, m, k, key)
