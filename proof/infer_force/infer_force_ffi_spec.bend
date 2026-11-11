# eukhe: the proof of LAW infer_force_ffi_spec
# The laws' reader reads every input as the entry does (the projection
# ifm.go of infer_force_ffi_malformed_exact); a whole request gets the
# model's answer, which is the spec's (infer_force_flag_exact,
# infer_force_after_exact); anything else gets the error form.

import Base
import ../../bend/infer_force.bend as M
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/infer_force.bend as InferForce
import ./infer_force_ffi_malformed_exact.bend as PIfm
import ./infer_force_ffi_after.bend as PIfa
import ./infer_force_flag_exact.bend as PIfFlag
import ./infer_force_after_exact.bend as PIfAfter

# the entry's answer to a request is the spec's reply to it
def iffs.answer(q: FF.Req) -> {FF.answer(q) == InferForce.reply_spec(PIfm.ifm.ask(q)) : String}:
  match q:
    case FF.QFlag{+i, +sup, +free}:
      %InferForce.infer_force_flag_exact(i, sup, free) : {Wr.put_bool(M.flag(i, sup, free), "") == Wr.put_bool(_, "") : String}
      {==}
    case FF.QAfter{+i, +r, +c}:
      %InferForce.infer_force_after_exact(i, r, c) : {FF.put_next(M.after(i, r, c)) == InferForce.spell_next(_) : String}
      PIfa.ifa.next(M.after(i, r, c))

def iffs.end(b: Bool, q: FF.Req) -> {FF.run.end(b, q) == InferForce.entry_spec.of(InferForce.read_ask.end(b, PIfm.ifm.ask(q))) : String}:
  match b:
    case True{}:
      iffs.answer(q)
    case False{}:
      {==}

def iffs.whole(d: Wr.Dec<FF.Req>) -> {FF.run(d) == InferForce.entry_spec.of(InferForce.read_ask.whole(PIfm.ifm.dec(d))) : String}:
  match d:
    case Wr.Got{q, s}:
      iffs.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def InferForce.infer_force_ffi_spec(s):
  %Equal.sym(Wr.Dec<InferForce.Ask>, InferForce.read_ask.go(Wr.get_nat(s)), PIfm.ifm.dec(FF.get_req.go(Wr.get_nat(s))), PIfm.ifm.go(Wr.get_nat(s))) : {FF.ffi(s) == InferForce.entry_spec.of(InferForce.read_ask.whole(_)) : String}
  iffs.whole(FF.get_req.go(Wr.get_nat(s)))
