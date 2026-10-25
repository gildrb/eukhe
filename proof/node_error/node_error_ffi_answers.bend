# eukhe: the proof of LAW node_error_ffi_answers

import Base
import ../../bend/node_error.bend as Ne
import ../../bend/ffi_node_error.bend as FNe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/node_error.bend as NodeError
import ./base.bend as LANodeError
import ./node_error_table_exact.bend as PNodeErrorTableExact
import ./node_error_file_exact.bend as PNodeErrorFileExact
import ./node_error_message_exact.bend as PNodeErrorMessageExact

# PROOF of LAW node_error_ffi_answers: the request reads back with nothing left (ne.reads), the file error code and the message are the spec's (node_error_file_exact, node_error_message_exact) and the reply writer is the spec's speller (ne.put_file).

def NodeError.node_error_ffi_answers(q, fit):
  match q:
    case FNe.Req{+c, +f}:
      %Equal.sym(String, FNe.ffi(NodeError.spell_req(FNe.Req{c, f}, "")), FNe.ffi.done(FNe.Req{c, f}, Wr.end("")), LANodeError.ne.reads(FNe.Req{c, f}, "", fit)) : {_ == NodeError.answer_spec(FNe.Req{c, f}) : String}
      %NodeError.node_error_file_exact(c) : {FNe.put_file(Ne.file(c), Wr.put_str(Ne.message(c, f), "")) == NodeError.spell_file(_, Wr.put_str(NodeError.message_spec(c, f), "")) : String}
      %NodeError.node_error_message_exact(c, f) : {FNe.put_file(Ne.file(c), Wr.put_str(Ne.message(c, f), "")) == NodeError.spell_file(Ne.file(c), Wr.put_str(_, "")) : String}
      LANodeError.ne.put_file(Ne.file(c), Wr.put_str(Ne.message(c, f), ""))
