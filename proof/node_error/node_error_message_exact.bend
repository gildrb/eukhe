# eukhe: the proof of LAW node_error_message_exact

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

# PROOF of LAW node_error_message_exact: the name and description are the row's (node_error_table_exact); per form both sides spell the same text.

def ne.msg(f: Ne.Form, +c: Ne.Code) -> {Ne.message(c, f) == NodeError.message_spec(c, f) : String}:
  match f:
    case Ne.Fd{s}:
      %NodeError.node_error_table_exact(c) : {Ne.message(c, Ne.Fd{s}) == NodeError.message_spec.of(_, Ne.Fd{s}) : String}
      {==}
    case Ne.Path{s, p}:
      %NodeError.node_error_table_exact(c) : {Ne.message(c, Ne.Path{s, p}) == NodeError.message_spec.of(_, Ne.Path{s, p}) : String}
      {==}
    case Ne.Dest{s, p, t}:
      %NodeError.node_error_table_exact(c) : {Ne.message(c, Ne.Dest{s, p, t}) == NodeError.message_spec.of(_, Ne.Dest{s, p, t}) : String}
      {==}
    case Ne.Spawn{prog}:
      %NodeError.node_error_table_exact(c) : {Ne.message(c, Ne.Spawn{prog}) == NodeError.message_spec.of(_, Ne.Spawn{prog}) : String}
      {==}

def NodeError.node_error_message_exact(c, f):
  ne.msg(f, c)
