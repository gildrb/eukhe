# eukhe: the proof of LAW node_error_ffi_example

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

# PROOF of LAW node_error_ffi_example: each anchor computes.

def NodeError.node_error_ffi_example():
  ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))
