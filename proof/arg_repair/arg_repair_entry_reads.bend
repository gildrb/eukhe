# eukhe: the proof of LAW arg_repair_entry_reads
#
# PROOF: each decoder stage answers Got only for the spec's spelling of its
# value, every length within the wire (rd.*, from dcw.nat, dcw.str and
# wire_bool_exact); a value is answered only for a request read whole
# (rd.top).

import Base
import ../../bend/ffi_arg_repair.bend as FAr
import ../../laws/arg_repair.bend as ArgRepair
import ./base/reads.bend as RD

def ArgRepair.arg_repair_entry_reads(s, ok):
  RD.rd.top(s, FAr.get_req(s), RD.rd.req(s), ok)
