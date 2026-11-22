# eukhe: the proof of LAW shell_ffi_req_exact
#
# PROOF: the decoder stages of shell_ffi_reads_only_requests (shx.tag)
# show that whatever get_req decodes is the spelling of a request that
# fits, then its rest; h names what it decoded.

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./shell_ffi_reads_only_requests.bend as PShx

def Shell.shell_ffi_req_exact(s, q, rest, h):
  %h : PShx.shx.Q(s, _)
  PShx.shx.tag(s, Wr.get_nat(s), {==})
