# eukhe: the proof of LAW command_ffi_req_exact
#
# PROOF of LAW command_ffi_req_exact: every request the reader accepts is
# spelled, and fits (ci_req_all of command_ffi_reads_only_requests, which
# inverts each stage of the reader with the wire exactness laws).

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command/entry.bend as Command
import ./command_ffi_reads_only_requests.bend as PCommandFfiReadsOnlyRequests
import ./base/reply.bend as LACommandReply

def crx_at(+s: String, -d: Wr.Dec<FCmd.Req>, er: {FCmd.get_req(s) == d : Wr.Dec<FCmd.Req>}) -> PCommandFfiReadsOnlyRequests.ci_req(s, d):
  %er : PCommandFfiReadsOnlyRequests.ci_req(s, _)
  PCommandFfiReadsOnlyRequests.ci_req_all(s)

def Command.command_ffi_req_exact(s, r, rest, h):
  LACommandReply.cr_pair(s, Command.cmd_spell_req(r, rest), Command.cmd_req_fits(r), crx_at(s, Wr.Got{r, rest}, h))
