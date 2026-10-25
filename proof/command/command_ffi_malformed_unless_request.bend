# eukhe: the proof of LAW command_ffi_malformed_unless_request
#
# PROOF of LAW command_ffi_malformed_unless_request: the decoder reads
# only spelled requests that fit, the rest after them untouched
# (ci_req_all of command_ffi_reads_only_requests); when it reads none the
# entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ./command_ffi_reads_only_requests.bend as PCommandFfiReadsOnlyRequests

def cmu_goal(+s: String) -> Type:
  &r: FCmd.Req -> &rest: String -> {(s, Command.cmd_req_fits(r)) == (Command.cmd_spell_req(r, rest), True{}) : String & Bool}

def cmu_eq(+s: String, +r: FCmd.Req, +rest: String, e1: {s == Command.cmd_spell_req(r, rest) : String}, e2: {Command.cmd_req_fits(r) == True{} : Bool}) -> {(s, Command.cmd_req_fits(r)) == (Command.cmd_spell_req(r, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Command.cmd_spell_req(r, rest), e1) : {(_, Command.cmd_req_fits(r)) == (Command.cmd_spell_req(r, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Command.cmd_req_fits(r), True{}, e2) : {(Command.cmd_spell_req(r, rest), _) == (Command.cmd_spell_req(r, rest), True{}) : String & Bool}
  {==}

def cmu_main(+s: String, d: Wr.Dec<FCmd.Req>, inv: PCommandFfiReadsOnlyRequests.ci_req(s, d), other: {String.eq(FCmd.ffi.go(d), Wr.err("command: malformed request")) == False{} : Bool}) -> cmu_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      (r, (rest, cmu_eq(s, r, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(cmu_goal(s), other)

def Command.command_ffi_malformed_unless_request(s, other):
  cmu_main(s, FCmd.get_req(s), PCommandFfiReadsOnlyRequests.ci_req_all(s), other)
