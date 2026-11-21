# eukhe: the proof of LAW command_ffi_out_exact
#
# PROOF of LAW command_ffi_out_exact: the key reply reader reads a line,
# then open, then submit; each is a wire value its exactness law inverts
# (wire_str_exact, wire_bool_exact), threading the equation of the input so
# far, and the decoded line fits (wire_str_decoded_fits), so an accepted
# reply is the grammar's spelling of what it read, then the rest, and fits.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ./base/reply.bend as LACommandReply

# what a key reply reader answer says about its input s
def cox_out(s: String, d: Wr.Dec<FCmd.OutW>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == Command.cmd_spell_outw(x, r) : String} & {Command.cmd_out_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cox_submit(-s0: String, +l: String, +a: Bool, +s2: String, pre: {s0 == Wr.put_str(l, Wr.put_bool(a, s2)) : String},
  fl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> cox_out(s0, FCmd.get_out.submit(l, a, d)):
  match d:
    case Wr.Got{+b, +s3}:
      (Equal.trans(String, s0, Wr.put_str(l, Wr.put_bool(a, s2)), Wr.put_str(l, Wr.put_bool(a, Wr.put_bool(b, s3))), pre,
          Equal.cong(String, String, z => Wr.put_str(l, Wr.put_bool(a, z)), s2, Wr.put_bool(b, s3), Wire.wire_bool_exact(s2, b, s3, ed))),
        fl)
    case Wr.Bad{}:
      Unit{}

def cox_open(-s0: String, +l: String, +s1: String, pre: {s0 == Wr.put_str(l, s1) : String},
  fl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> cox_out(s0, FCmd.get_out.open(l, d)):
  match d:
    case Wr.Got{+a, +s2}:
      cox_submit(s0, l, a, s2,
        Equal.trans(String, s0, Wr.put_str(l, s1), Wr.put_str(l, Wr.put_bool(a, s2)), pre,
          Equal.cong(String, String, z => Wr.put_str(l, z), s1, Wr.put_bool(a, s2), Wire.wire_bool_exact(s1, a, s2, ed))),
        fl, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def cox_line(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> cox_out(s, FCmd.get_out.line(d)):
  match d:
    case Wr.Got{+l, +s1}:
      +e2 = ed
      cox_open(s, l, s1, Wire.wire_str_exact(s, l, s1, e2), Wire.wire_str_decoded_fits(s, l, s1, e2), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# every key reply the reader accepts is its spelling, and fits
def cox_all(+s: String) -> cox_out(s, FCmd.get_out(s)):
  cox_line(s, Wr.get_str(s), {==})

def cox_at(+s: String, -d: Wr.Dec<FCmd.OutW>, er: {FCmd.get_out(s) == d : Wr.Dec<FCmd.OutW>}) -> cox_out(s, d):
  %er : cox_out(s, _)
  cox_all(s)

def Command.command_ffi_out_exact(s, x, rest, h):
  LACommandReply.cr_pair(s, Command.cmd_spell_outw(x, rest), Command.cmd_out_fits(x), cox_at(s, Wr.Got{x, rest}, h))
