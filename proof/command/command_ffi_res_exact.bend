# eukhe: the proof of LAW command_ffi_res_exact
#
# PROOF of LAW command_ffi_res_exact: the resolve reply reader reads a tag,
# then by the tag a path and a text or word; each stage is a wire value its
# exactness law inverts (wire_nat_exact, wire_strs_exact, wire_str_exact),
# threading the equation of the input so far, so an accepted reply is the
# grammar's spelling of what it read, then the rest.

import Base
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_strs_exact.bend as PWireStrsExact

# what a resolve reply reader answer says about its input s
def cx_res(s: String, d: Wr.Dec<FCmd.ResW>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Command.cmd_spell_resw(x, r) : String}
    case Wr.Bad{}:
      Unit

# ---- tag 0: runs (path, text) ----

def cx_runs_args(-s0: String, +p: List<&2, String>, +s2: String, pre: {s0 == Wr.put_nat(0n, LawsBase.wire_spell_strs(p, s2)) : String},
  d: Wr.Dec<String>, ed: {Wr.get_str(s2) == d : Wr.Dec<String>}) -> cx_res(s0, FCmd.get_res.runs.args(p, d)):
  match d:
    case Wr.Got{+a, +s3}:
      Equal.trans(String, s0, Wr.put_nat(0n, LawsBase.wire_spell_strs(p, s2)), Wr.put_nat(0n, LawsBase.wire_spell_strs(p, Wr.put_str(a, s3))), pre,
        Equal.cong(String, String, z => Wr.put_nat(0n, LawsBase.wire_spell_strs(p, z)), s2, Wr.put_str(a, s3), Wire.wire_str_exact(s2, a, s3, ed)))
    case Wr.Bad{}:
      Unit{}

def cx_runs(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(0n, s1) : String},
  d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> cx_res(s0, FCmd.get_res.runs(d)):
  match d:
    case Wr.Got{+p, +s2}:
      cx_runs_args(s0, p, s2,
        Equal.trans(String, s0, Wr.put_nat(0n, s1), Wr.put_nat(0n, LawsBase.wire_spell_strs(p, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, LawsBase.wire_spell_strs(p, s2), Wire.wire_strs_exact(s1, p, s2, ed))),
        Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

# ---- tag 1: opens (path) ----

def cx_opens(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String},
  d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> cx_res(s0, FCmd.get_res.opens(d)):
  match d:
    case Wr.Got{+p, +s2}:
      Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, LawsBase.wire_spell_strs(p, s2)), pre,
        Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, LawsBase.wire_spell_strs(p, s2), Wire.wire_strs_exact(s1, p, s2, ed)))
    case Wr.Bad{}:
      Unit{}

# ---- tag 2: unknown (path, word) ----

def cx_unknown_word(-s0: String, +p: List<&2, String>, +s2: String, pre: {s0 == Wr.put_nat(2n, LawsBase.wire_spell_strs(p, s2)) : String},
  d: Wr.Dec<String>, ed: {Wr.get_str(s2) == d : Wr.Dec<String>}) -> cx_res(s0, FCmd.get_res.unknown.word(p, d)):
  match d:
    case Wr.Got{+w, +s3}:
      Equal.trans(String, s0, Wr.put_nat(2n, LawsBase.wire_spell_strs(p, s2)), Wr.put_nat(2n, LawsBase.wire_spell_strs(p, Wr.put_str(w, s3))), pre,
        Equal.cong(String, String, z => Wr.put_nat(2n, LawsBase.wire_spell_strs(p, z)), s2, Wr.put_str(w, s3), Wire.wire_str_exact(s2, w, s3, ed)))
    case Wr.Bad{}:
      Unit{}

def cx_unknown(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(2n, s1) : String},
  d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> cx_res(s0, FCmd.get_res.unknown(d)):
  match d:
    case Wr.Got{+p, +s2}:
      cx_unknown_word(s0, p, s2,
        Equal.trans(String, s0, Wr.put_nat(2n, s1), Wr.put_nat(2n, LawsBase.wire_spell_strs(p, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, LawsBase.wire_spell_strs(p, s2), Wire.wire_strs_exact(s1, p, s2, ed))),
        Wr.get_str(s2), {==})
    case Wr.Bad{}:
      Unit{}

# ---- the tag ----

def cx_tag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> cx_res(s0, FCmd.get_res.tag(t, s1)):
  match t:
    case 0n:
      cx_runs(s0, s1, ex, FCmd.get_strs(s1), {==})
    case 1n:
      cx_opens(s0, s1, ex, FCmd.get_strs(s1), {==})
    case 2n:
      cx_unknown(s0, s1, ex, FCmd.get_strs(s1), {==})
    case 3n:
      ex
    case 4n+y:
      Unit{}

def cx_go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cx_res(s, FCmd.get_res.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      cx_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# every resolve reply the reader accepts is its spelling
def cx_all(+s: String) -> cx_res(s, FCmd.get_res(s)):
  cx_go(s, Wr.get_nat(s), {==})

def cx_at(+s: String, -d: Wr.Dec<FCmd.ResW>, er: {FCmd.get_res(s) == d : Wr.Dec<FCmd.ResW>}) -> cx_res(s, d):
  %er : cx_res(s, _)
  cx_all(s)

def Command.command_ffi_res_exact(s, x, rest, h):
  cx_at(s, Wr.Got{x, rest}, h)
