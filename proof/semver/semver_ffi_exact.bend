# eukhe: the proof of LAW semver_ffi_exact

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_exact: a reply that is not the error form comes
# from a request read whole (each decoder layer that answers Got gives the
# prefix of the encoding: wire_nat_exact, wire_str_exact, sv_tags_ex) with
# nothing left over: that input is the spelled request (sv_ex_top).

def Semver.semver_ffi_exact(s, ok):
  LASemver.sv_ex_top(s, Wr.get_nat(s), {==}, ok)
