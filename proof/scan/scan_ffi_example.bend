# eukhe: the proof of LAW scan_ffi_example

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/logic/logic.bend as LLogicLogic
import ../../laws/scan.bend as Scan
import ./base.bend as LAScan

# PROOF of LAW scan_ffi_example: each anchor computes.

def Scan.scan_ffi_example():
  ({==}, ({==}, ({==}, {==})))
