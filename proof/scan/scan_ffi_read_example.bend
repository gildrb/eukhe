# eukhe: the proof of LAW scan_ffi_read_example

import Base
import ../../bend/scan.bend as Sc
import ../../bend/ffi_scan.bend as FSc
import ../../bend/wire.bend as Wr
import ../../laws/scan.bend as Scan

# PROOF of LAW scan_ffi_read_example: each anchor computes.

def Scan.scan_ffi_read_example():
  ({==}, {==})
