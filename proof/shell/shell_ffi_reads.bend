# eukhe: the proof of LAW shell_ffi_reads
# The entry's decoder reads back the request Rust writes, the rest untouched (LASh.sh.rt).

import Base
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_ffi_reads(q, rest, fits):
  LASh.sh.rt(q, rest, fits)
