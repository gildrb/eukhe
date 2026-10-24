# eukhe: the proof of LAW shell_ffi_exact
# The entry reads every input as the laws' reader does (LASh.sh.req) and answers what the laws spell (LASh.sh.run).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_ffi_exact(s):
  LASh.sh.exact(s)
