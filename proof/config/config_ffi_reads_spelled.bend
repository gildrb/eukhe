# eukhe: the proof of LAW config_ffi_reads_spelled
# Every part of a spelled request reads back, the last leaving nothing
# (LFS.pfs.ask_rt).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../spec/config.bend as CS
import ./base/ffi_read.bend as LFR
import ./base/ffi_spell.bend as LFS
import ./base/ffi_reply.bend as LFP

def Config.config_ffi_reads_spelled(a, fits):
  %LFS.pfs.ask_rt(a, fits) : {CS.cf_r_whole(_) == Some{a} : Maybe<&2, FC.Ask>}
  {==}
