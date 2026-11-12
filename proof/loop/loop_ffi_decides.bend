# eukhe: the proof of LAW loop_ffi_decides
#
# PROOF: the decoder reads the spelled request whole (le.spelled, from
# le.r_req), so the entry runs the model on it, and its encoders spell the
# model's answer as the spec does (le.run).

import Base
import ../../bend/ffi_loop.bend as FLp
import ../../laws/loop/entry.bend as LoopEntry
import ./base/entry.bend as LALoopEntry

def LoopEntry.loop_ffi_decides(r, h):
  Equal.trans(String, FLp.ffi(LoopEntry.lp_spell_req(r, "")), FLp.ffi.run(r), LoopEntry.lp_spell_reply(r), LALoopEntry.le.spelled(r, "", h), LALoopEntry.le.run(r))
