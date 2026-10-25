# eukhe: the proof of LAW optchat_entry_answers
# The entry reads a spelled request back whole (LAF.oe.spelled) and runs
# it as the laws' model asks (LAF.oe.serve): LAF.oe.answers.

import Base
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF

def Optchat.optchat_entry_answers(cfg, s, q, fits):
  LAF.oe.answers(cfg, s, q, fits)
