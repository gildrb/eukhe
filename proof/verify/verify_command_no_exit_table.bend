# eukhe: the proof of LAW verify_command_no_exit_table
#
# PROOF: the four rows; both sides compute.

import Base
import ../../bend/verify.bend as V
import ../../laws/verify.bend as Verify

def Verify.verify_command_no_exit_table(e):
  ({==}, ({==}, ({==}, {==})))
