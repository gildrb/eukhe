# eukhe: the proof of LAW headless_exit_cause_is_first_failure
#
# PROOF: the exit's cause is the model's cause, and the model's cause is
# E1's first failure for every facts (hx.cause_eq).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless.bend as Sp
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_cause_is_first_failure(f):
  LAHeadlessExit.hx.cause_eq(f)
