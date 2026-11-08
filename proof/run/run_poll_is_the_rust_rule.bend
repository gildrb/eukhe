# eukhe: the proof of LAW run_poll_is_the_rust_rule
#
# PROOF: case by case on retryable (LARunEntry.rex.poll).

import Base
import ../../laws/run/spec.bend as RunSpec
import ./base/entry.bend as LARunEntry

def RunSpec.run_poll_is_the_rust_rule(retryable, failures, retries):
  LARunEntry.rex.poll(retryable, failures, retries)
