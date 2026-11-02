# eukhe: the proof of LAW run_entry_exact
#
# PROOF: the entry's decoder is the laws' reader stage by stage
# (rex.ask); on a request read whole its answer is the rules' decision
# (run_*_is_the_rust_rule, rec_recover_is_the_rust_rule), spelled as the
# laws spell it (rex.answer); the error texts are the same.

import Base
import ../../laws/run/entry.bend as RunEntry
import ./base/entry.bend as LARunEntry

def RunEntry.run_entry_exact(s):
  LARunEntry.rex.exact(s)
