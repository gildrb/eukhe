# eukhe: the proof of LAW run_reply_is_the_rust_rule

import Base
import ../../laws/run.bend as Run
import ./base.bend as LA

# (H4.9) The decisions Rust calls are the model's

def Run.run_reply_is_the_rust_rule(l, t, reply):
  LA.rk.run_reply_is_the_rust_rule(l, t, reply)
