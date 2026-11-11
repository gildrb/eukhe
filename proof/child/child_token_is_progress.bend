# eukhe: the proof of LAW child_token_is_progress
# A first token computes to the full clock; a poll with no token is no
# news, so it spends the elapsed ms off the clock (LA.pc.spends).

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/model.bend as Child
import ./base.bend as LA

def Child.child_token_is_progress(cfg, tok, l, n, e, x):
  ({==}, LA.pc.spends(l, e, tok, Ch.Cfg.fails(cfg)))
