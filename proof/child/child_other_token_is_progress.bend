# eukhe: the proof of LAW child_other_token_is_progress
# The tokens differ (the premise), so the poll is news: the full clock.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/model.bend as Child

def Child.child_other_token_is_progress(cfg, y, l, n, e, x, other):
  %Equal.sym(Bool, Nat.is_eq(y, x), False{}, other) : {Ch.busy(Bool.not(_), cfg, Ch.W{Some{y}, l, n}, Some{x}, e) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}
  {==}
