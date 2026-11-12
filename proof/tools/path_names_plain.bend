# eukhe: the proof of LAW path_names_plain
#
# PROOF: by induction on the names, from any names at: each name goes
# one below, so the walk reverses the names onto at.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

def pnp.walk(ns: List<&2, Nat>, at: List<&2, Nat>) -> {Tl.walk(Tools.tools_name_path(ns), at) == Some{List.reverse.go(&2, Nat, ns, at)} : Maybe<&2, List<&2, Nat>>}:
  match ns:
    case Nil{}:
      {==}
    case n <> rest:
      pnp.walk(rest, n <> at)

def Tools.path_names_plain(ns):
  pnp.walk(ns, Nil{})
