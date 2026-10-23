# eukhe: the proof of LAW list_import_lists_storage

import Base
import ../../bend/staging.bend as Sg
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pg.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the law list_import_lists_storage
def pg.import_lists(+es: List<&2, Sg.Ent>, +s: Nat) -> {Sg.mem(s, Sg.durables(Sg.imported(s, es))) == True{} : Bool}:
  +d = {[Sg.Dir{s, True{}, False{}, True{}}] : List<&2, Sg.Ent>}
  %LA.pg.dur_app(es, d) : {Sg.mem(s, _) == True{} : Bool}
  %LA.pg.mem_app(s, Sg.durables(es), [s]) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, LA.pg.eq_refl(s)) : {Bool.or(Sg.mem(s, Sg.durables(es)), Bool.or(_, False{})) == True{} : Bool}
  pg.or_t(Sg.mem(s, Sg.durables(es)))

def Laws.list_import_lists_storage(es, s):
  pg.import_lists(es, s)
