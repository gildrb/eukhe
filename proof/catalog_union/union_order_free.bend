# eukhe: the proof of LAW union_order_free

import Base
import ../../bend/catalog_union.bend as CU
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pcu.order_free(+k: Nat, +xs: List<&2, CU.Ent>, +xs2: List<&2, CU.Ent>, +ys: List<&2, CU.Ent>, +ys2: List<&2, CU.Ent>, sx: {CU.find(xs, k) == CU.find(xs2, k) : Maybe<&2, CU.Ent>}, sy: {CU.find(ys, k) == CU.find(ys2, k) : Maybe<&2, CU.Ent>}) -> {CU.find(CU.read(CU.Cat{CU.Bundled{}, xs}, CU.Cat{CU.Compiled{}, ys}), k) == CU.find(CU.read(CU.Cat{CU.Compiled{}, ys2}, CU.Cat{CU.Bundled{}, xs2}), k) : Maybe<&2, CU.Ent>}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(xs, ys), k), LA.pcu.pick(CU.find(xs, k), CU.find(ys, k)), LA.pcu.find_union(xs, ys, k)) : {_ == CU.find(CU.union(xs2, ys2), k) : Maybe<&2, CU.Ent>}
  Equal.sym(Maybe<&2, CU.Ent>, CU.find(CU.union(xs2, ys2), k), LA.pcu.pick(CU.find(xs, k), CU.find(ys, k)), LA.pcu.at(xs2, ys2, k, CU.find(xs, k), CU.find(ys, k), Equal.sym(Maybe<&2, CU.Ent>, CU.find(xs, k), CU.find(xs2, k), sx), Equal.sym(Maybe<&2, CU.Ent>, CU.find(ys, k), CU.find(ys2, k), sy)))

def Laws.union_order_free(k, xs, xs2, ys, ys2, sx, sy):
  pcu.order_free(k, xs, xs2, ys, ys2, sx, sy)
