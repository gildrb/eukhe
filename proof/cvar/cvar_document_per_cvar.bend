# eukhe: the proof of LAW cvar_document_per_cvar
# The model walks the declarations with the ones before; the spec walks
# the first ids. Invariant (dpc.main): with ds = before ++ xs, the walk of
# xs gives the spec's sets of the first ids of xs not declared before
# (dpc.out). A declaration whose id is declared before adds nothing; else
# its id is not declared before, so the lookup in ds finds it
# (dpc.find_split) and its source is the declaration's; dropping its id
# from the later first ids is declaring it before them (dpc.out_drop).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/resolution.bend as Cvar
import ./base.bend as LA

# the ids of L not declared in before
def dpc.out.pick(hit: Bool, y: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      rest
    case False{}:
      y <> rest

def dpc.out(L: List<&2, Nat>, +before: List<&2, Cv.Decl>) -> List<&2, Nat>:
  match L:
    case Nil{}:
      Nil{}
    case +y <> r:
      dpc.out.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), y, dpc.out(r, before))

def dpc.out_nil(L: List<&2, Nat>) -> {dpc.out(L, Nil{}) == L : List<&2, Nat>}:
  match L:
    case Nil{}:
      {==}
    case +y <> +r:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, t => y <> t, dpc.out(r, Nil{}), r, dpc.out_nil(r))

def dpc.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dpc.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dpc.ap_one(hb: Bool, +d: Cv.Decl, +y: Nat, eh: {Nat.is_eq(Cv.Decl.id(d), y) == hb : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find.go([d], y, hb)) == Bool.or(False{}, Nat.is_eq(Cv.Decl.id(d), y)) : Bool}:
  match hb:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(d), y), True{}, eh) : {True{} == Bool.or(False{}, _) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(Cv.Decl.id(d), y), False{}, eh) : {False{} == Bool.or(False{}, _) : Bool}
      {==}

def dpc.ap_go(hb: Bool, +h: Cv.Decl, +t: List<&2, Cv.Decl>, +d: Cv.Decl, +y: Nat, ih: {Maybe.is_some(&2, Cv.Decl, Cv.find(List.append(&2, Cv.Decl, t, [d]), y)) == Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(t, y)), Nat.is_eq(Cv.Decl.id(d), y)) : Bool}) -> {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> List.append(&2, Cv.Decl, t, [d]), y, hb)) == Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> t, y, hb)), Nat.is_eq(Cv.Decl.id(d), y)) : Bool}:
  match hb:
    case True{}:
      {==}
    case False{}:
      ih

# x is declared in before ++ [d] when it is in before or is d's id
def dpc.ap_some(b: List<&2, Cv.Decl>, +d: Cv.Decl, +y: Nat) -> {Maybe.is_some(&2, Cv.Decl, Cv.find(List.append(&2, Cv.Decl, b, [d]), y)) == Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(b, y)), Nat.is_eq(Cv.Decl.id(d), y)) : Bool}:
  match b:
    case Nil{}:
      dpc.ap_one(Nat.is_eq(Cv.Decl.id(d), y), d, y, {==})
    case +h <> +t:
      dpc.ap_go(Nat.is_eq(Cv.Decl.id(h), y), h, t, d, y, dpc.ap_some(t, d, y))

def dpc.out_drop.at(hb: Bool, +i: Nat, +y: Nat, +r: List<&2, Nat>, +before: List<&2, Cv.Decl>, +d: Cv.Decl, ei: {Cv.Decl.id(d) == i : Nat}, eh: {Nat.is_eq(i, y) == hb : Bool}, ih: {dpc.out(Cvar.spec_drop_nat(r, i), before) == dpc.out(r, List.append(&2, Cv.Decl, before, [d])) : List<&2, Nat>}) -> {dpc.out(Cvar.spec_drop_nat.pick(hb, y, Cvar.spec_drop_nat(r, i)), before) == dpc.out.pick(Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), Nat.is_eq(i, y)), y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}:
  match hb:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(i, y), True{}, eh) : {dpc.out(Cvar.spec_drop_nat(r, i), before) == dpc.out.pick(Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), _), y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      %Equal.sym(Bool, Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), True{}), True{}, dpc.or_true(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)))) : {dpc.out(Cvar.spec_drop_nat(r, i), before) == dpc.out.pick(_, y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(i, y), False{}, eh) : {dpc.out(y <> Cvar.spec_drop_nat(r, i), before) == dpc.out.pick(Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), _), y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      %Equal.sym(Bool, Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), False{}), Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), dpc.or_false(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)))) : {dpc.out(y <> Cvar.spec_drop_nat(r, i), before) == dpc.out.pick(_, y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => dpc.out.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), y, z), dpc.out(Cvar.spec_drop_nat(r, i), before), dpc.out(r, List.append(&2, Cv.Decl, before, [d])), ih)

# dropping d's id from L is declaring d before L
def dpc.out_drop(L: List<&2, Nat>, +i: Nat, +before: List<&2, Cv.Decl>, +d: Cv.Decl, +ei: {Cv.Decl.id(d) == i : Nat}) -> {dpc.out(Cvar.spec_drop_nat(L, i), before) == dpc.out(L, List.append(&2, Cv.Decl, before, [d])) : List<&2, Nat>}:
  match L:
    case Nil{}:
      {==}
    case +y <> +r:
      %Equal.sym(Bool, Maybe.is_some(&2, Cv.Decl, Cv.find(List.append(&2, Cv.Decl, before, [d]), y)), Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), Nat.is_eq(Cv.Decl.id(d), y)), dpc.ap_some(before, d, y)) : {dpc.out(Cvar.spec_drop_nat(y <> r, i), before) == dpc.out.pick(_, y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      %Equal.sym(Nat, Cv.Decl.id(d), i, ei) : {dpc.out(Cvar.spec_drop_nat(y <> r, i), before) == dpc.out.pick(Bool.or(Maybe.is_some(&2, Cv.Decl, Cv.find(before, y)), Nat.is_eq(_, y)), y, dpc.out(r, List.append(&2, Cv.Decl, before, [d]))) : List<&2, Nat>}
      dpc.out_drop.at(Nat.is_eq(i, y), i, y, r, before, d, ei, {==}, dpc.out_drop(r, i, before, d, ei))

def dpc.split_go(hb: Bool, +h: Cv.Decl, +t: List<&2, Cv.Decl>, +d: Cv.Decl, +rest: List<&2, Cv.Decl>, +x: Nat, no: {Maybe.is_some(&2, Cv.Decl, Cv.find.go(h <> t, x, hb)) == False{} : Bool}, ih: {Maybe.is_some(&2, Cv.Decl, Cv.find(t, x)) == False{} : Bool} -> {Cv.find(List.append(&2, Cv.Decl, t, d <> rest), x) == Cv.find(d <> rest, x) : Maybe<&2, Cv.Decl>}) -> {Cv.find.go(h <> List.append(&2, Cv.Decl, t, d <> rest), x, hb) == Cv.find(d <> rest, x) : Maybe<&2, Cv.Decl>}:
  match hb:
    case True{}:
      LA.pv.absurdF({Cv.find.go(h <> List.append(&2, Cv.Decl, t, d <> rest), x, True{}) == Cv.find(d <> rest, x) : Maybe<&2, Cv.Decl>}, Equal.sym(Bool, True{}, False{}, no))
    case False{}:
      ih(no)

# a lookup past declarations that do not have x
def dpc.find_split(before: List<&2, Cv.Decl>, +d: Cv.Decl, +rest: List<&2, Cv.Decl>, +x: Nat, no: {Maybe.is_some(&2, Cv.Decl, Cv.find(before, x)) == False{} : Bool}) -> {Cv.find(List.append(&2, Cv.Decl, before, d <> rest), x) == Cv.find(d <> rest, x) : Maybe<&2, Cv.Decl>}:
  match before:
    case Nil{}:
      {==}
    case +h <> +t:
      dpc.split_go(Nat.is_eq(Cv.Decl.id(h), x), h, t, d, rest, x, no, e => dpc.find_split(t, d, rest, x, e))

def dpc.assoc(b: List<&2, Cv.Decl>, +d: Cv.Decl, +rest: List<&2, Cv.Decl>) -> {List.append(&2, Cv.Decl, b, d <> rest) == List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, b, [d]), rest) : List<&2, Cv.Decl>}:
  match b:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Cv.Decl>, List<&2, Cv.Decl>, z => h <> z, List.append(&2, Cv.Decl, t, d <> rest), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, t, [d]), rest), dpc.assoc(t, d, rest))

def dpc.one(+x: Nat, m: Maybe<&2, Cv.Val>, +rest: List<&2, Cv.Bind>) -> {Cv.doc.one(x, m, rest) == Cvar.spec_doc_one(x, m, rest) : List<&2, Cv.Bind>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# the source of d's cvar is the spec's
def dpc.src(d: Cv.Decl, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>) -> {Cv.doc.pick(Cv.Decl.local(d), merged, global) == Cvar.spec_doc_src(Some{d}, merged, global) : List<&2, Cv.Bind>}:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      match c:
        case Cv.Global{}:
          {==}
        case Cv.Local{}:
          {==}

def dpc.hit(d: Cv.Decl, +rest: List<&2, Cv.Decl>, +i: Nat, ei: {Cv.Decl.id(d) == i : Nat}) -> {Cv.find(d <> rest, i) == Some{d} : Maybe<&2, Cv.Decl>}:
  match d:
    case Cv.Decl{+j, t, c, p, r, v}:
      %ei : {Cv.find.go(Cv.Decl{j, t, c, p, r, v} <> rest, _, Nat.is_eq(j, _)) == Some{Cv.Decl{j, t, c, p, r, v}} : Maybe<&2, Cv.Decl>}
      %LA.cvar.pv.eq_refl(j) : {Cv.find.go(Cv.Decl{j, t, c, p, r, v} <> rest, j, _) == Some{Cv.Decl{j, t, c, p, r, v}} : Maybe<&2, Cv.Decl>}
      {==}

def dpc.id(d: Cv.Decl) -> {Cv.Decl.id(d) == Cvar.spec_id(d) : Nat}:
  match d:
    case Cv.Decl{i, t, c, p, r, v}:
      {==}

def dpc.step(hb: Bool, +d: Cv.Decl, +i: Nat, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, +rest: List<&2, Cv.Decl>, +before: List<&2, Cv.Decl>, +q: List<&2, Nat>,
  ei: {Cv.Decl.id(d) == i : Nat}, eh: {Maybe.is_some(&2, Cv.Decl, Cv.find(before, i)) == hb : Bool}, e: {ds == List.append(&2, Cv.Decl, before, d <> rest) : List<&2, Cv.Decl>},
  ih: {Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d])) == Cvar.spec_doc_of(ds, merged, global, q) : List<&2, Cv.Bind>})
  -> {Cv.doc.first(hb, i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d]))) == Cvar.spec_doc_of(ds, merged, global, dpc.out.pick(hb, i, q)) : List<&2, Cv.Bind>}:
  match hb:
    case True{}:
      ih
    case False{}:
      +ef = Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(ds, i), Cv.find(List.append(&2, Cv.Decl, before, d <> rest), i), Cv.find(d <> rest, i),
        Equal.cong(List<&2, Cv.Decl>, Maybe<&2, Cv.Decl>, z => Cv.find(z, i), ds, List.append(&2, Cv.Decl, before, d <> rest), e),
        dpc.find_split(before, d, rest, i, eh))
      +eg = Equal.trans(Maybe<&2, Cv.Decl>, Cv.find(ds, i), Cv.find(d <> rest, i), Some{d}, ef, dpc.hit(d, rest, i, ei))
      %Equal.sym(Maybe<&2, Cv.Decl>, Cv.find(ds, i), Some{d}, eg) : {Cv.doc.one(i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d]))) == Cvar.spec_doc_one(i, Cv.layer(Cvar.spec_doc_src(_, merged, global), ds, Cv.Config{}, i, None{}), Cvar.spec_doc_of(ds, merged, global, q)) : List<&2, Cv.Bind>}
      %dpc.src(d, merged, global) : {Cv.doc.one(i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d]))) == Cvar.spec_doc_one(i, Cv.layer(_, ds, Cv.Config{}, i, None{}), Cvar.spec_doc_of(ds, merged, global, q)) : List<&2, Cv.Bind>}
      %Equal.sym(List<&2, Cv.Bind>, Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d])), Cvar.spec_doc_of(ds, merged, global, q), ih) : {Cv.doc.one(i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), _) == Cvar.spec_doc_one(i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), Cvar.spec_doc_of(ds, merged, global, q)) : List<&2, Cv.Bind>}
      dpc.one(i, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, i, None{}), Cvar.spec_doc_of(ds, merged, global, q))

def dpc.main(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, +before: List<&2, Cv.Decl>, +e: {ds == List.append(&2, Cv.Decl, before, xs) : List<&2, Cv.Decl>}) -> {Cv.document.go(xs, ds, merged, global, before) == Cvar.spec_doc_of(ds, merged, global, dpc.out(Cvar.spec_first_ids(xs), before)) : List<&2, Cv.Bind>}:
  match xs:
    case Nil{}:
      {==}
    case +d <> +rest:
      +i = Cvar.spec_id(d)
      +ei = dpc.id(d)
      +q = dpc.out(Cvar.spec_first_ids(rest), List.append(&2, Cv.Decl, before, [d]))
      +e2 = Equal.trans(List<&2, Cv.Decl>, ds, List.append(&2, Cv.Decl, before, d <> rest), List.append(&2, Cv.Decl, List.append(&2, Cv.Decl, before, [d]), rest), e, dpc.assoc(before, d, rest))
      %Equal.sym(List<&2, Nat>, dpc.out(Cvar.spec_drop_nat(Cvar.spec_first_ids(rest), i), before), q, dpc.out_drop(Cvar.spec_first_ids(rest), i, before, d, ei)) : {Cv.document.go(d <> rest, ds, merged, global, before) == Cvar.spec_doc_of(ds, merged, global, dpc.out.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(before, i)), i, _)) : List<&2, Cv.Bind>}
      %Equal.sym(Nat, Cv.Decl.id(d), i, ei) : {Cv.doc.first(Maybe.is_some(&2, Cv.Decl, Cv.find(before, _)), _, Cv.layer(Cv.doc.pick(Cv.Decl.local(d), merged, global), ds, Cv.Config{}, _, None{}), Cv.document.go(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d]))) == Cvar.spec_doc_of(ds, merged, global, dpc.out.pick(Maybe.is_some(&2, Cv.Decl, Cv.find(before, i)), i, q)) : List<&2, Cv.Bind>}
      dpc.step(Maybe.is_some(&2, Cv.Decl, Cv.find(before, i)), d, i, ds, merged, global, rest, before, q, ei, {==}, e, dpc.main(rest, ds, merged, global, List.append(&2, Cv.Decl, before, [d]), e2))

def Cvar.cvar_document_per_cvar(ds, merged, global):
  %dpc.out_nil(Cvar.spec_first_ids(ds)) : {Cv.document.go(ds, ds, merged, global, Nil{}) == Cvar.spec_doc_of(ds, merged, global, _) : List<&2, Cv.Bind>}
  dpc.main(ds, ds, merged, global, Nil{}, {==})
