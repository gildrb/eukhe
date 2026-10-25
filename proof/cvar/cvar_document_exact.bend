# eukhe: the proof of LAW cvar_document_exact
# Declaration by declaration: a declaration is skipped exactly when an
# earlier one has its id (LR.re.mem, LR.re.ids_snoc), the document its
# scope picks is the spec's, and the model's layer over it is the spec's
# last set that counts (LR.re.layer).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def dc.one(+x: Nat, m: Maybe<&2, Cv.Val>, +r: List<&2, Cv.Bind>) -> {Cv.doc.one(x, m, r) == Cvar.spec_doc.one(x, m, r) : List<&2, Cv.Bind>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def dc.first(b: Bool, +x: Nat, m: Maybe<&2, Cv.Val>, +r: List<&2, Cv.Bind>) -> {Cv.doc.first(b, x, m, r) == Cvar.spec_doc.first(b, x, m, r) : List<&2, Cv.Bind>}:
  match b:
    case True{}:
      {==}
    case False{}:
      dc.one(x, m, r)

def dc.src(c: Cv.Scope, +i: Nat, +t: Cv.Ty, +p: Bool, +r: Bool, +v: Cv.Val, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, +tk: Bool, +dr: List<&2, Cv.Bind>) -> {Cv.doc.first(tk, i, Cv.layer(Cv.doc.pick(Cv.Decl.local(Cv.Decl{i, t, c, p, r, v}), merged, global), ds, Cv.Config{}, i, None{}), dr) == Cvar.spec_doc.first(tk, i, Cvar.spec_last(Cvar.spec_doc.src(Cvar.spec_local(Cv.Decl{i, t, c, p, r, v}), merged, global), ds, Cv.Config{}, i, None{}), dr) : List<&2, Cv.Bind>}:
  match c:
    case Cv.Global{}:
      +l = Cv.layer(global, ds, Cv.Config{}, i, None{})
      %LR.re.layer(global, ds, Cv.Config{}, i, None{}) : {Cv.doc.first(tk, i, l, dr) == Cvar.spec_doc.first(tk, i, _, dr) : List<&2, Cv.Bind>}
      dc.first(tk, i, l, dr)
    case Cv.Local{}:
      +l = Cv.layer(merged, ds, Cv.Config{}, i, None{})
      %LR.re.layer(merged, ds, Cv.Config{}, i, None{}) : {Cv.doc.first(tk, i, l, dr) == Cvar.spec_doc.first(tk, i, _, dr) : List<&2, Cv.Bind>}
      dc.first(tk, i, l, dr)

def dc.go(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>, +before: List<&2, Cv.Decl>) -> {Cv.document.go(xs, ds, merged, global, before) == Cvar.spec_document(xs, ds, merged, global, Cvar.spec_ids(before)) : List<&2, Cv.Bind>}:
  match xs:
    case Nil{}:
      {==}
    case Cv.Decl{+i, +t, +c, +p, +r, +v} <> +rest:
      +d = {Cv.Decl{i, t, c, p, r, v} : Cv.Decl}
      +nb = List.append(&2, Cv.Decl, before, [d])
      +tk = Maybe.is_some(&2, Cv.Decl, Cv.find(before, i))
      +dr = Cv.document.go(rest, ds, merged, global, nb)
      +src = Cv.doc.pick(Cv.Decl.local(d), merged, global)
      +l = Cv.layer(src, ds, Cv.Config{}, i, None{})
      %LR.re.ids_snoc(before, d) : {Cv.doc.first(tk, i, l, dr) == Cvar.spec_doc.first(Cvar.spec_mem(i, Cvar.spec_ids(before)), i, Cvar.spec_last(Cvar.spec_doc.src(Cvar.spec_local(d), merged, global), ds, Cv.Config{}, i, None{}), Cvar.spec_document(rest, ds, merged, global, _)) : List<&2, Cv.Bind>}
      %dc.go(rest, ds, merged, global, nb) : {Cv.doc.first(tk, i, l, dr) == Cvar.spec_doc.first(Cvar.spec_mem(i, Cvar.spec_ids(before)), i, Cvar.spec_last(Cvar.spec_doc.src(Cvar.spec_local(d), merged, global), ds, Cv.Config{}, i, None{}), _) : List<&2, Cv.Bind>}
      %LR.re.mem(before, i) : {Cv.doc.first(tk, i, l, dr) == Cvar.spec_doc.first(_, i, Cvar.spec_last(Cvar.spec_doc.src(Cvar.spec_local(d), merged, global), ds, Cv.Config{}, i, None{}), dr) : List<&2, Cv.Bind>}
      dc.src(c, i, t, p, r, v, ds, merged, global, tk, dr)

def Cvar.cvar_document_exact(ds, merged, global):
  dc.go(ds, ds, merged, global, Nil{})
