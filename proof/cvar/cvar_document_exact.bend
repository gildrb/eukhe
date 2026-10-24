# eukhe: the proof of LAW cvar_document_exact
# Declaration by declaration: the document a cvar's scope picks is the
# spec's, and the model's layer over it is the spec's last set that counts
# (LR.re.layer).

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

def dc.go(xs: List<&2, Cv.Decl>, +ds: List<&2, Cv.Decl>, +merged: List<&2, Cv.Bind>, +global: List<&2, Cv.Bind>) -> {Cv.document.go(xs, ds, merged, global) == Cvar.spec_document(xs, ds, merged, global) : List<&2, Cv.Bind>}:
  match xs:
    case Nil{}:
      {==}
    case Cv.Decl{+i, t, c, p, r, v} <> +rest:
      match c:
        case Cv.Global{}:
          +d = Cv.document.go(rest, ds, merged, global)
          +l = Cv.layer(global, ds, Cv.Config{}, i, None{})
          %LR.re.layer(global, ds, Cv.Config{}, i, None{}) : {Cv.doc.one(i, l, d) == Cvar.spec_doc.one(i, _, Cvar.spec_document(rest, ds, merged, global)) : List<&2, Cv.Bind>}
          %dc.go(rest, ds, merged, global) : {Cv.doc.one(i, l, d) == Cvar.spec_doc.one(i, l, _) : List<&2, Cv.Bind>}
          dc.one(i, l, d)
        case Cv.Local{}:
          +d = Cv.document.go(rest, ds, merged, global)
          +l = Cv.layer(merged, ds, Cv.Config{}, i, None{})
          %LR.re.layer(merged, ds, Cv.Config{}, i, None{}) : {Cv.doc.one(i, l, d) == Cvar.spec_doc.one(i, _, Cvar.spec_document(rest, ds, merged, global)) : List<&2, Cv.Bind>}
          %dc.go(rest, ds, merged, global) : {Cv.doc.one(i, l, d) == Cvar.spec_doc.one(i, l, _) : List<&2, Cv.Bind>}
          dc.one(i, l, d)

def Cvar.cvar_document_exact(ds, merged, global):
  dc.go(ds, ds, merged, global)
