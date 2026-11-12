# eukhe: the proof of LAW glob_step_malformed_keeps
#
# PROOF: by the event the text reads as. No event, a path's time and the
# page keep the glob; a path whole answers the empty reply, not the
# malformed-event error, so it contradicts the premise.

import Base
import ../../bend/doc_glob.bend as Gb
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/doc_glob.bend as DocGlob

def gsk.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def gsk.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : gsk.BD(_, G)
  Unit{}

# a path whole answers the empty reply
def gsk.fin(+s: Nat, +k: Nat, +c: Nat, +len: Nat, +low: Nat, +xs: List<&2, Gb.It>, f: Gb.Fin, bad: {String.eq(DocGlob.glob.Snd(FGb.step.fin(s, k, c, f)), Wr.err("doc_glob: malformed event")) == True{} : Bool}) -> {DocGlob.glob.Fst(FGb.step.fin(s, k, c, f)) == FGb.Gl{s, k, c, len, low, xs} : FGb.St}:
  match f:
    case Gb.Fin{ys, n, w}:
      gsk.absurd({DocGlob.glob.Fst(FGb.step.fin(s, k, c, Gb.Fin{ys, n, w})) == FGb.Gl{s, k, c, len, low, xs} : FGb.St}, Equal.sym(Bool, False{}, True{}, bad))

def gsk.main(+s: Nat, +k: Nat, +c: Nat, +len: Nat, +low: Nat, +xs: List<&2, Gb.It>, m: Maybe<&2, FGb.Ev>, bad: {String.eq(DocGlob.glob.Snd(FGb.step.ev(FGb.Gl{s, k, c, len, low, xs}, m)), Wr.err("doc_glob: malformed event")) == True{} : Bool}) -> {DocGlob.glob.Fst(FGb.step.ev(FGb.Gl{s, k, c, len, low, xs}, m)) == FGb.Gl{s, k, c, len, low, xs} : FGb.St}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case FGb.Met{t}:
          {==}
        case FGb.Add{t, p}:
          gsk.fin(s, k, c, len, low, xs, Gb.fin(Gb.ins(Gb.it(t, p), xs), c), bad)
        case FGb.Show{}:
          {==}

def DocGlob.glob_step_malformed_keeps(s, k, c, len, low, xs, x, bad):
  gsk.main(s, k, c, len, low, xs, FGb.ev(Wr.get_nat(x)), bad)
