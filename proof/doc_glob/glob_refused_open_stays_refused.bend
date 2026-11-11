# eukhe: the proof of LAW glob_refused_open_stays_refused
#
# PROOF: an open that reads a skip and a limit answers the empty reply,
# not the malformed-open error; so an open that answers that error opens
# the refused state (grs.shut), and the refused state answers every text
# with the refused-open error and stays refused (grs.texts, by induction
# on the texts).

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/doc_glob.bend as DocGlob

def grs.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def grs.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : grs.BD(_, G)
  Unit{}

def grs.lim(+s: Nat, m: Maybe<&2, Maybe<&2, Nat>>, refused: {String.eq(DocGlob.glob.Snd(FGb.open.lim(s, m)), Wr.err("doc_glob: malformed open")) == True{} : Bool}) -> {(FGb.Shut{}, Wr.err("doc_glob: malformed open")) == FGb.open.lim(s, m) : FGb.St & String}:
  match m:
    case None{}:
      {==}
    case Some{lim}:
      grs.absurd({(FGb.Shut{}, Wr.err("doc_glob: malformed open")) == FGb.open.lim(s, Some{lim}) : FGb.St & String}, Equal.sym(Bool, False{}, True{}, refused))

# an open answered with the malformed-open error opens the refused state
def grs.shut(d: Wr.Dec<Nat>, refused: {String.eq(DocGlob.glob.Snd(FGb.open.got(d)), Wr.err("doc_glob: malformed open")) == True{} : Bool}) -> {(FGb.Shut{}, Wr.err("doc_glob: malformed open")) == FGb.open.got(d) : FGb.St & String}:
  match d:
    case Wr.Got{s, r}:
      grs.lim(s, FGb.lim.tag(Wr.get_nat(r)), refused)
    case Wr.Bad{}:
      {==}

# the refused state answers every text with the refused-open error
def grs.texts(ts: List<&2, String>, +o: String) -> {DocGlob.glob.Texts(ts, (FGb.Shut{}, o)) == o <> DocGlob.glob.Rep(List.length(&2, String, ts), Wr.err("doc_glob: the open was refused")) : List<&2, String>}:
  match ts:
    case Nil{}:
      {==}
    case x <> t:
      %grs.texts(t, Wr.err("doc_glob: the open was refused")) : {o <> DocGlob.glob.Texts(t, (FGb.Shut{}, Wr.err("doc_glob: the open was refused"))) == o <> _ : List<&2, String>}
      {==}

def DocGlob.glob_refused_open_stays_refused(x, ts, refused):
  %grs.shut(Wr.get_nat(x), refused) : {DocGlob.glob.Texts(ts, _) == Wr.err("doc_glob: malformed open") <> DocGlob.glob.Rep(List.length(&2, String, ts), Wr.err("doc_glob: the open was refused")) : List<&2, String>}
  grs.texts(ts, Wr.err("doc_glob: malformed open"))
