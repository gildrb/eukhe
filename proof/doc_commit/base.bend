# eukhe: lemmas the proofs of area doc_commit share

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit

# ---- documents ----

# proof_documents: the lemmas behind the laws of LAWS.bend section documents
# (Laws.<law> in PROOF.bend delegates here; the lines and endings laws
# delegate to PROOF.bend section doc_lines), one section per model of
# bend/doc_*.bend. Each section keeps its own name prefix: pc. (an edit of
# many files, the write tool, a move, the temp sweep), pv. (seen lines),
# ps. (what grep searched, continuations), pdt. (tags).

# ==== commit ====
# proof_doc_commit: the edit, write, move and sweep laws of
# LAWS.bend section documents (F1, F9, F2, F5, F10): the reply of an edit names
# exactly the files that landed, a conflict lands nothing, a sound edit
# lands every file; a write never replaces a version the session did not
# see; a move never replaces a file; a sweep removes only the free
# temporary files of its target, and all of them.
# Logic and numbers
# -----------------

def documents.pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def documents.pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : documents.pc.BD(_, Unit, A)
  Unit{}

# Sweep
# -----

def pc.put_app(+n: Cm.Temp, a: List<&2, Cm.Temp>, +c: List<&2, Cm.Temp>, b: Bool) -> {Cm.sweep.put(n, List.append(&2, Cm.Temp, a, c), b) == List.append(&2, Cm.Temp, Cm.sweep.put(n, a, b), c) : List<&2, Cm.Temp>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.sweep_app(pre: List<&2, Cm.Temp>, +x: List<&2, Cm.Temp>) -> {List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(x)) == Cm.sweep(List.append(&2, Cm.Temp, pre, x)) : List<&2, Cm.Temp>}:
  match pre:
    case Nil{}:
      {==}
    case +n <> +rest:
      %pc.put_app(n, Cm.sweep(rest), Cm.sweep(x), Cm.removes(n)) : {_ == Cm.sweep.put(n, Cm.sweep(List.append(&2, Cm.Temp, rest, x)), Cm.removes(n)) : List<&2, Cm.Temp>}
      %pc.sweep_app(rest, x) : {Cm.sweep.put(n, List.append(&2, Cm.Temp, Cm.sweep(rest), Cm.sweep(x)), Cm.removes(n)) == Cm.sweep.put(n, _, Cm.removes(n)) : List<&2, Cm.Temp>}
      {==}

# an entry the sweep keeps: the sweep of the whole is the sweep of the parts
def pc.kept(+pre: List<&2, Cm.Temp>, +n: Cm.Temp, +post: List<&2, Cm.Temp>, no: {False{} == Cm.removes(n) : Bool}) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, n <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  %pc.sweep_app(pre, n <> post) : {_ == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}
  %no : {List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep.put(n, Cm.sweep(post), _)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}
  {==}

# The writer's choices
# --------------------

def dcw.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def dcw.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : dcw.BT(_, G)
  Unit{}

# False is not True
def dcw.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  dcw.tf(G, Equal.sym(Bool, False{}, True{}, e))

def dcw.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def dcw.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      dcw.ft({b == True{} : Bool}, h)

def dcw.and_tt(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# the code's char-by-char comparison is the spec's text_same
def dcw.same(a: String, b: String) -> {Cm.same(a, b) == LawsBase.text_same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{x, u} SCon{y, v}:
      %dcw.same(u, v) : {Bool.and(Char.is_eq(x, y), Cm.same(u, v)) == Bool.and(Char.is_eq(x, y), _) : Bool}
      {==}

# the code's prefix test is the spec's
def dcw.starts(p: String, s: String) -> {Cm.starts(p, s) == DocCommit.sp_starts(p, s) : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, q}:
      match s:
        case SNil{}:
          {==}
        case SCon{d, t}:
          %dcw.starts(q, t) : {Bool.and(Char.is_eq(c, d), Cm.starts(q, t)) == Bool.and(Char.is_eq(c, d), _) : Bool}
          {==}
