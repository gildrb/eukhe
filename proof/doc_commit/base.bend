# eukhe: lemmas the proofs of area doc_commit share

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../base/staging.bend as LStg

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

# the code's text comparison: a text is the same as itself, and the same
# texts are equal
def dcl.same_refl(+a: String) -> {Cm.same(a, a) == True{} : Bool}:
  Equal.trans(Bool, Cm.same(a, a), LawsBase.text_same(a, a), True{}, dcw.same(a, a), LStg.stg.same_refl(a))

def dcl.same_eq(+a: String, +b: String, e: {Cm.same(a, b) == True{} : Bool}) -> {a == b : String}:
  LStg.stg.same_eq(a, b, Equal.trans(Bool, LawsBase.text_same(a, b), Cm.same(a, b), True{}, Equal.sym(Bool, Cm.same(a, b), LawsBase.text_same(a, b), dcw.same(a, b)), e))

# Logic and numbers
# -----------------

def dcl.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dcl.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, dcl.add_zero(p))

def dcl.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), dcl.add_succ(p, b))

def dcl.nat_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      dcl.nat_refl(p)

def dcl.nat_sound(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      dcw.ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      dcw.ft({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, p, q, dcl.nat_sound(p, q, h))

# The write tool (F2): the digests of the model's versions
# --------------------------------------------------------

# two digests are the same text exactly when their versions are equal
def dcl.dg_same(a: Nat, b: Nat) -> {Cm.same(DocCommit.dg(a), DocCommit.dg(b)) == Nat.is_eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      dcl.dg_same(p, q)

# the shipped membership on digests is the model's on versions
def dcl.member_dg(+v: Nat, s: List<&2, Nat>) -> {Cm.member(DocCommit.dg(v), DocCommit.dgs(s)) == Cm.mem(v, s) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +x <> +rest:
      %dcl.dg_same(x, v) : {Bool.or(Cm.same(DocCommit.dg(x), DocCommit.dg(v)), Cm.member(DocCommit.dg(v), DocCommit.dgs(rest))) == Bool.or(_, Cm.mem(v, rest)) : Bool}
      %dcl.member_dg(v, rest) : {Bool.or(Cm.same(DocCommit.dg(x), DocCommit.dg(v)), Cm.member(DocCommit.dg(v), DocCommit.dgs(rest))) == Bool.or(Cm.same(DocCommit.dg(x), DocCommit.dg(v)), _) : Bool}
      {==}

def dcl.unsee_put(+x: Nat, -r1: List<&2, String>, -r2: List<&2, Nat>, b: Bool, ih: {r1 == DocCommit.dgs(r2) : List<&2, String>}) -> {Cm.unsee.put(DocCommit.dg(x), r1, b) == DocCommit.dgs(Cm.drop.put(x, r2, b)) : List<&2, String>}:
  match b:
    case True{}:
      ih
    case False{}:
      Equal.cong(List<&2, String>, List<&2, String>, z => DocCommit.dg(x) <> z, r1, DocCommit.dgs(r2), ih)

# the shipped unsee on digests is the model's drop on versions
def dcl.unsee_dg(+v: Nat, s: List<&2, Nat>) -> {Cm.unsee(DocCommit.dg(v), DocCommit.dgs(s)) == DocCommit.dgs(Cm.drop(v, s)) : List<&2, String>}:
  match s:
    case Nil{}:
      {==}
    case +x <> +rest:
      %dcl.dg_same(x, v) : {Cm.unsee.put(DocCommit.dg(x), Cm.unsee(DocCommit.dg(v), DocCommit.dgs(rest)), Cm.same(DocCommit.dg(x), DocCommit.dg(v))) == DocCommit.dgs(Cm.drop.put(x, Cm.drop(v, rest), _)) : List<&2, String>}
      dcl.unsee_put(x, Cm.unsee(DocCommit.dg(v), DocCommit.dgs(rest)), Cm.drop(v, rest), Cm.same(DocCommit.dg(x), DocCommit.dg(v)), dcl.unsee_dg(v, rest))

def dcl.take_dg(l: List<&2, Nat>, n: Nat) -> {List.take(&2, String, DocCommit.dgs(l), n) == DocCommit.dgs(List.take(&2, Nat, l, n)) : List<&2, String>}:
  match l:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case +x <> +r:
      match n:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(List<&2, String>, List<&2, String>, z => DocCommit.dg(x) <> z, List.take(&2, String, DocCommit.dgs(r), p), DocCommit.dgs(List.take(&2, Nat, r, p)), dcl.take_dg(r, p))

# the shipped seen list on digests is the model's saw on versions
def dcl.seen_dg(+c: Nat, +s: List<&2, Nat>) -> {Cm.seen(DocCommit.dg(c), DocCommit.dgs(s)) == DocCommit.dgs(Cm.saw(c, s)) : List<&2, String>}:
  %Equal.sym(List<&2, String>, Cm.unsee(DocCommit.dg(c), DocCommit.dgs(s)), DocCommit.dgs(Cm.drop(c, s)), dcl.unsee_dg(c, s)) : {List.take(&2, String, DocCommit.dg(c) <> _, 8n) == DocCommit.dgs(Cm.saw(c, s)) : List<&2, String>}
  dcl.take_dg(c <> Cm.drop(c, s), 8n)

# A move (F5)
# -----------

# a file named n wherever it is makes n taken
def dcl.has_at(pre: List<&2, Cm.Entry>, +n: Nat, +b: Nat, +post: List<&2, Cm.Entry>) -> {Cm.has(n, List.append(&2, Cm.Entry, pre, Cm.Entry{n, b} <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, dcl.nat_refl(n)) : {Bool.or(_, Cm.has(n, post)) == True{} : Bool}
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, g}:
          %Equal.sym(Bool, Cm.has(n, List.append(&2, Cm.Entry, rest, Cm.Entry{n, b} <> post)), True{}, dcl.has_at(rest, n, b, post)) : {Bool.or(Nat.is_eq(m, n), _) == True{} : Bool}
          dcl.or_true(Nat.is_eq(m, n))

def dcl.has_tail(+m: Nat, +g: Nat, +n: Nat, -rest: List<&2, Cm.Entry>, s: Sigma<&1, &1, DocCommit.EntAt, w => {rest == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>) -> Sigma<&1, &1, DocCommit.EntAt, w => {Cm.Entry{m, g} <> rest == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>:
  (w, p) = s
  match w:
    case DocCommit.EntAt{+pre, +bd, +post}:
      (DocCommit.EntAt{Cm.Entry{m, g} <> pre, bd, post}, Equal.cong(List<&2, Cm.Entry>, List<&2, Cm.Entry>, z => Cm.Entry{m, g} <> z, rest, DocCommit.ent_at(DocCommit.EntAt{pre, bd, post}, n), p))

def dcl.has_from(+m: Nat, +g: Nat, +n: Nat, +rest: List<&2, Cm.Entry>, b: Bool, eb: {Nat.is_eq(m, n) == b : Bool}, h: {Bool.or(b, Cm.has(n, rest)) == True{} : Bool}, ih: {Cm.has(n, rest) == True{} : Bool} -> Sigma<&1, &1, DocCommit.EntAt, w => {rest == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>) -> Sigma<&1, &1, DocCommit.EntAt, w => {Cm.Entry{m, g} <> rest == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>:
  match b:
    case True{}:
      (DocCommit.EntAt{Nil{}, g, rest}, Equal.cong(Nat, List<&2, Cm.Entry>, z => Cm.Entry{z, g} <> rest, m, n, dcl.nat_sound(m, n, eb)))
    case False{}:
      dcl.has_tail(m, g, n, rest, ih(h))

# n is taken only when a file is named n: its place
def dcl.has_only(+n: Nat, es: List<&2, Cm.Entry>, taken: {Cm.has(n, es) == True{} : Bool}) -> Sigma<&1, &1, DocCommit.EntAt, w => {es == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>:
  match es:
    case Nil{}:
      dcw.ft(Sigma<&1, &1, DocCommit.EntAt, w => {Nil{} == DocCommit.ent_at(w, n) : List<&2, Cm.Entry>}>, taken)
    case e <> +rest:
      match e:
        case Cm.Entry{+m, +g}:
          dcl.has_from(m, g, n, rest, Nat.is_eq(m, n), {==}, taken, h => dcl.has_only(n, rest, h))

def dcl.rename_put_len(+t: Nat, +m: Nat, g: Nat, -r: List<&2, Cm.Entry>, b: Bool) -> {List.length(&2, Cm.Entry, Cm.rename.put(t, m, g, r, b)) == 1n+List.length(&2, Cm.Entry, r) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a rename keeps the number of files
def dcl.rename_len(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>) -> {List.length(&2, Cm.Entry, Cm.rename(s, t, es)) == List.length(&2, Cm.Entry, es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, +g}:
          Equal.trans(Nat, List.length(&2, Cm.Entry, Cm.rename.put(t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s))), 1n+List.length(&2, Cm.Entry, Cm.rename(s, t, rest)), 1n+List.length(&2, Cm.Entry, rest), dcl.rename_put_len(t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s)), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Cm.Entry, Cm.rename(s, t, rest)), List.length(&2, Cm.Entry, rest), dcl.rename_len(s, t, rest)))

def dcl.get_put(+t: Nat, +m: Nat, g: Nat, -r: List<&2, Cm.Entry>, b: Bool, -k: Nat) -> {List.get(&2, Cm.Entry, Cm.rename.put(t, m, g, r, b), 1n+k) == List.get(&2, Cm.Entry, r, k) : Maybe<&2, Cm.Entry>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcl.renamed_put(+t: Nat, +m: Nat, +g: Nat, -r: List<&2, Cm.Entry>, -x: Cm.Entry, b: Bool, at: {Cm.rename.put(t, m, g, r, b) == x <> r : List<&2, Cm.Entry>}) -> {List.get(&2, Cm.Entry, Cm.rename.put(t, m, g, r, b), 0n) == Some{x} : Maybe<&2, Cm.Entry>}:
  %Equal.sym(List<&2, Cm.Entry>, Cm.rename.put(t, m, g, r, b), x <> r, at) : {List.get(&2, Cm.Entry, _, 0n) == Some{x} : Maybe<&2, Cm.Entry>}
  {==}

# after a rename, the file in a place is the file the rename put there:
# x, the renamed file of Entry{m, b} (rn)
def dcl.renamed_at(+s: Nat, +t: Nat, pre: List<&2, Cm.Entry>, +m: Nat, +b: Nat, +post: List<&2, Cm.Entry>, +x: Cm.Entry, rn: {Cm.rename.put(t, m, b, Cm.rename(s, t, post), Nat.is_eq(m, s)) == x <> Cm.rename(s, t, post) : List<&2, Cm.Entry>}) -> {List.get(&2, Cm.Entry, Cm.rename(s, t, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post)), List.length(&2, Cm.Entry, pre)) == Some{x} : Maybe<&2, Cm.Entry>}:
  match pre:
    case Nil{}:
      dcl.renamed_put(t, m, b, Cm.rename(s, t, post), x, Nat.is_eq(m, s), rn)
    case e <> +rest:
      match e:
        case Cm.Entry{+n, +g}:
          Equal.trans(Maybe<&2, Cm.Entry>, List.get(&2, Cm.Entry, Cm.rename.put(t, n, g, Cm.rename(s, t, List.append(&2, Cm.Entry, rest, Cm.Entry{m, b} <> post)), Nat.is_eq(n, s)), 1n+List.length(&2, Cm.Entry, rest)), List.get(&2, Cm.Entry, Cm.rename(s, t, List.append(&2, Cm.Entry, rest, Cm.Entry{m, b} <> post)), List.length(&2, Cm.Entry, rest)), Some{x}, dcl.get_put(t, n, g, Cm.rename(s, t, List.append(&2, Cm.Entry, rest, Cm.Entry{m, b} <> post)), Nat.is_eq(n, s), List.length(&2, Cm.Entry, rest)), dcl.renamed_at(s, t, rest, m, b, post, x, rn))

# the put of a file named as the source renames it; of another keeps it
def dcl.put_src(+t: Nat, +m: Nat, +g: Nat, -r: List<&2, Cm.Entry>, b: Bool, eb: {b == True{} : Bool}) -> {Cm.rename.put(t, m, g, r, b) == Cm.Entry{t, g} <> r : List<&2, Cm.Entry>}:
  match b:
    case True{}:
      {==}
    case False{}:
      dcw.ft({Cm.rename.put(t, m, g, r, False{}) == Cm.Entry{t, g} <> r : List<&2, Cm.Entry>}, eb)

def dcl.put_other(+t: Nat, +m: Nat, +g: Nat, -r: List<&2, Cm.Entry>, b: Bool, eb: {b == False{} : Bool}) -> {Cm.rename.put(t, m, g, r, b) == Cm.Entry{m, g} <> r : List<&2, Cm.Entry>}:
  match b:
    case True{}:
      dcw.tf({Cm.rename.put(t, m, g, r, True{}) == Cm.Entry{m, g} <> r : List<&2, Cm.Entry>}, eb)
    case False{}:
      {==}
