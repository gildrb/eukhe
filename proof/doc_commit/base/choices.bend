# eukhe: lemmas the proofs of laws/doc_commit/choices.bend share (R1-R6):
# the check's index after clear files, the reply's counts and notes by
# place, the gate's membership by place, the seen list's unsee, the
# sweep's indices around one entry and the prefix tests

import Base
import ../../../bend/doc_commit.bend as Cm
import ../../../laws/base.bend as LawsBase
import ../../../laws/doc_commit.bend as DocCommit
import ../../../laws/doc_commit/choices.bend as DocCommitChoices
import ../base.bend as LA
import ../../base/staging.bend as LStg

# Logic
# -----

def dcq.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LA.dcw.ft({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def dcq.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def dcq.MI(m: Maybe<&2, Cm.Note>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def dcq.none_some(-b: Cm.Note, -G: Type, e: {None{} == Some{b} : Maybe<&2, Cm.Note>}) -> G:
  %e : dcq.MI(_, G)
  Unit{}

# Chars: Char.is_eq is symmetric
# ------------------------------

def dcq.ne_refl(+c: Char, +d: Char, de: {d == c : Char}, eb: {Char.is_eq(c, d) == False{} : Bool}) -> {Char.is_eq(c, c) == False{} : Bool}:
  %de : {Char.is_eq(c, _) == False{} : Bool}
  eb

def dcq.sym_f(+c: Char, +d: Char, eb: {Char.is_eq(c, d) == False{} : Bool}, b: Bool, e2: {Char.is_eq(d, c) == b : Bool}) -> {Char.is_eq(d, c) == False{} : Bool}:
  match b:
    case True{}:
      LA.dcw.tf({Char.is_eq(d, c) == False{} : Bool}, Equal.trans(Bool, True{}, Char.is_eq(c, c), False{}, Equal.sym(Bool, Char.is_eq(c, c), True{}, LStg.stg.char_refl(c)), dcq.ne_refl(c, d, LStg.stg.char_sound(d, c, e2), eb)))
    case False{}:
      e2

def dcq.sym_go(+c: Char, +d: Char, b: Bool, eb: {Char.is_eq(c, d) == b : Bool}) -> {Char.is_eq(d, c) == b : Bool}:
  match b:
    case True{}:
      %LStg.stg.char_sound(c, d, eb) : {Char.is_eq(_, c) == True{} : Bool}
      LStg.stg.char_refl(c)
    case False{}:
      dcq.sym_f(c, d, eb, Char.is_eq(d, c), {==})

def dcq.char_sym(+c: Char, +d: Char) -> {Char.is_eq(d, c) == Char.is_eq(c, d) : Bool}:
  dcq.sym_go(c, d, Char.is_eq(c, d), {==})

# R1: the check after clear files
# -------------------------------

def dcq.clear(n: Nat, +k: Nat) -> {Cm.check.go(DocCommitChoices.clears(n), k) == Cm.Go{} : Cm.Check}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      dcq.clear(m, 1n+k)

# n clear files before rest only move the check's index on by n
def dcq.skip(n: Nat, +rest: List<&2, Cm.Met>, +k: Nat) -> {Cm.check.go(List.append(&2, Cm.Met, DocCommitChoices.clears(n), rest), k) == Cm.check.go(rest, Nat.add(n, k)) : Cm.Check}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      Equal.trans(Cm.Check, Cm.check.go(List.append(&2, Cm.Met, DocCommitChoices.clears(m), rest), 1n+k), Cm.check.go(rest, Nat.add(m, 1n+k)), Cm.check.go(rest, 1n+Nat.add(m, k)), dcq.skip(m, rest, 1n+k), Equal.cong(Nat, Cm.Check, z => Cm.check.go(rest, z), Nat.add(m, 1n+k), 1n+Nat.add(m, k), LA.dcl.add_succ(m, k)))

# R3: the reply's counts
# ----------------------

def dcq.failed(fs: List<&2, Cm.Fate>) -> {Cm.any.failed(fs) == Nat.is_gt(DocCommitChoices.nfailed(fs), 0n) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcq.failed(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcq.failed(rest)
            case Cm.Fails{}:
              {==}
        case Cm.Untried{}:
          dcq.failed(rest)

def dcq.landed(fs: List<&2, Cm.Fate>) -> {Bool.not(Cm.any.landed(fs)) == Nat.is_eq(DocCommitChoices.nlanded(fs), 0n) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcq.landed(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              {==}
            case Cm.Fails{}:
              dcq.landed(rest)
        case Cm.Untried{}:
          dcq.landed(rest)

def dcq.unwritten(fs: List<&2, Cm.Fate>) -> {Cm.unwritten(fs) == Nat.is_gt(DocCommitChoices.nunwritten(fs), 0n) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      match f:
        case Cm.Noop{}:
          dcq.unwritten(rest)
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              dcq.unwritten(rest)
            case Cm.Fails{}:
              {==}
        case Cm.Untried{}:
          {==}

# R3: the reply that is not an error
# ----------------------------------

def dcq.isf(b: Bool, -fs: List<&2, Cm.Fate>) -> {DocCommitChoices.is_failure(Cm.answer.go(b, fs)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcq.notes_go(b: Bool, +fs: List<&2, Cm.Fate>, ok: {DocCommitChoices.is_failure(Cm.answer.go(b, fs)) == False{} : Bool}) -> {DocCommitChoices.notes_of(Cm.answer.go(b, fs)) == Cm.reports(fs, Cm.first.failed(fs, 0n)) : List<&2, Cm.Note>}:
  match b:
    case True{}:
      LA.dcw.tf({DocCommitChoices.notes_of(Cm.answer.go(True{}, fs)) == Cm.reports(fs, Cm.first.failed(fs, 0n)) : List<&2, Cm.Note>}, ok)
    case False{}:
      {==}

def dcq.partial_go(b: Bool, +fs: List<&2, Cm.Fate>, ok: {DocCommitChoices.is_failure(Cm.answer.go(b, fs)) == False{} : Bool}) -> {DocCommitChoices.partial_of(Cm.answer.go(b, fs)) == Cm.unwritten(fs) : Bool}:
  match b:
    case True{}:
      LA.dcw.tf({DocCommitChoices.partial_of(Cm.answer.go(True{}, fs)) == Cm.unwritten(fs) : Bool}, ok)
    case False{}:
      {==}

# the notes of a reply that is not an error: one report a file
def dcq.notes(+fs: List<&2, Cm.Fate>, ok: {DocCommitChoices.is_failure(Cm.answer(fs)) == False{} : Bool}) -> {DocCommitChoices.notes_of(Cm.answer(fs)) == Cm.reports(fs, Cm.first.failed(fs, 0n)) : List<&2, Cm.Note>}:
  dcq.notes_go(Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), fs, ok)

def dcq.reports_len(fs: List<&2, Cm.Fate>, +k: Nat) -> {List.length(&2, Cm.Note, Cm.reports(fs, k)) == List.length(&2, Cm.Fate, fs) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> +rest:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Cm.Note, Cm.reports(rest, k)), List.length(&2, Cm.Fate, rest), dcq.reports_len(rest, k))

# the report in a file's place is the report of its fate
def dcq.rep_at(pre: List<&2, Cm.Fate>, +f: Cm.Fate, +post: List<&2, Cm.Fate>, +k: Nat) -> {List.get(&2, Cm.Note, Cm.reports(List.append(&2, Cm.Fate, pre, f <> post), k), List.length(&2, Cm.Fate, pre)) == Some{Cm.report.of(k, f)} : Maybe<&2, Cm.Note>}:
  match pre:
    case Nil{}:
      {==}
    case p <> rest:
      dcq.rep_at(rest, f, post, k)

# the report of a tried file or a no-op is its own note
def dcq.own(f: Cm.Fate, +k: Nat, -x: Cm.Note, own: {DocCommitChoices.own_note(f) == Some{x} : Maybe<&2, Cm.Note>}) -> {Some{Cm.report.of(k, f)} == Some{x} : Maybe<&2, Cm.Note>}:
  match f:
    case Cm.Noop{}:
      own
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          own
        case Cm.Fails{}:
          own
    case Cm.Untried{}:
      dcq.none_some(x, {Some{Cm.Skipped{k}} == Some{x} : Maybe<&2, Cm.Note>}, own)

# the first failure after files that did not fail is at their count
def dcq.ff_front(pre: List<&2, Cm.Fate>, +mid: List<&2, Cm.Fate>, +rest: List<&2, Cm.Fate>, +n: Nat, clean: {Nat.is_eq(DocCommitChoices.nfailed(pre), 0n) == True{} : Bool}) -> {Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), rest), n) == Nat.add(List.length(&2, Cm.Fate, pre), n) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case p <> +r:
      match p:
        case Cm.Noop{}:
          Equal.trans(Nat, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, r, Cm.Wrote{Cm.Fails{}} <> mid), rest), 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_front(r, mid, rest, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              Equal.trans(Nat, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, r, Cm.Wrote{Cm.Fails{}} <> mid), rest), 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_front(r, mid, rest, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))
            case Cm.Fails{}:
              LA.dcw.ft({Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, Cm.Wrote{Cm.Fails{}} <> r, Cm.Wrote{Cm.Fails{}} <> mid), rest), n) == Nat.add(List.length(&2, Cm.Fate, Cm.Wrote{Cm.Fails{}} <> r), n) : Nat}, clean)
        case Cm.Untried{}:
          Equal.trans(Nat, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, r, Cm.Wrote{Cm.Fails{}} <> mid), rest), 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_front(r, mid, rest, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))

# with no failure, the first failure is past the last file
def dcq.ff_all(xs: List<&2, Cm.Fate>, +n: Nat, clean: {Nat.is_eq(DocCommitChoices.nfailed(xs), 0n) == True{} : Bool}) -> {Cm.first.failed(xs, n) == Nat.add(List.length(&2, Cm.Fate, xs), n) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case p <> +r:
      match p:
        case Cm.Noop{}:
          Equal.trans(Nat, Cm.first.failed(r, 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_all(r, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))
        case Cm.Wrote{o}:
          match o:
            case Cm.Lands{w}:
              Equal.trans(Nat, Cm.first.failed(r, 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_all(r, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))
            case Cm.Fails{}:
              LA.dcw.ft({Cm.first.failed(Cm.Wrote{Cm.Fails{}} <> r, n) == Nat.add(List.length(&2, Cm.Fate, Cm.Wrote{Cm.Fails{}} <> r), n) : Nat}, clean)
        case Cm.Untried{}:
          Equal.trans(Nat, Cm.first.failed(r, 1n+n), Nat.add(List.length(&2, Cm.Fate, r), 1n+n), 1n+Nat.add(List.length(&2, Cm.Fate, r), n), dcq.ff_all(r, 1n+n, clean), LA.dcl.add_succ(List.length(&2, Cm.Fate, r), n))

def dcq.gt0(x: Nat, e: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {Nat.is_gt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      LA.dcw.ft({Nat.is_gt(1n+p, 0n) == False{} : Bool}, e)

# with no failure the reply is not an error
def dcq.no_fail(+fs: List<&2, Cm.Fate>, clean: {Nat.is_eq(DocCommitChoices.nfailed(fs), 0n) == True{} : Bool}) -> {DocCommitChoices.is_failure(Cm.answer(fs)) == False{} : Bool}:
  Equal.trans(Bool, DocCommitChoices.is_failure(Cm.answer(fs)), Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), False{}, dcq.isf(Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), fs), Equal.trans(Bool, Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), Bool.and(Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), Bool.not(Cm.any.landed(fs))), Bool.and(False{}, Bool.not(Cm.any.landed(fs))), Equal.cong(Bool, Bool, z => Bool.and(z, Bool.not(Cm.any.landed(fs))), Cm.any.failed(fs), Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), dcq.failed(fs)), Equal.cong(Bool, Bool, z => Bool.and(z, Bool.not(Cm.any.landed(fs))), Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), False{}, dcq.gt0(DocCommitChoices.nfailed(fs), clean))))

# R4: membership by place
# -----------------------

def dcq.member_at(pre: List<&2, String>, +g: String, +post: List<&2, String>) -> {Cm.member(g, List.append(&2, String, pre, g <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Cm.same(g, g), True{}, LA.dcl.same_refl(g)) : {Bool.or(_, Cm.member(g, post)) == True{} : Bool}
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Cm.member(g, List.append(&2, String, rest, g <> post)), True{}, dcq.member_at(rest, g, post)) : {Bool.or(Cm.same(x, g), _) == True{} : Bool}
      LA.dcl.or_true(Cm.same(x, g))

def dcq.str_tail(+x: String, +g: String, -rest: List<&2, String>, s: Sigma<&1, &1, DocCommitChoices.StrAt, w => {rest == DocCommitChoices.str_at(w, g) : List<&2, String>}>) -> Sigma<&1, &1, DocCommitChoices.StrAt, w => {x <> rest == DocCommitChoices.str_at(w, g) : List<&2, String>}>:
  (w, p) = s
  match w:
    case DocCommitChoices.StrAt{+pre, +post}:
      (DocCommitChoices.StrAt{x <> pre, post}, Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, rest, DocCommitChoices.str_at(DocCommitChoices.StrAt{pre, post}, g), p))

def dcq.mem_from(+x: String, +g: String, +rest: List<&2, String>, b: Bool, eb: {Cm.same(x, g) == b : Bool}, h: {Bool.or(b, Cm.member(g, rest)) == True{} : Bool}, ih: {Cm.member(g, rest) == True{} : Bool} -> Sigma<&1, &1, DocCommitChoices.StrAt, w => {rest == DocCommitChoices.str_at(w, g) : List<&2, String>}>) -> Sigma<&1, &1, DocCommitChoices.StrAt, w => {x <> rest == DocCommitChoices.str_at(w, g) : List<&2, String>}>:
  match b:
    case True{}:
      (DocCommitChoices.StrAt{Nil{}, rest}, Equal.cong(String, List<&2, String>, z => z <> rest, x, g, LA.dcl.same_eq(x, g, eb)))
    case False{}:
      dcq.str_tail(x, g, rest, ih(h))

# a digest the shipped membership finds is in some place
def dcq.mem_only(+g: String, s: List<&2, String>, h: {Cm.member(g, s) == True{} : Bool}) -> Sigma<&1, &1, DocCommitChoices.StrAt, w => {s == DocCommitChoices.str_at(w, g) : List<&2, String>}>:
  match s:
    case Nil{}:
      LA.dcw.ft(Sigma<&1, &1, DocCommitChoices.StrAt, w => {Nil{} == DocCommitChoices.str_at(w, g) : List<&2, String>}>, h)
    case +x <> +rest:
      dcq.mem_from(x, g, rest, Cm.same(x, g), {==}, h, h2 => dcq.mem_only(g, rest, h2))

# R5: the seen list's unsee
# -------------------------

def dcq.unsee_drop(+d: String, pre: List<&2, String>, +post: List<&2, String>) -> {Cm.unsee(d, List.append(&2, String, pre, d <> post)) == Cm.unsee(d, List.append(&2, String, pre, post)) : List<&2, String>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Cm.same(d, d), True{}, LA.dcl.same_refl(d)) : {Cm.unsee.put(d, Cm.unsee(d, post), _) == Cm.unsee(d, post) : List<&2, String>}
      {==}
    case +x <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, z => Cm.unsee.put(x, z, Cm.same(x, d)), Cm.unsee(d, List.append(&2, String, rest, d <> post)), Cm.unsee(d, List.append(&2, String, rest, post)), dcq.unsee_drop(d, rest, post))

def dcq.unsee_fresh(+d: String, s: List<&2, String>, +h: {DocCommitChoices.fresh(d, s) == True{} : Bool}) -> {Cm.unsee(d, s) == s : List<&2, String>}:
  match s:
    case Nil{}:
      {==}
    case +x <> +rest:
      +nx = dcq.not_true(LawsBase.text_same(x, d), LA.dcw.and_l(Bool.not(LawsBase.text_same(x, d)), DocCommitChoices.fresh(d, rest), h))
      +sx = Equal.trans(Bool, Cm.same(x, d), LawsBase.text_same(x, d), False{}, LA.dcw.same(x, d), nx)
      %Equal.sym(Bool, Cm.same(x, d), False{}, sx) : {Cm.unsee.put(x, Cm.unsee(d, rest), _) == x <> rest : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, Cm.unsee(d, rest), rest, dcq.unsee_fresh(d, rest, LA.dcw.and_r(Bool.not(LawsBase.text_same(x, d)), DocCommitChoices.fresh(d, rest), h)))

# R6: the sweep's indices around one entry
# ----------------------------------------

def dcq.gput_app(+n: Nat, a: List<&2, Nat>, -c: List<&2, Nat>, b: Bool) -> {Cm.gone.put(n, List.append(&2, Nat, a, c), b) == List.append(&2, Nat, Cm.gone.put(n, a, b), c) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcq.off_put(b: Bool, +m: Nat, +n: Nat, -x: List<&2, Nat>, -y: List<&2, Nat>, eq: {x == DocCommitChoices.shift(m, y) : List<&2, Nat>}) -> {Cm.gone.put(Nat.add(m, n), x, b) == DocCommitChoices.shift(m, Cm.gone.put(n, y, b)) : List<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.add(m, n) <> z, x, DocCommitChoices.shift(m, y), eq)
    case False{}:
      eq

# indices from m + n are the indices from n moved on by m
def dcq.off(+p: String, es: List<&2, Cm.Ent>, +m: Nat, +n: Nat) -> {Cm.gone.go(p, es, Nat.add(m, n)) == DocCommitChoices.shift(m, Cm.gone.go(p, es, n)) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      dcq.off_put(Cm.sweeps(p, e), m, n, Cm.gone.go(p, rest, 1n+Nat.add(m, n)), Cm.gone.go(p, rest, 1n+n), Equal.trans(List<&2, Nat>, Cm.gone.go(p, rest, 1n+Nat.add(m, n)), Cm.gone.go(p, rest, Nat.add(m, 1n+n)), DocCommitChoices.shift(m, Cm.gone.go(p, rest, 1n+n)), Equal.cong(Nat, List<&2, Nat>, z => Cm.gone.go(p, rest, z), 1n+Nat.add(m, n), Nat.add(m, 1n+n), Equal.sym(Nat, Nat.add(m, 1n+n), 1n+Nat.add(m, n), LA.dcl.add_succ(m, n))), dcq.off(p, rest, m, 1n+n)))

def dcq.at0(+p: String, +es: List<&2, Cm.Ent>, +k: Nat) -> {Cm.gone.go(p, es, k) == DocCommitChoices.shift(k, Cm.gone.go(p, es, 0n)) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Cm.gone.go(p, es, k), Cm.gone.go(p, es, Nat.add(k, 0n)), DocCommitChoices.shift(k, Cm.gone.go(p, es, 0n)), Equal.cong(Nat, List<&2, Nat>, z => Cm.gone.go(p, es, z), k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, LA.dcl.add_zero(k))), dcq.off(p, es, k, 0n))

# the sweep of entries split around x
def dcq.split(+p: String, pre: List<&2, Cm.Ent>, +x: Cm.Ent, +post: List<&2, Cm.Ent>, +n: Nat) -> {Cm.gone.go(p, List.append(&2, Cm.Ent, pre, x <> post), n) == List.append(&2, Nat, Cm.gone.go(p, pre, n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, pre), n))) : List<&2, Nat>}:
  match pre:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(List<&2, Nat>, Cm.gone.go(p, List.append(&2, Cm.Ent, rest, x <> post), 1n+n), List.append(&2, Nat, Cm.gone.go(p, rest, 1n+n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, rest), 1n+n))), dcq.split(p, rest, x, post, 1n+n)) : {Cm.gone.put(n, _, Cm.sweeps(p, e)) == List.append(&2, Nat, Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Cm.sweeps(p, e)), Cm.gone.go(p, x <> post, 1n+Nat.add(List.length(&2, Cm.Ent, rest), n))) : List<&2, Nat>}
      %LA.dcl.add_succ(List.length(&2, Cm.Ent, rest), n) : {Cm.gone.put(n, List.append(&2, Nat, Cm.gone.go(p, rest, 1n+n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, rest), 1n+n))), Cm.sweeps(p, e)) == List.append(&2, Nat, Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Cm.sweeps(p, e)), Cm.gone.go(p, x <> post, _)) : List<&2, Nat>}
      dcq.gput_app(n, Cm.gone.go(p, rest, 1n+n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, rest), 1n+n)), Cm.sweeps(p, e))

# an entry the sweep keeps, in its place
def dcq.kept_at(+p: String, +pre: List<&2, Cm.Ent>, +x: Cm.Ent, +post: List<&2, Cm.Ent>, no: {Cm.sweeps(p, x) == False{} : Bool}) -> {Cm.gone.go(p, List.append(&2, Cm.Ent, pre, x <> post), 0n) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, Cm.gone.go(p, List.append(&2, Cm.Ent, pre, x <> post), 0n), List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, pre), 0n))), dcq.split(p, pre, x, post, 0n)) : {_ == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Cm.Ent, pre), 0n), List.length(&2, Cm.Ent, pre), LA.dcl.add_zero(List.length(&2, Cm.Ent, pre))) : {List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.go(p, x <> post, _)) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  %Equal.sym(Bool, Cm.sweeps(p, x), False{}, no) : {List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.put(List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 1n+List.length(&2, Cm.Ent, pre)), _)) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, Cm.gone.go(p, pre, 0n), z), Cm.gone.go(p, post, 1n+List.length(&2, Cm.Ent, pre)), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n)), dcq.at0(p, post, 1n+List.length(&2, Cm.Ent, pre)))

# an entry the sweep removes, in its place
def dcq.gone_at(+p: String, +pre: List<&2, Cm.Ent>, +x: Cm.Ent, +post: List<&2, Cm.Ent>, yes: {Cm.sweeps(p, x) == True{} : Bool}) -> {Cm.gone.go(p, List.append(&2, Cm.Ent, pre, x <> post), 0n) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), List.length(&2, Cm.Ent, pre) <> DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, Cm.gone.go(p, List.append(&2, Cm.Ent, pre, x <> post), 0n), List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.go(p, x <> post, Nat.add(List.length(&2, Cm.Ent, pre), 0n))), dcq.split(p, pre, x, post, 0n)) : {_ == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), List.length(&2, Cm.Ent, pre) <> DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.add(List.length(&2, Cm.Ent, pre), 0n), List.length(&2, Cm.Ent, pre), LA.dcl.add_zero(List.length(&2, Cm.Ent, pre))) : {List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.go(p, x <> post, _)) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), List.length(&2, Cm.Ent, pre) <> DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  %Equal.sym(Bool, Cm.sweeps(p, x), True{}, yes) : {List.append(&2, Nat, Cm.gone.go(p, pre, 0n), Cm.gone.put(List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 1n+List.length(&2, Cm.Ent, pre)), _)) == List.append(&2, Nat, Cm.gone.go(p, pre, 0n), List.length(&2, Cm.Ent, pre) <> DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n))) : List<&2, Nat>}
  Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, Cm.gone.go(p, pre, 0n), List.length(&2, Cm.Ent, pre) <> z), Cm.gone.go(p, post, 1n+List.length(&2, Cm.Ent, pre)), DocCommitChoices.shift(1n+List.length(&2, Cm.Ent, pre), Cm.gone.go(p, post, 0n)), dcq.at0(p, post, 1n+List.length(&2, Cm.Ent, pre)))

# R6: the prefix tests
# --------------------

# the code's prefix test is Base's String.starts_with
def dcq.sw_step(b: Bool, -x: Bool, -q: String, -t: String, ih: {x == String.starts_with.go(q, t) : Bool}) -> {Bool.and(b, x) == String.starts_with.go.if(q, t, b) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def dcq.starts_sw(p: String, s: String) -> {Cm.starts(p, s) == String.starts_with(s, p) : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +q}:
      match s:
        case SNil{}:
          {==}
        case SCon{+d, +t}:
          %dcq.char_sym(d, c) : {Bool.and(Char.is_eq(c, d), Cm.starts(q, t)) == String.starts_with.go.if(q, t, _) : Bool}
          dcq.sw_step(Char.is_eq(c, d), Cm.starts(q, t), q, t, dcq.starts_sw(q, t))

# a text starts with itself
def dcq.starts_app(q: String, +r: String) -> {Cm.starts(q, String.append(q, r)) == True{} : Bool}:
  match q:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, LStg.stg.char_refl(c)) : {Bool.and(_, Cm.starts(u, String.append(u, r))) == True{} : Bool}
      dcq.starts_app(u, r)

# a char of a dashless text is not `-`
def dcq.dash_head(+c: Char, +t: String, hd: {DocCommitChoices.dashless(SCon{c, t}) == True{} : Bool}) -> {Char.is_eq(c, '-') == False{} : Bool}:
  dcq.not_true(Char.is_eq(c, '-'), LA.dcw.and_l(Bool.not(Char.is_eq(c, '-')), DocCommitChoices.dashless(t), hd))

# an entry whose name the prefix does not start is not swept, held or not
def dcq.no_sweep(+p: String, +n: String, held: Bool, s0: {Cm.starts(p, n) == False{} : Bool}) -> {Cm.sweeps(p, Cm.Ent{n, held}) == False{} : Bool}:
  %Equal.sym(Bool, Cm.starts(p, n), False{}, s0) : {Bool.and(_, Bool.not(held)) == False{} : Bool}
  {==}

def dcq.pf_step(b: Bool, -x: Bool, -ts: Bool, ne: {Bool.and(b, ts) == False{} : Bool}, ih: {ts == False{} : Bool} -> {x == False{} : Bool}) -> {Bool.and(b, x) == False{} : Bool}:
  match b:
    case True{}:
      ih(ne)
    case False{}:
      {==}

# two different dashless digests: neither's `h-` starts the other's
# `g-` and what follows
def dcq.pf(h: String, g: String, +rest: String, hd: {DocCommitChoices.dashless(h) == True{} : Bool}, gd: {DocCommitChoices.dashless(g) == True{} : Bool}, ne: {LawsBase.text_same(h, g) == False{} : Bool}) -> {Cm.starts(String.append(h, "-"), String.append(String.append(g, "-"), rest)) == False{} : Bool}:
  match h g:
    case SNil{} SNil{}:
      LA.dcw.tf({Cm.starts(String.append(SNil{}, "-"), String.append(String.append(SNil{}, "-"), rest)) == False{} : Bool}, ne)
    case SNil{} SCon{+d, +gt}:
      %Equal.sym(Bool, Char.is_eq('-', d), False{}, Equal.trans(Bool, Char.is_eq('-', d), Char.is_eq(d, '-'), False{}, dcq.char_sym(d, '-'), dcq.dash_head(d, gt, gd))) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case SCon{+c, +ht} SNil{}:
      %Equal.sym(Bool, Char.is_eq(c, '-'), False{}, dcq.dash_head(c, ht, hd)) : {Bool.and(_, Cm.starts(String.append(ht, "-"), rest)) == False{} : Bool}
      {==}
    case SCon{+c, +ht} SCon{+d, +gt}:
      dcq.pf_step(Char.is_eq(c, d), Cm.starts(String.append(ht, "-"), String.append(String.append(gt, "-"), rest)), LawsBase.text_same(ht, gt), ne, n2 => dcq.pf(ht, gt, rest, LA.dcw.and_r(Bool.not(Char.is_eq(c, '-')), DocCommitChoices.dashless(ht), hd), LA.dcw.and_r(Bool.not(Char.is_eq(d, '-')), DocCommitChoices.dashless(gt), gd), n2))
