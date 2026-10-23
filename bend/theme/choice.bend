# theme: the theme a name picks over the files read: candidates, clashes, the warning's cause, the broken files

import Base
import ./name.bend as TName

# The theme a name picks
# ----------------------
# Rust reads every theme file the sources reach (the registered files,
# then the custom directory's), in that order; `pick` decides the rest.

# a theme file the sources reach: a valid one, by the name it advertises,
# from the custom directory or not; or one that did not load, with the
# name it advertises (when it is a theme object) and its file stem (when
# that is text)
type Ld is Data:
  Fine{name: String, custom: Bool}
  Broke{name: Maybe<&2, String>, stem: Maybe<&2, String>}

# the candidate id of the file at index at: after the builtins
def file.id(at: Nat) -> U32:
  U32.from_nat(Nat.add(3n, at))

def same(a: Bool, +b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def cands.keep(keep: Bool, nm: String, +at: Nat, rest: List<&2, TName.Cand>) -> List<&2, TName.Cand>:
  match keep:
    case True{}:
      TName.Cand{nm, True{}, file.id(at)} <> rest
    case False{}:
      rest

def cands.of(l: Ld, +custom: Bool, +at: Nat, rest: List<&2, TName.Cand>) -> List<&2, TName.Cand>:
  match l:
    case Fine{nm, c}:
      cands.keep(same(c, custom), nm, at, rest)
    case Broke{nm, st}:
      rest

# the valid files of one source (custom or registered), in order, as
# candidates; the first is at index at
def cands(ls: List<&2, Ld>, +custom: Bool, +at: Nat) -> List<&2, TName.Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      cands.of(l, custom, at, cands(rest, custom, 1n+at))

# the theme name n resolves to over the files ls
def pick.res(+ls: List<&2, Ld>, +n: String) -> TName.Res:
  TName.resolve.name(TName.sources(cands(ls, False{}, 0n), cands(ls, True{}, 0n)), n)

# A valid file whose name an earlier valid file advertises clashes with
# the first of them (it is never picked). There are few theme files: a
# lookup per file is cheap.

type Clash is Data:
  Clash{at: Nat, winner: Nat}

def first.pick(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

def fine.named(l: Ld, +n: String) -> Bool:
  match l:
    case Fine{nm, c}:
      String.eq(nm, n)
    case Broke{nm, st}:
      False{}

# the index of the first valid file named n (the first is at index at)
def fine.first(ls: List<&2, Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      first.pick(fine.named(l, n), at, fine.first(rest, n, 1n+at))

def clash.if(same: Bool, w: Nat, at: Nat) -> Maybe<&2, Clash>:
  match same:
    case True{}:
      None{}
    case False{}:
      Some{Clash{at, w}}

def clash.of(m: Maybe<&2, Nat>, +at: Nat) -> Maybe<&2, Clash>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      clash.if(Nat.is_eq(w, at), w, at)

def clash.at(+all: List<&2, Ld>, l: Ld, +at: Nat) -> Maybe<&2, Clash>:
  match l:
    case Fine{+nm, c}:
      clash.of(fine.first(all, nm, 0n), at)
    case Broke{nm, st}:
      None{}

def clash.cons(m: Maybe<&2, Clash>, rest: List<&2, Clash>) -> List<&2, Clash>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def clashes.go(+all: List<&2, Ld>, ls: List<&2, Ld>, +at: Nat) -> List<&2, Clash>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      clash.cons(clash.at(all, l, at), clashes.go(all, rest, 1n+at))

# every clash, in file order
def clashes(+ls: List<&2, Ld>) -> List<&2, Clash>:
  clashes.go(ls, ls, 0n)

# A name that resolves to no theme warns, with its cause: the first file
# that did not load and advertises the name (or, when it is no theme
# object, is named after it), else none.

def blames.name(m: Maybe<&2, String>, st: Maybe<&2, String>, +n: String) -> Bool:
  match m:
    case Some{x}:
      String.eq(x, n)
    case None{}:
      match st:
        case Some{s}:
          String.eq(s, n)
        case None{}:
          False{}

def blames(l: Ld, +n: String) -> Bool:
  match l:
    case Fine{nm, c}:
      False{}
    case Broke{nm, st}:
      blames.name(nm, st, n)

def cause.go(ls: List<&2, Ld>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{l, rest}:
      first.pick(blames(l, n), at, cause.go(rest, n, 1n+at))

type Cause is Data:
  FailedAt{at: Nat}
  NoTheme{}

def cause.of(m: Maybe<&2, Nat>) -> Cause:
  match m:
    case None{}:
      NoTheme{}
    case Some{at}:
      FailedAt{at}

def skip.is(m: Maybe<&2, Nat>, +at: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, at)

def broken.keep(keep: Bool, at: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      at <> rest
    case False{}:
      rest

def broken.of(l: Ld, +skip: Maybe<&2, Nat>, +at: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Fine{nm, c}:
      rest
    case Broke{nm, st}:
      broken.keep(Bool.not(skip.is(skip, at)), at, rest)

# the files that did not load, in order, but the one at skip
def broken(ls: List<&2, Ld>, +skip: Maybe<&2, Nat>, +at: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      broken.of(l, skip, at, broken(rest, skip, 1n+at))

# what a name picks: the theme (the candidate id: 0..2 the builtins, 3 + i
# the file at index i), the cause of its warning (none when it does not
# warn), the clashes, and the other files that did not load (each warns)
type Pick is Data:
  Pick{res: TName.Res, cause: Maybe<&2, Cause>, clashes: List<&2, Clash>, broken: List<&2, Nat>}

def pick.warn(warned: Bool, id: U32, +ls: List<&2, Ld>, +n: String) -> Pick:
  match warned:
    case True{}:
      +m = cause.go(ls, n, 0n)
      Pick{TName.Res{id, True{}}, Some{cause.of(m)}, clashes(ls), broken(ls, m, 0n)}
    case False{}:
      Pick{TName.Res{id, False{}}, None{}, clashes(ls), broken(ls, None{}, 0n)}

def pick.go(r: TName.Res, +ls: List<&2, Ld>, +n: String) -> Pick:
  match r:
    case TName.Res{id, warned}:
      pick.warn(warned, id, ls, n)

# resolve name n over the files ls
def pick(+ls: List<&2, Ld>, +n: String) -> Pick:
  pick.go(pick.res(ls, n), ls, n)
