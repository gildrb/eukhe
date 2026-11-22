# eukhe: the proof of LAW undo_touches_only_changed
#
# PROOF: by induction on the rows: a row's fix keeps it exactly when it is held or its two contents are the same (unt.cell, by cases; the code's blob equality is the spec's, LA.unb.nat_eq).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def unt.same_blob(x: Nat, y: Nat, q: Bool, e: {Nat.is_eq(x, y) == q : Bool}, fs: List<&2, U.Fix>) -> {Undo.sp_kept(U.fix.changed(Some{x}, Bool.not(q)) <> fs) == Undo.sp_nat_eq(x, y) <> Undo.sp_kept(fs) : List<&2, Bool>}:
  match q:
    case True{}:
      %Equal.sym(Bool, Undo.sp_nat_eq(x, y), True{}, Equal.trans(Bool, Undo.sp_nat_eq(x, y), Nat.is_eq(x, y), True{}, Equal.sym(Bool, Nat.is_eq(x, y), Undo.sp_nat_eq(x, y), LA.unb.nat_eq(x, y)), e)) : {Undo.sp_kept(U.fix.changed(Some{x}, Bool.not(True{})) <> fs) == _ <> Undo.sp_kept(fs) : List<&2, Bool>}
      {==}
    case False{}:
      %Equal.sym(Bool, Undo.sp_nat_eq(x, y), False{}, Equal.trans(Bool, Undo.sp_nat_eq(x, y), Nat.is_eq(x, y), False{}, Equal.sym(Bool, Nat.is_eq(x, y), Undo.sp_nat_eq(x, y), LA.unb.nat_eq(x, y)), e)) : {Undo.sp_kept(U.fix.changed(Some{x}, Bool.not(False{})) <> fs) == _ <> Undo.sp_kept(fs) : List<&2, Bool>}
      {==}

def unt.cell(h: Bool, b: Maybe<&2, Nat>, n: Maybe<&2, Nat>, fs: List<&2, U.Fix>) -> {Undo.sp_kept(U.fix(U.Row{b, n, h}) <> fs) == Bool.or(h, Undo.sp_same(b, n)) <> Undo.sp_kept(fs) : List<&2, Bool>}:
  match h:
    case True{}:
      match b:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case False{}:
      match b n:
        case None{} None{}:
          {==}
        case None{} Some{y}:
          {==}
        case Some{x} None{}:
          {==}
        case Some{+x} Some{+y}:
          unt.same_blob(x, y, Nat.is_eq(x, y), {==}, fs)

def unt.rows(rows: List<&2, U.Row>) -> {Undo.sp_kept(U.fixes(rows)) == Undo.sp_alone(rows) : List<&2, Bool>}:
  match rows:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case U.Row{+b, +n, +h}:
          %Equal.sym(List<&2, Bool>, Undo.sp_kept(U.fix(U.Row{b, n, h}) <> U.fixes(t)), Bool.or(h, Undo.sp_same(b, n)) <> Undo.sp_kept(U.fixes(t)), unt.cell(h, b, n, U.fixes(t))) : {_ == Undo.sp_alone(U.Row{b, n, h} <> t) : List<&2, Bool>}
          %Equal.sym(List<&2, Bool>, Undo.sp_kept(U.fixes(t)), Undo.sp_alone(t), unt.rows(t)) : {Bool.or(h, Undo.sp_same(b, n)) <> _ == Undo.sp_alone(U.Row{b, n, h} <> t) : List<&2, Bool>}
          {==}

def Undo.undo_touches_only_changed(rows):
  unt.rows(rows)
