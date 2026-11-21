# eukhe: the proof of LAW undo_restores_rows
#
# PROOF: by induction on the rows: each row's fix carries out to the row's goal (unr.cell, by cases on held and the two contents; two blobs the code calls the same are equal, LA.unb.nat_eq_true), and the goal of a row list is the row's goal before the rest's (unr.goal_cons).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


# the content a row must have after /undo
def unr.goal(b: Maybe<&2, Nat>, n: Maybe<&2, Nat>, h: Bool) -> Maybe<&2, Nat>:
  match h:
    case True{}:
      n
    case False{}:
      b

def unr.goal_cons(b: Maybe<&2, Nat>, n: Maybe<&2, Nat>, h: Bool, t: List<&2, U.Row>) -> {Undo.sp_goal(U.Row{b, n, h} <> t) == unr.goal(b, n, h) <> Undo.sp_goal(t) : List<&2, Maybe<&2, Nat>>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def unr.same_blob(x: Nat, y: Nat, q: Bool, e: {Nat.is_eq(x, y) == q : Bool}) -> {Undo.sp_apply(U.Row{Some{x}, Some{y}, False{}}, U.fix.changed(Some{x}, Bool.not(q))) == Some{Some{x}} : Maybe<&2, Maybe<&2, Nat>>}:
  match q:
    case True{}:
      %LA.unb.nat_eq_true(x, y, e) : {Some{Some{_}} == Some{Some{x}} : Maybe<&2, Maybe<&2, Nat>>}
      {==}
    case False{}:
      {==}

def unr.cell(h: Bool, b: Maybe<&2, Nat>, n: Maybe<&2, Nat>) -> {Undo.sp_apply(U.Row{b, n, h}, U.fix(U.Row{b, n, h})) == Some{unr.goal(b, n, h)} : Maybe<&2, Maybe<&2, Nat>>}:
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
          unr.same_blob(x, y, Nat.is_eq(x, y), {==})

def unr.rows(rows: List<&2, U.Row>) -> {Undo.sp_after(rows, U.fixes(rows)) == Some{Undo.sp_goal(rows)} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}:
  match rows:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case U.Row{+b, +n, +h}:
          %Equal.sym(Maybe<&2, List<&2, Maybe<&2, Nat>>>, Undo.sp_after(t, U.fixes(t)), Some{Undo.sp_goal(t)}, unr.rows(t)) : {Undo.sp_after.cons(Undo.sp_apply(U.Row{b, n, h}, U.fix(U.Row{b, n, h})), _) == Some{Undo.sp_goal(U.Row{b, n, h} <> t)} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}
          %Equal.sym(Maybe<&2, Maybe<&2, Nat>>, Undo.sp_apply(U.Row{b, n, h}, U.fix(U.Row{b, n, h})), Some{unr.goal(b, n, h)}, unr.cell(h, b, n)) : {Undo.sp_after.cons(_, Some{Undo.sp_goal(t)}) == Some{Undo.sp_goal(U.Row{b, n, h} <> t)} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}
          %Equal.sym(List<&2, Maybe<&2, Nat>>, Undo.sp_goal(U.Row{b, n, h} <> t), unr.goal(b, n, h) <> Undo.sp_goal(t), unr.goal_cons(b, n, h, t)) : {Undo.sp_after.cons(Some{unr.goal(b, n, h)}, Some{Undo.sp_goal(t)}) == Some{_} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}
          {==}

def Undo.undo_restores_rows(rows):
  unr.rows(rows)
