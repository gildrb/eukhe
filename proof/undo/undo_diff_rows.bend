# eukhe: the proof of LAW undo_diff_rows
#
# PROOF: by induction on the rows: a held row is skipped, another one differs exactly when its fix changes it, which is exactly when its contents are not the same (unw.cell, by cases; LA.unb.nat_eq).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA


def unw.same_blob(x: Nat, y: Nat, q: Bool, e: {Nat.is_eq(x, y) == q : Bool}) -> {U.seen.of(U.fix.changed(Some{x}, Bool.not(q))) == Undo.sp_seen_of(Undo.sp_nat_eq(x, y)) : U.Seen}:
  match q:
    case True{}:
      %Equal.sym(Bool, Undo.sp_nat_eq(x, y), True{}, Equal.trans(Bool, Undo.sp_nat_eq(x, y), Nat.is_eq(x, y), True{}, Equal.sym(Bool, Nat.is_eq(x, y), Undo.sp_nat_eq(x, y), LA.unb.nat_eq(x, y)), e)) : {U.seen.of(U.fix.changed(Some{x}, Bool.not(True{}))) == Undo.sp_seen_of(_) : U.Seen}
      {==}
    case False{}:
      %Equal.sym(Bool, Undo.sp_nat_eq(x, y), False{}, Equal.trans(Bool, Undo.sp_nat_eq(x, y), Nat.is_eq(x, y), False{}, Equal.sym(Bool, Nat.is_eq(x, y), Undo.sp_nat_eq(x, y), LA.unb.nat_eq(x, y)), e)) : {U.seen.of(U.fix.changed(Some{x}, Bool.not(False{}))) == Undo.sp_seen_of(_) : U.Seen}
      {==}

def unw.cell(b: Maybe<&2, Nat>, n: Maybe<&2, Nat>) -> {U.seen(U.Row{b, n, False{}}) == Undo.sp_seen_of(Undo.sp_same(b, n)) : U.Seen}:
  match b n:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      unw.same_blob(x, y, Nat.is_eq(x, y), {==})

def unw.rows(rows: List<&2, U.Row>) -> {U.seens(rows) == Undo.sp_seens(rows) : List<&2, U.Seen>}:
  match rows:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case U.Row{b, n, h}:
          match h:
            case True{}:
              %Equal.sym(List<&2, U.Seen>, U.seens(t), Undo.sp_seens(t), unw.rows(t)) : {U.Skipped{} <> _ == U.Skipped{} <> Undo.sp_seens(t) : List<&2, U.Seen>}
              {==}
            case False{}:
              %Equal.sym(List<&2, U.Seen>, U.seens(t), Undo.sp_seens(t), unw.rows(t)) : {U.seen(U.Row{b, n, False{}}) <> _ == Undo.sp_seen_of(Undo.sp_same(b, n)) <> Undo.sp_seens(t) : List<&2, U.Seen>}
              %Equal.sym(U.Seen, U.seen(U.Row{b, n, False{}}), Undo.sp_seen_of(Undo.sp_same(b, n)), unw.cell(b, n)) : {_ <> Undo.sp_seens(t) == Undo.sp_seen_of(Undo.sp_same(b, n)) <> Undo.sp_seens(t) : List<&2, U.Seen>}
              {==}

def Undo.undo_diff_rows(rows):
  unw.rows(rows)
