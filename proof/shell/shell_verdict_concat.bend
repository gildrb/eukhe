# eukhe: the proof of LAW shell_verdict_concat
#
# PROOF: a verdict is a refusal exactly when some part writes an own path
# (svc.refused_of); some part of ps then qs does exactly when some part of
# ps does or some part of qs does (svc.mine_app, by induction on ps).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell

def svc.refused_of(b: Bool) -> {Shell.refused(Tl.verdict.of(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def svc.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def svc.mine_app(ps: List<&2, Tl.Piece>, +qs: List<&2, Tl.Piece>) -> {Tl.pieces.mine(List.append(&2, Tl.Piece, ps, qs)) == Bool.or(Tl.pieces.mine(ps), Tl.pieces.mine(qs)) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> +t:
      match p:
        case Tl.Piece{o, s, +m}:
          %Equal.sym(Bool, Tl.pieces.mine(List.append(&2, Tl.Piece, t, qs)), Bool.or(Tl.pieces.mine(t), Tl.pieces.mine(qs)), svc.mine_app(t, qs)) : {Bool.or(m, _) == Bool.or(Bool.or(m, Tl.pieces.mine(t)), Tl.pieces.mine(qs)) : Bool}
          svc.or_assoc(m, Tl.pieces.mine(t), Tl.pieces.mine(qs))

def svc.go(+ps: List<&2, Tl.Piece>, +qs: List<&2, Tl.Piece>) -> {Shell.refused(Tl.verdict(List.append(&2, Tl.Piece, ps, qs))) == Bool.or(Shell.refused(Tl.verdict(ps)), Shell.refused(Tl.verdict(qs))) : Bool}:
  +a = Tl.pieces.mine(List.append(&2, Tl.Piece, ps, qs))
  +b = Tl.pieces.mine(ps)
  +c = Tl.pieces.mine(qs)
  %Equal.sym(Bool, Shell.refused(Tl.verdict.of(a)), a, svc.refused_of(a)) : {_ == Bool.or(Shell.refused(Tl.verdict.of(b)), Shell.refused(Tl.verdict.of(c))) : Bool}
  %Equal.sym(Bool, Shell.refused(Tl.verdict.of(b)), b, svc.refused_of(b)) : {a == Bool.or(_, Shell.refused(Tl.verdict.of(c))) : Bool}
  %Equal.sym(Bool, Shell.refused(Tl.verdict.of(c)), c, svc.refused_of(c)) : {a == Bool.or(b, _) : Bool}
  svc.mine_app(ps, qs)

def Shell.shell_verdict_concat(ps, qs):
  svc.go(ps, qs)
