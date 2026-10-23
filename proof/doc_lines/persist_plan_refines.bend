# eukhe: the proof of LAW persist_plan_refines

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

# the carry rule over m more copies of o, after a first one
def pln.rep(m: Nat, +o: Maybe<&2, Dl.End>, +c: Dl.End, +xs: List<&2, Maybe<&2, Dl.End>>) -> {DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, m, o), xs), Dl.sep(o, c)) == List.append(&2, Dl.End, DocLines.lines.Rep(Dl.End, m, Dl.sep(o, c)), DocLines.lines.Carry(xs, Dl.sep(o, c))) : List<&2, Dl.End>}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      match o:
        case None{}:
          %pln.rep(k, None{}, c, xs) : {c <> DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, k, None{}), xs), c) == c <> _ : List<&2, Dl.End>}
          {==}
        case Some{+e}:
          %pln.rep(k, Some{e}, c, xs) : {e <> DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, k, Some{e}), xs), e) == e <> _ : List<&2, Dl.End>}
          {==}

# the carry rule over a run of 1+m copies of o
def pln.rep1(+m: Nat, o: Maybe<&2, Dl.End>, +c: Dl.End, +xs: List<&2, Maybe<&2, Dl.End>>) -> {DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, 1n+m, o), xs), c) == List.append(&2, Dl.End, DocLines.lines.Rep(Dl.End, 1n+m, Dl.sep(o, c)), DocLines.lines.Carry(xs, Dl.sep(o, c))) : List<&2, Dl.End>}:
  match o:
    case None{}:
      %pln.rep(m, None{}, c, xs) : {c <> DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, m, None{}), xs), c) == c <> _ : List<&2, Dl.End>}
      {==}
    case Some{+e}:
      %pln.rep(m, Some{e}, c, xs) : {e <> DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, m, Some{e}), xs), e) == e <> _ : List<&2, Dl.End>}
      {==}

def pln.plan(rs: List<&2, Dl.Run>, +c: Dl.End) -> {DocLines.lines.Flat(Dl.plan(rs, c)) == DocLines.lines.Carry(DocLines.lines.Ends(rs), c) : List<&2, Dl.End>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Dl.Run{+o, n}:
          match n:
            case 0n:
              pln.plan(rest, c)
            case 1n+(+m):
              +s = Dl.sep(o, c)
              %Equal.sym(List<&2, Dl.End>, DocLines.lines.Flat(Dl.plan(rest, s)), DocLines.lines.Carry(DocLines.lines.Ends(rest), s), pln.plan(rest, s)) : {List.append(&2, Dl.End, DocLines.lines.Rep(Dl.End, 1n+m, s), _) == DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, 1n+m, o), DocLines.lines.Ends(rest)), c) : List<&2, Dl.End>}
              Equal.sym(List<&2, Dl.End>, DocLines.lines.Carry(List.append(&2, Maybe<&2, Dl.End>, DocLines.lines.Rep(Maybe<&2, Dl.End>, 1n+m, o), DocLines.lines.Ends(rest)), c), List.append(&2, Dl.End, DocLines.lines.Rep(Dl.End, 1n+m, s), DocLines.lines.Carry(DocLines.lines.Ends(rest), s)), pln.rep1(m, o, c, DocLines.lines.Ends(rest)))

def DocLines.persist_plan_refines(rs, c):
  pln.plan(rs, c)
