# eukhe: the proof of LAW line_steps
# Induction on the tries, generalized over the calls made so far: driving
# the steps from a line with `made` calls behind it is `line.go` with
# `made` more calls. Each reply ends the line the way line.go ends it, or
# asks with one more call made and one try less (the induction hypothesis,
# shifted by one call).

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ../base/nat.bend as LNat

# a line with k more calls
def lsx.plus(k: Nat, o: C.Line) -> C.Line:
  match o:
    case C.Line{c, l}:
      C.Line{Nat.add(c, k), l}

def lsx.zero(o: C.Line) -> {lsx.plus(0n, o) == o : C.Line}:
  match o:
    case C.Line{c, l}:
      %LNat.add_zero(c) : {C.Line{Nat.add(c, 0n), l} == C.Line{_, l} : C.Line}
      {==}

def lsx.shift(-k: Nat, o: C.Line) -> {lsx.plus(1n+k, o) == lsx.plus(k, C.Line.more(o)) : C.Line}:
  match o:
    case C.Line{c, l}:
      %LNat.add_succ(c, k) : {C.Line{Nat.add(c, 1n+k), l} == C.Line{_, l} : C.Line}
      {==}

# a line that ended stays ended, whatever replies are left
def lsx.ends(rs: List<&2, C.Reply>, -c: Nat, -e: C.Fin, -node: Nat) -> {C.line.drive(rs, C.Ends{c, e}, node) == C.Line{c, C.Fin.line(node, e)} : C.Line}:
  match rs:
    case Nil{}:
      {==}
    case x <> y:
      {==}

# a reply of a text to a line with 1+p tries left: the step and line.go
# take the same end; an ask is the induction hypothesis ih
def lsx.says(fit: Bool, less: Bool, p: Nat, +made: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +input: List<&2, C.W>, +ws: List<&2, C.W>, +len: Nat, +rest: List<&2, C.Reply>,
  ih: {C.line.drive(rest, C.line.again(p, C.Lst{p, 1n+made, node, Some{ws}, len, input}), node) == lsx.plus(1n+made, C.line.go(p, node, Some{ws}, len, rest, input)) : C.Line})
  -> {C.line.drive(rest, C.line.says(fit, less, p, made, node, best, input, ws, len), node) == lsx.plus(made, C.line.next(fit, less, ws, node, best, input, C.line.go(p, node, Some{ws}, len, rest, input))) : C.Line}:
  match fit less:
    case True{} True{}:
      lsx.ends(rest, 1n+made, C.Whole{ws}, node)
    case True{} False{}:
      lsx.ends(rest, 1n+made, C.Whole{ws}, node)
    case False{} False{}:
      match best:
        case None{}:
          lsx.ends(rest, 1n+made, C.CutInput{input}, node)
        case Some{b}:
          lsx.ends(rest, 1n+made, C.CutBest{b}, node)
    case False{} True{}:
      match p:
        case 0n:
          lsx.ends(rest, 1n+made, C.CutReply{ws}, node)
        case 1n+q:
          Equal.trans(C.Line, C.line.drive(rest, C.Asks{C.Lst{1n+q, 1n+made, node, Some{ws}, len, input}}, node), lsx.plus(1n+made, C.line.go(1n+q, node, Some{ws}, len, rest, input)), lsx.plus(made, C.Line.more(C.line.go(1n+q, node, Some{ws}, len, rest, input))),
            ih, lsx.shift(made, C.line.go(1n+q, node, Some{ws}, len, rest, input)))

# an empty reply ends the line with the best reply, else the input, cut
def lsx.empty(p: Nat, +made: Nat, +node: Nat, best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rest: List<&2, C.Reply>, +input: List<&2, C.W>) -> {C.line.drive(C.Says{Nil{}} <> rest, C.line.again(1n+p, C.Lst{1n+p, made, node, best, bl, input}), node) == lsx.plus(made, C.line.go(1n+p, node, best, bl, C.Says{Nil{}} <> rest, input)) : C.Line}:
  match best:
    case None{}:
      lsx.ends(rest, 1n+made, C.CutInput{input}, node)
    case Some{b}:
      lsx.ends(rest, 1n+made, C.CutBest{b}, node)

def lsx.go(t: Nat, +made: Nat, +node: Nat, +best: Maybe<&2, List<&2, C.W>>, +bl: Nat, rs: List<&2, C.Reply>, +input: List<&2, C.W>) -> {C.line.drive(rs, C.line.again(t, C.Lst{t, made, node, best, bl, input}), node) == lsx.plus(made, C.line.go(t, node, best, bl, rs, input)) : C.Line}:
  match t:
    case 0n:
      match best:
        case None{}:
          lsx.ends(rs, made, C.CutInput{input}, node)
        case Some{b}:
          lsx.ends(rs, made, C.CutBest{b}, node)
    case 1n++p:
      match rs:
        case Nil{}:
          {==}
        case r <> +rest:
          match r:
            case C.Erred{}:
              lsx.ends(rest, 1n+made, C.Lost{}, node)
            case C.Says{ws}:
              match ws:
                case Nil{}:
                  lsx.empty(p, made, node, best, bl, rest, input)
                case +w <> +x:
                  +len = C.Text.len(w <> x)
                  lsx.says(Nat.is_le(len, node), C.shorter(len, best, bl), p, made, node, best, input, w <> x, len, rest,
                    lsx.go(p, 1n+made, node, Some{w <> x}, len, rest, input))

def Compactor.line_steps(tries, node, input, rs):
  Equal.trans(C.Line, C.line.drive(rs, C.line.open(tries, node, input), node), lsx.plus(0n, C.line(tries, node, input, rs)), C.line(tries, node, input, rs),
    lsx.go(tries, 0n, node, None{}, 0n, rs, input), lsx.zero(C.line(tries, node, input, rs)))
