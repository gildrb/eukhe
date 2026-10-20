# proof_runners: the lemmas PROOF.bend proves the (G4) laws with
# (laws/runners.bend), about the model in bend/runners.bend.

import Base
import ./runners.bend as Rn

# Logic
# -----

def pr.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pr.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pr.BD(_, A, Unit)
  Unit{}

def pr.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pr.BD(_, Unit, A)
  Unit{}

def pr.MD(m: Maybe<&2, Rn.Tool>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

def pr.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pr.absurdF({b == True{} : Bool}, h)

def pr.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pr.absurdF({False{} == True{} : Bool}, h)

def pr.and_f(a: Bool, +b: Bool, h: {b == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

# not a or b, and a: b
def pr.imp(a: Bool, +b: Bool, h: {Bool.or(Bool.not(a), b) == True{} : Bool}, ha: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pr.absurdF({b == True{} : Bool}, ha)

# The registry
# ------------

# every tool of a covered list that runs code is gated
def pr.cover(xs: List<&2, Rn.Tool>, i: Nat, +t: Rn.Tool, cov: {Rn.covered(xs) == True{} : Bool}, at: {List.get(&2, Rn.Tool, xs, i) == Some{t} : Maybe<&2, Rn.Tool>}, runs: {Rn.runs(t) == True{} : Bool}) -> {Rn.gated(t) == True{} : Bool}:
  match xs:
    case Nil{}:
      %at : pr.MD(_, Unit, {Rn.gated(t) == True{} : Bool})
      Unit{}
    case +x <> +rest:
      match i:
        case 0n:
          +same = Equal.cong(Maybe<&2, Rn.Tool>, Rn.Tool, m => Maybe.default(&2, Rn.Tool, m, t), Some{x}, Some{t}, at)
          %same : {Rn.gated(_) == True{} : Bool}
          pr.imp(Rn.runs(x), Rn.gated(x), pr.and_l(Bool.or(Bool.not(Rn.runs(x)), Rn.gated(x)), Rn.covered(rest), cov), Equal.trans(Bool, Rn.runs(x), Rn.runs(t), True{}, Equal.cong(Rn.Tool, Bool, s => Rn.runs(s), x, t, same), runs))
        case 1n+p:
          pr.cover(rest, p, t, pr.and_r(Bool.or(Bool.not(Rn.runs(x)), Rn.gated(x)), Rn.covered(rest), cov), at, runs)

def pr.covers(chat: Bool, i: Nat, +t: Rn.Tool, at: {List.get(&2, Rn.Tool, Rn.registry(chat), i) == Some{t} : Maybe<&2, Rn.Tool>}, runs: {Rn.runs(t) == True{} : Bool}) -> {Rn.gated(t) == True{} : Bool}:
  match chat:
    case True{}:
      pr.cover(Rn.registry(True{}), i, t, {==}, at, runs)
    case False{}:
      pr.cover(Rn.registry(False{}), i, t, {==}, at, runs)

def pr.ipython(chat: Bool) -> {Rn.find(Rn.registry(chat), "ipython") == Some{Rn.Tool{"ipython", [Rn.exec()], Rn.EachCall{}}} : Maybe<&2, Rn.Tool>}:
  match chat:
    case True{}:
      {==}
    case False{}:
      {==}

# The cell gate
# -------------

def pr.go_only(free: Bool, a: Rn.Asker, ran: {Rn.ran(Rn.cell.go(free, a)) == True{} : Bool}) -> {Bool.or(free, Rn.Asker.yes(a)) == True{} : Bool}:
  match free:
    case True{}:
      {==}
    case False{}:
      match a:
        case Rn.NoClient{}:
          pr.absurdF({False{} == True{} : Bool}, ran)
        case Rn.Silent{}:
          pr.absurdF({False{} == True{} : Bool}, ran)
        case Rn.Says{y}:
          match y:
            case True{}:
              {==}
            case False{}:
              pr.absurdF({False{} == True{} : Bool}, ran)

def pr.only(+caps: List<&2, Nat>, +auto: List<&2, Nat>, +a: Rn.Asker, ran: {Rn.ran(Rn.cell(caps, auto, a)) == True{} : Bool}) -> {Bool.or(Rn.within(caps, auto), Rn.Asker.yes(a)) == True{} : Bool}:
  pr.go_only(Rn.within(caps, auto), a, ran)

def pr.unasked(+caps: List<&2, Nat>, +auto: List<&2, Nat>, a: Rn.Asker, free: {Rn.within(caps, auto) == True{} : Bool}) -> {Rn.cell(caps, auto, a) == Rn.Out{False{}, Rn.Ran{Rn.Auto{}}} : Rn.Out}:
  %Equal.sym(Bool, Rn.within(caps, auto), True{}, free) : {Rn.cell.go(_, a) == Rn.Out{False{}, Rn.Ran{Rn.Auto{}}} : Rn.Out}
  {==}

def pr.approved(+caps: List<&2, Nat>, +auto: List<&2, Nat>, held: {Rn.within(caps, auto) == False{} : Bool}) -> {Rn.cell(caps, auto, Rn.Says{True{}}) == Rn.Out{True{}, Rn.Ran{Rn.Approved{}}} : Rn.Out}:
  %Equal.sym(Bool, Rn.within(caps, auto), False{}, held) : {Rn.cell.go(_, Rn.Says{True{}}) == Rn.Out{True{}, Rn.Ran{Rn.Approved{}}} : Rn.Out}
  {==}

def pr.no_yes(a: Rn.Asker, no: {Rn.Asker.yes(a) == False{} : Bool}) -> {Rn.ran(Rn.cell.go(False{}, a)) == False{} : Bool}:
  match a:
    case Rn.NoClient{}:
      {==}
    case Rn.Silent{}:
      {==}
    case Rn.Says{y}:
      match y:
        case True{}:
          pr.absurdT({True{} == False{} : Bool}, no)
        case False{}:
          {==}

def pr.stops(+caps: List<&2, Nat>, +auto: List<&2, Nat>, +a: Rn.Asker, held: {Rn.within(caps, auto) == False{} : Bool}, no: {Rn.Asker.yes(a) == False{} : Bool}) -> {Rn.ran(Rn.cell(caps, auto, a)) == False{} : Bool}:
  %Equal.sym(Bool, Rn.within(caps, auto), False{}, held) : {Rn.ran(Rn.cell.go(_, a)) == False{} : Bool}
  pr.no_yes(a, no)

# a cap list holding exec is not within an auto set without exec
def pr.exec_asks(caps: List<&2, Nat>, +auto: List<&2, Nat>, has: {Rn.elem(caps, Rn.exec()) == True{} : Bool}, lacks: {Rn.elem(auto, Rn.exec()) == False{} : Bool}) -> {Rn.within(caps, auto) == False{} : Bool}:
  match caps:
    case Nil{}:
      pr.absurdF({True{} == False{} : Bool}, has)
    case +c <> +rest:
      match c:
        case 0n:
          pr.and_f(Bool.and(Rn.grantable(0n), Rn.elem(auto, 0n)), Rn.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))
        case 1n+p:
          match p:
            case 0n:
              pr.and_f(Bool.and(Rn.grantable(1n), Rn.elem(auto, 1n)), Rn.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))
            case 1n+q:
              match q:
                case 0n:
                  %Equal.sym(Bool, Rn.elem(auto, 2n), False{}, lacks) : {Bool.and(Bool.and(True{}, _), Rn.within(rest, auto)) == False{} : Bool}
                  {==}
                case 1n+r:
                  pr.and_f(Bool.and(Rn.grantable(3n+r), Rn.elem(auto, 3n+r)), Rn.within(rest, auto), pr.exec_asks(rest, auto, has, lacks))
