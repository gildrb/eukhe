# eukhe: the proof of LAW edit_cut_points_split
#
# PROOF: byte by byte over the body. The two cut points take the bytes in
# turn, so put back together they are the body (any n). Before the n-th
# `\n` the first part takes every byte and counts each `\n`; at it, it
# stops with that `\n` last, so it holds n of them (n at most the body's
# count) and, unless n is 0 and it is empty, ends with a `\n`: a byte put
# before a part that holds a `\n` leaves its last byte alone.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./base.bend as LA

# the cut points put back together are the body
def ecs.app(bs: List<&2, Dl.B>, n: Nat) -> {List.append(&2, Dl.B, Dl.upto(bs, n), Dl.from(bs, n)) == bs : List<&2, Dl.B>}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Dl.A{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecs.app(rest, 1n+m) : {Dl.A{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), Dl.from(rest, 1n+m)) == Dl.A{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.R{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecs.app(rest, 1n+m) : {Dl.R{} <> List.append(&2, Dl.B, Dl.upto(rest, 1n+m), Dl.from(rest, 1n+m)) == Dl.R{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.N{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecs.app(rest, m) : {Dl.N{} <> List.append(&2, Dl.B, Dl.upto(rest, m), Dl.from(rest, m)) == Dl.N{} <> _ : List<&2, Dl.B>}
              {==}

# the first part holds n `\n` bytes
def ecs.count(bs: List<&2, Dl.B>, n: Nat, fits: {Nat.is_le(n, Dl.lfs(bs)) == True{} : Bool}) -> {Dl.lfs(Dl.upto(bs, n)) == n : Nat}:
  match bs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          LA.pdl.absurd({Dl.lfs(Dl.upto(Nil{}, 1n+m)) == 1n+m : Nat}, Equal.sym(Bool, False{}, True{}, fits))
    case b <> rest:
      match b:
        case Dl.A{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              ecs.count(rest, 1n+m, fits)
        case Dl.R{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              ecs.count(rest, 1n+m, fits)
        case Dl.N{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecs.count(rest, m, fits) : {1n+Dl.lfs(Dl.upto(rest, m)) == 1n+_ : Nat}
              {==}

def ecs.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      G

# 0 is no successor
def ecs.zero_succ(-G: Type, -m: Nat, e: {0n == 1n+m : Nat}) -> G:
  %e : ecs.NZ(_, G)
  Unit{}

# a byte put before a part that holds a `\n` leaves its last byte alone
def ecs.closed_cons(u: List<&2, Dl.B>, b: Dl.B, m: Nat, h: {Dl.lfs(u) == 1n+m : Nat}) -> {DocLines.lines.Closed(u) == DocLines.lines.Closed(b <> u) : Bool}:
  match u:
    case Nil{}:
      ecs.zero_succ({DocLines.lines.Closed(Nil{}) == DocLines.lines.Closed([b]) : Bool}, m, h)
    case c <> more:
      {==}

# the first part of no `\n` is empty
def ecs.upto0(bs: List<&2, Dl.B>) -> {Nil{} == Dl.upto(bs, 0n) : List<&2, Dl.B>}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Dl.A{}:
          {==}
        case Dl.R{}:
          {==}
        case Dl.N{}:
          {==}

# the first part is empty or ends with a `\n`
def ecs.closed(bs: List<&2, Dl.B>, n: Nat, fits: {Nat.is_le(n, Dl.lfs(bs)) == True{} : Bool}) -> {DocLines.lines.Closed(Dl.upto(bs, n)) == True{} : Bool}:
  match bs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          LA.pdl.absurd({DocLines.lines.Closed(Dl.upto(Nil{}, 1n+m)) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, fits))
    case b <> +rest:
      match b:
        case Dl.A{}:
          match n:
            case 0n:
              {==}
            case 1n++m:
              +f = fits
              %ecs.closed_cons(Dl.upto(rest, 1n+m), Dl.A{}, m, ecs.count(rest, 1n+m, f)) : {_ == True{} : Bool}
              ecs.closed(rest, 1n+m, f)
        case Dl.R{}:
          match n:
            case 0n:
              {==}
            case 1n++m:
              +f = fits
              %ecs.closed_cons(Dl.upto(rest, 1n+m), Dl.R{}, m, ecs.count(rest, 1n+m, f)) : {_ == True{} : Bool}
              ecs.closed(rest, 1n+m, f)
        case Dl.N{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              match m:
                case 0n:
                  %ecs.upto0(rest) : {DocLines.lines.Closed(Dl.N{} <> _) == True{} : Bool}
                  {==}
                case 1n++p:
                  +f = fits
                  %ecs.closed_cons(Dl.upto(rest, 1n+p), Dl.N{}, p, ecs.count(rest, 1n+p, f)) : {_ == True{} : Bool}
                  ecs.closed(rest, 1n+p, f)

def DocLines.edit_cut_points_split(bs, n, fits):
  +f = fits
  (ecs.app(bs, n), ecs.count(bs, n, f), ecs.closed(bs, n, f))
