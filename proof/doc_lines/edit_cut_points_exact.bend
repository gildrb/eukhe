# eukhe: the proof of LAW edit_cut_points_exact: the model's count and cut points step
# alike with the spec's, byte by byte

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

def ecp.lfs(bs: List<&2, Dl.B>) -> {Dl.lfs(bs) == DocLines.lines.Lfs(bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Dl.A{}:
          ecp.lfs(rest)
        case Dl.R{}:
          ecp.lfs(rest)
        case Dl.N{}:
          %ecp.lfs(rest) : {1n+Dl.lfs(rest) == 1n+_ : Nat}
          {==}

def ecp.upto(bs: List<&2, Dl.B>, n: Nat) -> {Dl.upto(bs, n) == DocLines.lines.Upto(bs, n) : List<&2, Dl.B>}:
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
              %ecp.upto(rest, 1n+m) : {Dl.A{} <> Dl.upto(rest, 1n+m) == Dl.A{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.R{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecp.upto(rest, 1n+m) : {Dl.R{} <> Dl.upto(rest, 1n+m) == Dl.R{} <> _ : List<&2, Dl.B>}
              {==}
        case Dl.N{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              %ecp.upto(rest, m) : {Dl.N{} <> Dl.upto(rest, m) == Dl.N{} <> _ : List<&2, Dl.B>}
              {==}

def ecp.from(bs: List<&2, Dl.B>, n: Nat) -> {Dl.from(bs, n) == DocLines.lines.From(bs, n) : List<&2, Dl.B>}:
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
              ecp.from(rest, 1n+m)
        case Dl.R{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              ecp.from(rest, 1n+m)
        case Dl.N{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              ecp.from(rest, m)

def DocLines.edit_cut_points_exact(bs, n):
  (ecp.lfs(bs), ecp.upto(bs, n), ecp.from(bs, n))
