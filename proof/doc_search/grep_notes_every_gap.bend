# eukhe: the proof of LAW grep_notes_every_gap

import Base
import ../../bend/doc_search.bend as Sr
import ../../LAWS.bend as Laws

# Grep: a notice for each class left out
# --------------------------------------

def ps.bump(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      1n+x
    case False{}:
      x

# the count of a notice after one more entry: one more when the notice
# reports the entry
def ps.count_step(c: Sr.Count, pa: Bool, x: Sr.Class, n: Sr.Note) -> {Sr.Note.count(Sr.Count.part(pa, Sr.Count.add(c, x)), n) == ps.bump(Sr.Note.cls(n, x, pa), Sr.Note.count(c, n)) : Nat}:
  match c:
    case Sr.Count{a, b, d, e, f, g, h, i, j, q}:
      match pa:
        case True{}:
          match x:
            case Sr.NoMatch{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Shown{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.PagedOut{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Unsearched{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Skipped{v}:
              match v:
                case Sr.Binary{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Unreadable{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Excluded{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Link{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Broken{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
        case False{}:
          match x:
            case Sr.NoMatch{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Shown{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.PagedOut{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Unsearched{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Skipped{v}:
              match v:
                case Sr.Binary{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Unreadable{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Excluded{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Link{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Broken{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}

def ps.count_zero(n: Sr.Note) -> {Sr.Note.count(Sr.Count.zero(), n) == 0n : Nat}:
  match n:
    case Sr.NSkip{w}:
      match w:
        case Sr.Binary{}:
          {==}
        case Sr.Unreadable{}:
          {==}
        case Sr.Excluded{}:
          {==}
        case Sr.Link{}:
          {==}
        case Sr.Broken{}:
          {==}
    case Sr.NPartial{}:
      {==}
    case Sr.NUnsearched{}:
      {==}

def ps.or_bump(b: Bool, +x: Nat) -> {Bool.or(b, Bool.not(Nat.is_eq(x, 0n))) == Bool.not(Nat.is_eq(ps.bump(b, x), 0n)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the law grep_notes_every_gap
def ps.notes_every_gap(os: List<&2, Sr.Out>, +n: Sr.Note) -> {Sr.noted(n, os) == Bool.not(Nat.is_eq(Sr.Note.count(Sr.account(os), n), 0n)) : Bool}:
  match os:
    case Nil{}:
      %Equal.sym(Nat, Sr.Note.count(Sr.Count.zero(), n), 0n, ps.count_zero(n)) : {False{} == Bool.not(Nat.is_eq(_, 0n)) : Bool}
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{i, +c, t, +pa}:
          +acc = Sr.account(rest)
          +b = Sr.Note.cls(n, c, pa)
          +x = Sr.Note.count(acc, n)
          +after = Sr.Note.count(Sr.Count.part(pa, Sr.Count.add(acc, c)), n)
          +ih = Equal.cong(Bool, Bool, y => Bool.or(b, y), Sr.noted(n, rest), Bool.not(Nat.is_eq(x, 0n)), ps.notes_every_gap(rest, n))
          +last = Equal.cong(Nat, Bool, y => Bool.not(Nat.is_eq(y, 0n)), ps.bump(b, x), after, Equal.sym(Nat, after, ps.bump(b, x), ps.count_step(acc, pa, c, n)))
          Equal.trans(Bool, Bool.or(b, Sr.noted(n, rest)), Bool.or(b, Bool.not(Nat.is_eq(x, 0n))), Bool.not(Nat.is_eq(after, 0n)), ih, Equal.trans(Bool, Bool.or(b, Bool.not(Nat.is_eq(x, 0n))), Bool.not(Nat.is_eq(ps.bump(b, x), 0n)), Bool.not(Nat.is_eq(after, 0n)), ps.or_bump(b, x), last))

def Laws.grep_notes_every_gap(os, t):
  ps.notes_every_gap(os, t)
