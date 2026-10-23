# eukhe: the laws of area doc_lines

import Base
import ../bend/doc_lines.bend as Dl
import ../bend/ffi_doc_lines.bend as Fdl
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F4) Lines and their endings
# ----------------------------
# bend/doc_lines.bend: every input is free: any body of bytes (content,
# `\r`, `\n` in any order), with or without a BOM; any edit that replaces
# any run of whole lines with any new lines.

# LAW: a file loaded and persisted with no edit is the same bytes: every
# line keeps its own ending, a lone `\r` stays content, the BOM stays
law load_persist_roundtrip:
  for +f: Dl.Doc
  {Dl.persist(Dl.load(f)) == f : Dl.Doc}

# LAW: an edit of the lines [s, s+k) keeps every byte outside them: the
# bytes of the lines before s, and the bytes after line s+k (its later
# lines with their own endings, and the last piece), are the same in the
# persisted file
law edit_keeps_untouched_bytes:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  for fits: {Nat.is_le(Nat.add(s, k), Dl.lfs(bs)) == True{} : Bool}
  exs x: List<&2, Dl.B>
  {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, x, Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}

# LAW: grep and read number the lines of a text the same way and show
# the same text for each line (a text that is not empty: grep shows no
# row of an empty text, read shows one empty row)
law grep_line_is_read_line:
  for +b: Dl.B
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}

# the n copies of x
def lines.Rep(-A: Data, n: Nat, +x: A) -> List<&2, A>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      x <> lines.Rep(A, m, x)

# the ending of the origin of each line, from its runs
def lines.Ends(rs: List<&2, Dl.Run>) -> List<&2, Maybe<&2, Dl.End>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Dl.Run{o, n}:
          List.append(&2, Maybe<&2, Dl.End>, lines.Rep(Maybe<&2, Dl.End>, n, o), lines.Ends(rest))

# the separator after each line, from its runs
def lines.Flat(ss: List<&2, Dl.Seps>) -> List<&2, Dl.End>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Dl.Seps{e, n}:
          List.append(&2, Dl.End, lines.Rep(Dl.End, n, e), lines.Flat(rest))

# the separator after each line: the ending of its origin, else the
# separator written before it (c before the first line)
def lines.Carry(ens: List<&2, Maybe<&2, Dl.End>>, +c: Dl.End) -> List<&2, Dl.End>:
  match ens:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case None{}:
          c <> lines.Carry(rest, c)
        case Some{+e}:
          e <> lines.Carry(rest, e)

def lines.Owns.go(rest: List<&2, Dl.Piece>, p: Dl.Piece) -> List<&2, Maybe<&2, Dl.End>>:
  match rest:
    case Nil{}:
      Nil{}
    case q <> more:
      match p:
        case Dl.Piece{t, en}:
          en <> lines.Owns.go(more, q)

# the own ending of each piece but the last
def lines.Owns(ps: List<&2, Dl.Piece>) -> List<&2, Maybe<&2, Dl.End>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      lines.Owns.go(rest, p)

def lines.Weave.go(rest: List<&2, Dl.Piece>, p: Dl.Piece, ss: List<&2, Dl.End>) -> List<&2, Dl.B>:
  match rest:
    case Nil{}:
      match p:
        case Dl.Piece{t, en}:
          t
    case q <> more:
      match p:
        case Dl.Piece{t, en}:
          match ss:
            case Nil{}:
              List.append(&2, Dl.B, t, lines.Weave.go(more, q, Nil{}))
            case s <> st:
              List.append(&2, Dl.B, t, List.append(&2, Dl.B, Dl.ebytes(s), lines.Weave.go(more, q, st)))

# the bytes of the pieces, each but the last followed by its separator
# from ss
def lines.Weave(ps: List<&2, Dl.Piece>, ss: List<&2, Dl.End>) -> List<&2, Dl.B>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      lines.Weave.go(rest, p, ss)

# LAW: persist writes each piece, and after each piece but the last the
# separator that the carry rule gives: its own ending, else the one
# written before it
# EXCLUDES: a persist whose separators follow another rule than the plan
# the Rust weaves with
law persist_weaves_carry:
  for +ps: List<&2, Dl.Piece>
  for +c: Dl.End
  {Dl.start(ps, c) == lines.Weave(ps, lines.Carry(lines.Owns(ps), c)) : List<&2, Dl.B>}

# LAW: the plan over runs gives, line for line, the separators of the
# carry rule
# EXCLUDES: a lost or doubled line in a run, a run that does not move the
# carry, an empty run that moves it, a new line that takes LF instead of
# the carry
# LEAVES FREE: where the answer splits its runs (Rust reads them line by
# line)
law persist_plan_refines:
  for +rs: List<&2, Dl.Run>
  for +c: Dl.End
  {lines.Flat(Dl.plan(rs, c)) == lines.Carry(lines.Ends(rs), c) : List<&2, Dl.End>}

# LAW anchor: two CRLF lines, three new lines (they take CRLF), an LF
# line, an empty run, a new line (it takes LF)
# EXCLUDES: new lines that take LF or the file's first ending
law persist_plan_example:
  {Dl.plan([Dl.Run{Some{Dl.CrLf{}}, 2n}, Dl.Run{None{}, 3n}, Dl.Run{Some{Dl.Lf{}}, 1n}, Dl.Run{Some{Dl.CrLf{}}, 0n}, Dl.Run{None{}, 1n}], Dl.Lf{}) == [Dl.Seps{Dl.CrLf{}, 2n}, Dl.Seps{Dl.CrLf{}, 3n}, Dl.Seps{Dl.Lf{}, 1n}, Dl.Seps{Dl.Lf{}, 1n}] : List<&2, Dl.Seps>}

# a run of lines fits the wire: its length does
def lines.RunFit(r: Dl.Run) -> Bool:
  match r:
    case Dl.Run{o, n}:
      LawsBase.wire_fits(n)

def lines.RunsFit(rs: List<&2, Dl.Run>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(lines.RunFit(r), lines.RunsFit(rest))

# every number of a request of the plan fits the wire
def lines.WireFits(+rs: List<&2, Dl.Run>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), lines.RunsFit(rs))

# LAW: the plan's entry of the compiled core answers, for every request
# whose numbers fit the wire, the encoding of the model's separators
# EXCLUDES: a codec that loses, reorders or misreads a run or the carry
law lines_entry_refines:
  for +rs: List<&2, Dl.Run>
  for +c: Dl.End
  for h: {lines.WireFits(rs) == True{} : Bool}
  {Fdl.ffi(Fdl.put_req(rs, c, "")) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}

# LAW anchor: an unknown ending tag answers the error form
# EXCLUDES: a default ending for a request the entry could not read
law lines_entry_rejects_example:
  {Fdl.ffi("0,2,") == Wr.err("doc_lines: malformed carry") : String}

# LAW witness: a request of the plan fits the wire (lines_entry_refines is
# not vacuous)
# EXCLUDES: a vacuous lines_entry_refines
law lines_wire_fits_example:
  {lines.WireFits([Dl.Run{Some{Dl.CrLf{}}, 3n}, Dl.Run{None{}, 1n}]) == True{} : Bool}
