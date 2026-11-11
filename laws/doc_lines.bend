# eukhe: the laws of area doc_lines
#
# Requirements (section F4 of the documents laws: the lines of a file and
# their endings; bend/doc_lines.bend, bend/ffi_doc_lines.bend; Rust
# crates/eukhe-docs text.rs, hashline/endings.rs, read/, grep/, write/):
# R1 a file loaded and persisted with no edit is the same bytes: every
#    line keeps its own ending, a lone `\r` stays content, the BOM stays.
# R2 an edit of the lines [s, s+k) (from 0) of a file (s + k at most its
#    count of `\n`) persists as the bytes up to its s-th `\n`, then each
#    new line, in order, followed by the ending written right before it
#    (the ending of line s-1; for s = 0 the file's first ending, LF when it
#    has none), then the bytes after its (s+k)-th `\n`; the BOM flag kept.
#    The count is the number of `\n` bytes; the cut points split the body
#    at its n-th `\n`.
# R3 an edited file whose lines own one ending only (LF, or CRLF; new
#    lines and the last line own none), persisted from that ending, has
#    that ending after every line but the last (the requirement: an edited
#    file keeps its detected ending).
# R4 the separators Rust persists an edit with (the plan over runs of
#    line origins) follow the carry rule: each line's own ending, else the
#    separator written before it; a run of no lines neither appears nor
#    moves the carry.
# R5 read's and grep's rows of a text: the text split on `\n`, each row
#    without the one `\r` right before its `\n`, a lone `\r` content, no row
#    after a final `\n`; read shows an empty text as one empty row, grep
#    as none; both number and show a nonempty text alike.
# R6 the carry of a loaded file (the `L` request over its projection) is
#    its first ending scanned byte by byte (CRLF when a `\r` comes right
#    before its first `\n`), LF when it has no `\n`.
# R7 a whole-file write (`W`) keeps the BOM of the file on disk and its
#    first ending (else LF) for every line, and warns exactly when both
#    texts have a `\n` and their first endings differ.
# R8 the entry answers each request Rust writes (bend/ffi_doc_lines.bend
#    header; every number within the wire) with the model's answer
#    spelled, reads exactly the request and nothing after it, and answers
#    any other input with the exact error form of its malformed part
#    (runs, carry, projection) or of input left over.
# Coverage: R1 load_persist_roundtrip; R2 edit_puts_new_lines,
# edit_keeps_untouched_bytes, edit_cut_points_split,
# edit_count_is_newlines; R3 persist_keeps_one_ending; R4
# persist_plan_refines, lines_entry_refines; R5 read_rows_exact,
# grep_rows_exact, grep_line_is_read_line; R6 lines_carry_is_first_end,
# lines_carry_is_first, load_holds_first_end; R7 lines_write_keeps; R8
# lines_entry_answers, lines_entry_exact, lines_entry_left_over_spelled,
# lines_entry_malformed_unless_carry, lines_entry_malformed_unless_load,
# lines_entry_malformed_unless_write, lines_entry_malformed_unless_runs.
# Anchors (no
# coverage): persist_plan_example, lines_entry_rejects_example,
# lines_entry_example, lines_entry_errors_example; witnesses:
# lines_wire_fits_example, lines_req_fits_example.

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

# LAW load_persist_roundtrip (R1): a file loaded and persisted with no edit is the same bytes: every
# line keeps its own ending, a lone `\r` stays content, the BOM stays
law load_persist_roundtrip:
  for +f: Dl.Doc
  {Dl.persist(Dl.load(f)) == f : Dl.Doc}

# LAW edit_keeps_untouched_bytes (R2): an edit of the lines [s, s+k) keeps every byte outside them: the
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

# LAW grep_line_is_read_line (R5): grep and read number the lines of a text the same way and show
# the same text for each line (a text that is not empty: grep shows no
# row of an empty text, read shows one empty row)
law grep_line_is_read_line:
  for +b: Dl.B
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}

# put b at the start of the first row
def lines.Push(b: Dl.B, rs: List<&2, List<&2, Dl.B>>) -> List<&2, List<&2, Dl.B>>:
  match rs:
    case Nil{}:
      [[b]]
    case r <> m:
      (b <> r) <> m

# the rows of the text `\r` <> c <> more, from rs, the rows of c <> more:
# before a `\n` the `\r` is part of that ending, else content of the first
# row
def lines.AfterR(c: Dl.B, rs: List<&2, List<&2, Dl.B>>) -> List<&2, List<&2, Dl.B>>:
  match c:
    case Dl.N{}:
      rs
    case Dl.A{}:
      lines.Push(Dl.R{}, rs)
    case Dl.R{}:
      lines.Push(Dl.R{}, rs)

# the rows of the text y <> t: the text split on `\n`; the one `\r` right
# before a `\n` is part of that ending, not of the row; any other `\r` is
# content; no row after a final `\n`
def lines.Rows(t: List<&2, Dl.B>, y: Dl.B) -> List<&2, List<&2, Dl.B>>:
  match t:
    case Nil{}:
      match y:
        case Dl.A{}:
          [[Dl.A{}]]
        case Dl.R{}:
          [[Dl.R{}]]
        case Dl.N{}:
          [[]]
    case +c <> more:
      match y:
        case Dl.A{}:
          lines.Push(Dl.A{}, lines.Rows(more, c))
        case Dl.N{}:
          Nil{} <> lines.Rows(more, c)
        case Dl.R{}:
          lines.AfterR(c, lines.Rows(more, c))

# read's rows of a text: an empty text is one empty row
def lines.ReadRows(bs: List<&2, Dl.B>) -> List<&2, List<&2, Dl.B>>:
  match bs:
    case Nil{}:
      [[]]
    case b <> rest:
      lines.Rows(rest, b)

# grep's rows of a text: an empty text has no row
def lines.GrepRows(bs: List<&2, Dl.B>) -> List<&2, List<&2, Dl.B>>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      lines.Rows(rest, b)

# LAW read_rows_exact (R5): read's rows of any text are the text split on `\n`,
# each row without the one `\r` right before its `\n`, a lone `\r` kept
# as content, no row after a final `\n`, an empty text one empty row
# EXCLUDES: read and grep changed alike (grep_line_is_read_line still
#   holds, the row lengths of rows_lines_are_read_rows still match): a
#   lone `\r` turned into other content, row bytes swapped or reordered,
#   both `\r` of a `\r\r\n` dropped, a lone `\r` taken as an ending
law read_rows_exact:
  for +bs: List<&2, Dl.B>
  {Dl.read_rows(bs) == lines.ReadRows(bs) : List<&2, List<&2, Dl.B>>}

# LAW grep_rows_exact (R5): grep's rows of any text are the text split on `\n`,
# each row without the one `\r` right before its `\n`, a lone `\r` kept
# as content, no row after a final `\n`, an empty text no row
# EXCLUDES: grep and read changed alike (grep_line_is_read_line still
#   holds): a lone `\r` turned into other content, row bytes swapped or
#   reordered, both `\r` of a `\r\r\n` dropped, the `\r` of a last
#   unterminated row dropped, a row shown for an empty text
law grep_rows_exact:
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(bs) == lines.GrepRows(bs) : List<&2, List<&2, Dl.B>>}

# the texts of the pieces of an edited file
def lines.Texts(ps: List<&2, Dl.Piece>) -> List<&2, List<&2, Dl.B>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          t <> lines.Texts(rest)

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

# LAW persist_plan_refines (R4): the plan over runs gives, line for line, the separators of the
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

# LAW persist_plan_example (anchor): two CRLF lines, three new lines (they take CRLF), an LF
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

# LAW lines_entry_refines (R4, R8): the plan's entry of the compiled core answers, for every request
# whose numbers fit the wire, the encoding of the model's separators
# EXCLUDES: a codec that loses, reorders or misreads a run or the carry
law lines_entry_refines:
  for +rs: List<&2, Dl.Run>
  for +c: Dl.End
  for h: {lines.WireFits(rs) == True{} : Bool}
  {Fdl.ffi(Fdl.put_req(rs, c, "")) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}

# LAW lines_entry_rejects_example (anchor): an unknown ending tag answers the error form
# EXCLUDES: a default ending for a request the entry could not read
law lines_entry_rejects_example:
  {Fdl.ffi("0,2,") == Wr.err("doc_lines: malformed carry") : String}

# LAW lines_wire_fits_example (witness): a request of the plan fits the wire (lines_entry_refines is
# not vacuous)
# EXCLUDES: a vacuous lines_entry_refines
law lines_wire_fits_example:
  {lines.WireFits([Dl.Run{Some{Dl.CrLf{}}, 3n}, Dl.Run{None{}, 1n}]) == True{} : Bool}

# (F4) The projection and the decisions over it
# ---------------------------------------------
# bend/doc_lines.bend `proj`, `carry`, `write`; bend/ffi_doc_lines.bend.
# Rust scans a file into its projection (the BOM flag, each line's length
# in chars and own ending); the entry decides on it. Every input is free:
# any file, any projection, any request text.

# the first ending of a body, scanned byte by byte (r: a `\r` came just
# before; None: the body has no `\n`)
def lines.FirstEnd(bs: List<&2, Dl.B>, r: Bool) -> Maybe<&2, Dl.End>:
  match bs:
    case Nil{}:
      None{}
    case b <> rest:
      match b:
        case Dl.A{}:
          lines.FirstEnd(rest, False{})
        case Dl.R{}:
          lines.FirstEnd(rest, True{})
        case Dl.N{}:
          match r:
            case True{}:
              Some{Dl.CrLf{}}
            case False{}:
              Some{Dl.Lf{}}

def lines.OrLf(m: Maybe<&2, Dl.End>) -> Dl.End:
  match m:
    case None{}:
      Dl.Lf{}
    case Some{e}:
      e

# both bodies hold a `\n` and their first endings differ
def lines.Warn.two(e: Dl.End, f: Dl.End) -> Bool:
  match e:
    case Dl.Lf{}:
      match f:
        case Dl.Lf{}:
          False{}
        case Dl.CrLf{}:
          True{}
    case Dl.CrLf{}:
      match f:
        case Dl.Lf{}:
          True{}
        case Dl.CrLf{}:
          False{}

# both bodies hold a `\n` and their first endings differ
def lines.Warn(k: Maybe<&2, Dl.End>, a: Maybe<&2, Dl.End>) -> Bool:
  match k:
    case None{}:
      False{}
    case Some{e}:
      match a:
        case None{}:
          False{}
        case Some{f}:
          lines.Warn.two(e, f)

# LAW lines_carry_is_first (R6): the carry the entry decides from a file's
# projection is the first ending persist starts from (the model's load)
# EXCLUDES: a carry read from another line than the first, LF for a CRLF
# file, a carry that ignores the projection
law lines_carry_is_first:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  {Dl.carry(Dl.proj(Dl.Doc{bom, bs})) == Dl.first(Dl.split(bs)) : Dl.End}

# LAW lines_carry_is_first_end (R6): the carry the entry decides from a file's projection is its
# first ending scanned byte by byte (a `\n`, CRLF when a `\r` comes right
# before it), LF when the file has no `\n`
# EXCLUDES: the carry of another line than the first (the last line's
#   ending), which lines_carry_is_first lets through when the model's own
#   load agrees with it
law lines_carry_is_first_end:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  {Dl.carry(Dl.proj(Dl.Doc{bom, bs})) == lines.OrLf(lines.FirstEnd(bs, False{})) : Dl.End}

def lines.EdHead(d: Dl.Ed) -> Bool & Dl.End:
  match d:
    case Dl.Ed{b, c, ps}:
      (b, c)

# LAW load_holds_first_end (R6): a loaded file holds its BOM flag and its
# first ending scanned byte by byte (LF when it has no `\n`), the carry
# persist starts from
# EXCLUDES: a load whose carry is not the file's first ending (LF for a
#   CRLF file, the last line's ending), so new lines at the top of the file
#   get another ending than the file's
law load_holds_first_end:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  {lines.EdHead(Dl.load(Dl.Doc{bom, bs})) == (bom, lines.OrLf(lines.FirstEnd(bs, False{}))) : Bool & Dl.End}

# LAW lines_write_keeps (R7): a whole-file write keeps the BOM of the file on
# disk and its first ending (LF when it has none) for every line, and
# warns exactly when both texts have a `\n` and their first endings differ
# EXCLUDES: the content's BOM or ending kept, a warning for a one-line
# text, a missing warning, a lone `\r` read as an ending
law lines_write_keeps:
  for +b1: Bool
  for +bs1: List<&2, Dl.B>
  for +b2: Bool
  for +bs2: List<&2, Dl.B>
  {Dl.write(Dl.proj(Dl.Doc{b1, bs1}), Dl.proj(Dl.Doc{b2, bs2})) == Dl.Kept{b1, lines.OrLf(lines.FirstEnd(bs1, False{})), lines.Warn(lines.FirstEnd(bs1, False{}), lines.FirstEnd(bs2, False{}))} : Dl.Kept}

# (F4) Edits, end to end
# ----------------------
# An edit of a loaded file, persisted: where it cuts the body, the bytes
# it keeps, and the ending each new line gets. Every input is free: any
# body, any BOM, any edit within the file, any new lines (any bytes).

# the bytes of an ending
def lines.EndBytes(e: Dl.End) -> List<&2, Dl.B>:
  match e:
    case Dl.Lf{}:
      [Dl.N{}]
    case Dl.CrLf{}:
      [Dl.R{}, Dl.N{}]

# the texts xs, each followed by the bytes e
def lines.Each(xs: List<&2, List<&2, Dl.B>>, +e: List<&2, Dl.B>) -> List<&2, Dl.B>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      List.append(&2, Dl.B, x, List.append(&2, Dl.B, e, lines.Each(rest, e)))

# the ending written right before line s (from 0) of the body bs: for
# s = 0 the body's first ending; else the ending of line s-1, the first
# ending after its (s-1)-th `\n`; LF when there is none
def lines.Before(bs: List<&2, Dl.B>, s: Nat) -> Dl.End:
  match s:
    case 0n:
      lines.OrLf(lines.FirstEnd(bs, False{}))
    case 1n+m:
      lines.OrLf(lines.FirstEnd(Dl.from(bs, m), False{}))

# LAW edit_count_is_newlines (R2): the count an edit's lines are checked
# against (Dl.lfs) is the number of `\n` bytes: it adds up over any two
# bodies put together, a `\n` counts 1, a content byte and a `\r` count 0
# (so it is the count of `\n` of every body)
# EXCLUDES: a count of bytes, of `\r\n` pairs, of lines (one more than the
#   `\n`), or a constant: edits past the end admitted, or edits of the
#   last lines refused (edit_keeps_untouched_bytes, edit_cut_points_split
#   and edit_puts_new_lines then say nothing about them)
law edit_count_is_newlines:
  for +a: List<&2, Dl.B>
  for +b: List<&2, Dl.B>
  {Dl.lfs(List.append(&2, Dl.B, a, b)) == Nat.add(Dl.lfs(a), Dl.lfs(b)) : Nat} & {[Dl.lfs([Dl.N{}]), Dl.lfs([Dl.A{}]), Dl.lfs([Dl.R{}])] == [1n, 0n, 0n] : List<&2, Nat>}

# the body u is empty or ends with a `\n`
def lines.Closed.go(rest: List<&2, Dl.B>, b: Dl.B) -> Bool:
  match rest:
    case Nil{}:
      match b:
        case Dl.N{}:
          True{}
        case Dl.A{}:
          False{}
        case Dl.R{}:
          False{}
    case c <> more:
      lines.Closed.go(more, c)

def lines.Closed(u: List<&2, Dl.B>) -> Bool:
  match u:
    case Nil{}:
      True{}
    case b <> rest:
      lines.Closed.go(rest, b)

# LAW edit_cut_points_split (R2): for any body bs and any n at most its
# count of `\n`, the cut points the edit laws name split bs at its n-th
# `\n`: Dl.upto(bs, n) then Dl.from(bs, n) is bs, the first part holds n
# `\n` bytes, and it is empty or ends with a `\n`. Only one split of bs
# has these three properties: the first n lines with their endings, then
# the bytes after them
# EXCLUDES: cut points that lose, double or move bytes, cut inside a line
#   or at another `\n` (an edit that keeps a line it replaces, or drops
#   the own ending of the line after it, then passes the edit laws)
law edit_cut_points_split:
  for +bs: List<&2, Dl.B>
  for +n: Nat
  for fits: {Nat.is_le(n, Dl.lfs(bs)) == True{} : Bool}
  {List.append(&2, Dl.B, Dl.upto(bs, n), Dl.from(bs, n)) == bs : List<&2, Dl.B>} & {Dl.lfs(Dl.upto(bs, n)) == n : Nat} & {lines.Closed(Dl.upto(bs, n)) == True{} : Bool}

# LAW edit_puts_new_lines (R2): an edit of the lines [s, s+k) of any file
# (any BOM, any body, s + k at most its count of `\n`) by any new lines
# persists as the bytes up to its s-th `\n`, then each new line, in order,
# followed by the ending written right before line s (the ending of line
# s-1; for s = 0 the file's first ending, LF when it has none), then the
# bytes after its (s+k)-th `\n`; the BOM flag kept
# EXCLUDES: new lines lost, doubled, reordered or changed; a new line with
#   no separator, or with LF in a CRLF file ("a\r\nb\r\n" with "x" put at
#   line 0 written "x\na\r\nb\r\n"); the separator taken from another line
#   (the last line's ending, the first ending for an edit further down);
#   a replaced line kept; a kept line's own ending changed; the BOM
#   dropped or flipped
law edit_puts_new_lines:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  for fits: {Nat.is_le(Nat.add(s, k), Dl.lfs(bs)) == True{} : Bool}
  {Dl.persist(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == Dl.Doc{bom, List.append(&2, Dl.B, Dl.upto(bs, s), List.append(&2, Dl.B, lines.Each(xs, lines.EndBytes(lines.Before(bs, s))), Dl.from(bs, Nat.add(s, k))))} : Dl.Doc}

# the endings a and b are one ending
def lines.SameEnd(a: Dl.End, b: Dl.End) -> Bool:
  match a b:
    case Dl.Lf{} Dl.Lf{}:
      True{}
    case Dl.Lf{} Dl.CrLf{}:
      False{}
    case Dl.CrLf{} Dl.Lf{}:
      False{}
    case Dl.CrLf{} Dl.CrLf{}:
      True{}

# every piece owns the ending e or none
def lines.Owned(ps: List<&2, Dl.Piece>, +e: Dl.End) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          match en:
            case None{}:
              lines.Owned(rest, e)
            case Some{f}:
              Bool.and(lines.SameEnd(f, e), lines.Owned(rest, e))

# LAW persist_keeps_one_ending (R3): an edited file whose pieces own only
# the ending e or none (kept lines of a file that ends every line with e,
# new lines, the last line), persisted with the carry e, is each line's
# text followed by e, but the last line's: its bytes followed by one more
# e are every text followed by e
# EXCLUDES: a CRLF file whose new or kept lines persist with LF (or an LF
#   file with CRLF); a separator lost, doubled, or written after the last
#   line; a line's text changed, lost or reordered
law persist_keeps_one_ending:
  for +p: Dl.Piece
  for +ps: List<&2, Dl.Piece>
  for +e: Dl.End
  for one: {lines.Owned(p <> ps, e) == True{} : Bool}
  {List.append(&2, Dl.B, Dl.start(p <> ps, e), lines.EndBytes(e)) == lines.Each(lines.Texts(p <> ps), lines.EndBytes(e)) : List<&2, Dl.B>}

# the requests of the entry
type lines.Req is Data:
  lines.Plan{runs: List<&2, Dl.Run>, carry: Dl.End}
  lines.Load{p: Dl.Proj}
  lines.Write{prev: Dl.Proj, next: Dl.Proj}

def lines.spell_run(r: Dl.Run, rest: String) -> String:
  match r:
    case Dl.Run{o, n}:
      LawsBase.proj_spell_mend(o, Wr.put_nat(n, rest))

def lines.spell_seps(x: Dl.Seps, rest: String) -> String:
  match x:
    case Dl.Seps{e, n}:
      LawsBase.proj_spell_end(e, Wr.put_nat(n, rest))

# the spelling of a request: a plan is its runs (count first) then its
# carry; `L` then a projection; `W` then two
def lines.spell_req(r: lines.Req) -> String:
  match r:
    case lines.Plan{rs, c}:
      Wr.put_list(~Dl.Run, ~lines.spell_run, rs, LawsBase.proj_spell_end(c, ""))
    case lines.Load{p}:
      SCon{'L', LawsBase.proj_spell(p, "")}
    case lines.Write{p, q}:
      SCon{'W', LawsBase.proj_spell(p, LawsBase.proj_spell(q, ""))}

def lines.spell_kept(k: Dl.Kept) -> String:
  match k:
    case Dl.Kept{b, e, w}:
      Wr.put_bool(b, LawsBase.proj_spell_end(e, Wr.put_bool(w, "")))

# the spelling of the model's answer: the separators of the plan, the
# carry, or what a write keeps (BOM, ending, warning)
def lines.answer(r: lines.Req) -> String:
  match r:
    case lines.Plan{rs, c}:
      Wr.put_list(~Dl.Seps, ~lines.spell_seps, Dl.plan(rs, c), "")
    case lines.Load{p}:
      LawsBase.proj_spell_end(Dl.carry(p), "")
    case lines.Write{p, q}:
      lines.spell_kept(Dl.write(p, q))

# every number of a request fits the wire
def lines.ReqFits(r: lines.Req) -> Bool:
  match r:
    case lines.Plan{rs, c}:
      lines.WireFits(rs)
    case lines.Load{p}:
      LawsBase.proj_fits(p)
    case lines.Write{p, q}:
      Bool.and(LawsBase.proj_fits(p), LawsBase.proj_fits(q))

# LAW lines_entry_answers (R8): the entry answers every request whose numbers
# fit the wire, spelled from the wire primitives, with the spelling of the
# model's decision
# EXCLUDES: a codec that loses, reorders or misreads a field (a run, an
# ending, a line's length or ending, the BOM, which projection is which),
# a reply of another decision or in another spelling
law lines_entry_answers:
  for +r: lines.Req
  for h: {lines.ReqFits(r) == True{} : Bool}
  {Fdl.ffi(lines.spell_req(r)) == lines.answer(r) : String}

# LAW lines_entry_exact (R8): every input the entry does not answer with the
# error form is the spelling of a request whose numbers fit
# EXCLUDES: a default answer to malformed input, an unknown tag or ending
# read as a known one, input left over ignored
law lines_entry_exact:
  for +s: String
  for h: {LawsBase.wire_opens_err(Fdl.ffi(s)) == False{} : Bool}
  exs r: lines.Req
  {s == lines.spell_req(r) : String} & {lines.ReqFits(r) == True{} : Bool}

# LAW lines_entry_example (anchor): the requests Rust writes, as text: a
# CRLF file of 3 chars and an empty last line (carry CRLF); a write of
# LF content over a BOM CRLF file (BOM and CRLF kept, a warning); a plan
# of 2 CRLF lines and a new one (it takes CRLF); an unknown request
# EXCLUDES: another spelling of the requests or replies Rust reads
law lines_entry_example:
  {[Fdl.ffi("LF2,3,1,1,0,0,"), Fdl.ffi("WT2,3,1,1,0,0,F2,1,1,0,0,0,"), Fdl.ffi("2,1,1,2,0,1,0,"), Fdl.ffi("X")] == ["1,", "T1,T", "2,1,2,1,1,", Wr.err("doc_lines: malformed runs")] : List<&2, String>}

# LAW lines_req_fits_example (witness): requests of each kind fit the
# wire (lines_entry_answers is not vacuous)
law lines_req_fits_example:
  {[lines.ReqFits(lines.Load{Dl.Proj{False{}, [Dl.Line{3n, Some{Dl.CrLf{}}}, Dl.Line{0n, None{}}]}}), lines.ReqFits(lines.Write{Dl.Proj{True{}, Nil{}}, Dl.Proj{False{}, [Dl.Line{1n, None{}}]}}), lines.ReqFits(lines.Plan{[Dl.Run{None{}, 2n}], Dl.Lf{}})] == [True{}, True{}, True{}] : List<&2, Bool>}

# The entry's errors
# ------------------
# Which input gets which error text. With lines_entry_answers and
# lines_entry_exact these laws pin every answer of the entry: a spelled
# request that fits answers the spelled decision, with input after it the
# left-over error; spelled runs then no spelled carry the carry's error;
# `L` or `W` then no spelled projection(s) the projection's error; any
# other input that does not open with spelled runs the runs' error.

# the spelling of a request, then rest (lines.spell_req is it with no rest)
def lines.spell_req_on(r: lines.Req, rest: String) -> String:
  match r:
    case lines.Plan{rs, c}:
      Wr.put_list(~Dl.Run, ~lines.spell_run, rs, LawsBase.proj_spell_end(c, rest))
    case lines.Load{p}:
      SCon{'L', LawsBase.proj_spell(p, rest)}
    case lines.Write{p, q}:
      SCon{'W', LawsBase.proj_spell(p, LawsBase.proj_spell(q, rest))}

# s opens with the mark of a load (`L`) or a write (`W`)
def lines.Marked(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      Bool.or(Char.is_eq(c, 'L'), Char.is_eq(c, 'W'))

# LAW lines_entry_left_over_spelled: a spelled request that fits (a plan, a
# load or a write), followed by any more input, answers the error form
# "doc_lines: input left over"
# EXCLUDES: trailing input ignored, read as part of the request, or named
#   as a malformed field
law lines_entry_left_over_spelled:
  for +r: lines.Req
  for fits: {lines.ReqFits(r) == True{} : Bool}
  for +c: Char
  for +rest: String
  {Fdl.ffi(lines.spell_req_on(r, SCon{c, rest})) == Wr.err("doc_lines: input left over") : String}

# LAW lines_entry_malformed_unless_carry: after spelled runs that fit, every
# answer but the error form "doc_lines: malformed carry" comes from input
# that goes on with a spelled ending (0 LF, 1 CRLF)
# EXCLUDES: an unknown or cut carry read as LF or CRLF (a default), named
#   as the runs' error or as input left over, the carry's error spelled
#   with another text
law lines_entry_malformed_unless_carry:
  for +rs: List<&2, Dl.Run>
  for fits: {lines.WireFits(rs) == True{} : Bool}
  for +t: String
  for other: {String.eq(Fdl.ffi(Wr.put_list(~Dl.Run, ~lines.spell_run, rs, t)), Wr.err("doc_lines: malformed carry")) == False{} : Bool}
  exs c: Dl.End
  exs rest: String
  {t == LawsBase.proj_spell_end(c, rest) : String}

# LAW lines_entry_malformed_unless_load: after `L`, every answer but the
# error form "doc_lines: malformed projection" comes from input that goes
# on with a spelled projection that fits
# EXCLUDES: a projection that does not read (an unknown ending tag, a cut
#   line, a short count, no BOM flag) answered with a carry or another
#   error, the projection's error spelled with another text
law lines_entry_malformed_unless_load:
  for +t: String
  for other: {String.eq(Fdl.ffi(SCon{'L', t}), Wr.err("doc_lines: malformed projection")) == False{} : Bool}
  exs p: Dl.Proj
  exs rest: String
  {t == LawsBase.proj_spell(p, rest) : String} & {LawsBase.proj_fits(p) == True{} : Bool}

# LAW lines_entry_malformed_unless_write: after `W`, every answer but the
# error form "doc_lines: malformed projection" comes from input that goes
# on with two spelled projections that fit
# EXCLUDES: either projection that does not read answered with a decision
#   or another error (the second one's error named as left-over input),
#   the projection's error spelled with another text
law lines_entry_malformed_unless_write:
  for +t: String
  for other: {String.eq(Fdl.ffi(SCon{'W', t}), Wr.err("doc_lines: malformed projection")) == False{} : Bool}
  exs p: Dl.Proj
  exs q: Dl.Proj
  exs rest: String
  {t == LawsBase.proj_spell(p, LawsBase.proj_spell(q, rest)) : String} & {Bool.and(LawsBase.proj_fits(p), LawsBase.proj_fits(q)) == True{} : Bool}

# LAW lines_entry_malformed_unless_runs: an input that does not open with
# `L` or `W` answers the error form "doc_lines: malformed runs" unless it
# begins with spelled runs that fit (a plan)
# EXCLUDES: input that is no request (empty, another mark, runs with an
#   unknown ending tag, a cut run) answered with a decision, the carry's or
#   another error, the runs' error spelled with another text
law lines_entry_malformed_unless_runs:
  for +s: String
  for plain: {lines.Marked(s) == False{} : Bool}
  for other: {String.eq(Fdl.ffi(s), Wr.err("doc_lines: malformed runs")) == False{} : Bool}
  exs rs: List<&2, Dl.Run>
  exs t: String
  {s == Wr.put_list(~Dl.Run, ~lines.spell_run, rs, t) : String} & {lines.WireFits(rs) == True{} : Bool}

# LAW lines_entry_errors_example (anchor): no input, and a run with an
# ending tag 2, answer the runs' error; runs with no carry the carry's; a
# plan with input after it, a load with input after it and a write with
# input after it the left-over error; `L` alone, a line with an ending tag
# 2, and a write with one projection the projection's error
# EXCLUDES: two error texts swapped, a field's error named as another
law lines_entry_errors_example:
  {[Fdl.ffi(""), Fdl.ffi("1,2,0,0,"), Fdl.ffi("0,"), Fdl.ffi("0,0,x"), Fdl.ffi("LF0,0,"), Fdl.ffi("WF0,F0,T"), Fdl.ffi("L"), Fdl.ffi("LF1,0,2,"), Fdl.ffi("WF0,")] == [Wr.err("doc_lines: malformed runs"), Wr.err("doc_lines: malformed runs"), Wr.err("doc_lines: malformed carry"), Wr.err("doc_lines: input left over"), Wr.err("doc_lines: input left over"), Wr.err("doc_lines: input left over"), Wr.err("doc_lines: malformed projection"), Wr.err("doc_lines: malformed projection"), Wr.err("doc_lines: malformed projection")] : List<&2, String>}

# the bytes after the n-th `\n` (none when there are fewer)
def lines.From(bs: List<&2, Dl.B>, n: Nat) -> List<&2, Dl.B>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Dl.N{}:
          match n:
            case 0n:
              Dl.N{} <> rest
            case 1n+m:
              lines.From(rest, m)
        case Dl.A{}:
          match n:
            case 0n:
              Dl.A{} <> rest
            case 1n+m:
              lines.From(rest, 1n+m)
        case Dl.R{}:
          match n:
            case 0n:
              Dl.R{} <> rest
            case 1n+m:
              lines.From(rest, 1n+m)

# the number of `\n` bytes
def lines.Lfs(bs: List<&2, Dl.B>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      match b:
        case Dl.N{}:
          Nat.add(1n, lines.Lfs(rest))
        case Dl.A{}:
          lines.Lfs(rest)
        case Dl.R{}:
          lines.Lfs(rest)

# the bytes up to and with the n-th `\n` (all of them when there are fewer)
def lines.Upto(bs: List<&2, Dl.B>, n: Nat) -> List<&2, Dl.B>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case Dl.N{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              Dl.N{} <> lines.Upto(rest, m)
        case Dl.A{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              Dl.A{} <> lines.Upto(rest, 1n+m)
        case Dl.R{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              Dl.R{} <> lines.Upto(rest, 1n+m)

# LAW edit_cut_points_exact: the count and the cut points edit_keeps_untouched_bytes names
# (Dl.lfs, Dl.upto, Dl.from) are the number of `\n` bytes, the bytes up to
# and with the n-th `\n`, and the bytes after it
# EXCLUDES: edit_keeps_untouched_bytes made vacuous by cut points that keep
#   nothing or a count that admits no edit (an edit that drops the own
#   endings of the lines after it then passes)
law edit_cut_points_exact:
  for +bs: List<&2, Dl.B>
  for +n: Nat
  {Dl.lfs(bs) == lines.Lfs(bs) : Nat} & {Dl.upto(bs, n) == lines.Upto(bs, n) : List<&2, Dl.B>} & {Dl.from(bs, n) == lines.From(bs, n) : List<&2, Dl.B>}

def lines.EdTexts(d: Dl.Ed) -> List<&2, List<&2, Dl.B>>:
  match d:
    case Dl.Ed{b, c, ps}:
      lines.Texts(ps)

# LAW edit_writes_new_lines: an edit of the lines [s, s+k) keeps the lines
# before s, then has exactly the new lines, in order, then the lines after
# s+k
# EXCLUDES: new lines lost, doubled, reordered or changed by the edit (the
# laws above pin the bytes outside the edit only)
law edit_writes_new_lines:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  {lines.EdTexts(Dl.edit(Dl.load(Dl.Doc{bom, bs}), s, k, xs)) == List.append(&2, List<&2, Dl.B>, List.take(&2, List<&2, Dl.B>, lines.Texts(Dl.pieces(Dl.split(bs))), s), List.append(&2, List<&2, Dl.B>, xs, List.drop(&2, List<&2, Dl.B>, lines.Texts(Dl.pieces(Dl.split(bs))), Nat.add(s, k)))) : List<&2, List<&2, Dl.B>>}

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

# LAW persist_weaves_carry: persist writes each piece, and after each piece but the last the
# separator that the carry rule gives: its own ending, else the one
# written before it
# EXCLUDES: a persist whose separators follow another rule than the plan
# the Rust weaves with
law persist_weaves_carry:
  for +ps: List<&2, Dl.Piece>
  for +c: Dl.End
  {Dl.start(ps, c) == lines.Weave(ps, lines.Carry(lines.Owns(ps), c)) : List<&2, Dl.B>}

# LAW persist_writes_with_carry: persist writes an edited file's BOM flag
# and its pieces woven with the carry rule from the file's first ending it
# holds (before the first new line: that ending)
# EXCLUDES: a persist that starts the carry from LF (or another ending)
#   instead of the file's first ending: lines put at the top of a CRLF
#   file written with LF ("a\r\nb\r\n" with "a" put at line 0 written
#   "a\na\r\nb\r\n"); a persist that drops or flips the BOM
law persist_writes_with_carry:
  for +b: Bool
  for +c: Dl.End
  for +ps: List<&2, Dl.Piece>
  {Dl.persist(Dl.Ed{b, c, ps}) == Dl.Doc{b, lines.Weave(ps, lines.Carry(lines.Owns(ps), c))} : Dl.Doc}

# new lines as pieces: each its text, with no ending of its own
def lines.Fresh(xs: List<&2, List<&2, Dl.B>>) -> List<&2, Dl.Piece>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Dl.Piece{x, None{}} <> lines.Fresh(rest)

# LAW edit_exact: an edit of the lines [s, s+k) keeps the BOM flag and the
# first ending of the file, the pieces before s and from s+k on, and puts
# the new lines in between as pieces with no ending of their own (they
# take the carry)
# EXCLUDES: an edit that changes the carry or the BOM, new lines that bring
#   an ending of their own (LF in a CRLF file), pieces lost or doubled
law edit_exact:
  for +b: Bool
  for +c: Dl.End
  for +ps: List<&2, Dl.Piece>
  for +s: Nat
  for +k: Nat
  for +xs: List<&2, List<&2, Dl.B>>
  {Dl.edit(Dl.Ed{b, c, ps}, s, k, xs) == Dl.Ed{b, c, List.append(&2, Dl.Piece, List.take(&2, Dl.Piece, ps, s), List.append(&2, Dl.Piece, lines.Fresh(xs), List.drop(&2, Dl.Piece, ps, Nat.add(s, k))))} : Dl.Ed}

def lines.sp_end.tag(r: Wr.Dec<Nat>) -> Wr.Dec<Dl.End>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{Dl.Lf{}, s}
        case 1n:
          Wr.Got{Dl.CrLf{}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# an ending: the tag 0 (LF) or 1 (CRLF)
def lines.sp_end(s: String) -> Wr.Dec<Dl.End>:
  lines.sp_end.tag(Wr.get_nat(s))

def lines.sp_mend.some(r: Wr.Dec<Dl.End>) -> Wr.Dec<Maybe<&2, Dl.End>>:
  match r:
    case Wr.Got{e, s}:
      Wr.Got{Some{e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def lines.sp_mend.tag(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Dl.End>>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{None{}, s}
        case 1n:
          lines.sp_mend.some(lines.sp_end(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# a Maybe<End>: the tag 0 (none), or 1 then an ending
def lines.sp_mend(s: String) -> Wr.Dec<Maybe<&2, Dl.End>>:
  lines.sp_mend.tag(Wr.get_nat(s))

def lines.sp_run.n(o: Maybe<&2, Dl.End>, r: Wr.Dec<Nat>) -> Wr.Dec<Dl.Run>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Dl.Run{o, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def lines.sp_run.end(r: Wr.Dec<Maybe<&2, Dl.End>>) -> Wr.Dec<Dl.Run>:
  match r:
    case Wr.Got{o, s}:
      lines.sp_run.n(o, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a run: its origin's ending (a Maybe<End>), then its count of lines
def lines.sp_run(s: String) -> Wr.Dec<Dl.Run>:
  lines.sp_run.end(lines.sp_mend(s))

# the first own ending among the lines of a projection (None: none has one)
def lines.sp_first(ls: List<&2, Dl.Line>) -> Maybe<&2, Dl.End>:
  match ls:
    case Nil{}:
      None{}
    case l <> rest:
      match l:
        case Dl.Line{n, en}:
          match en:
            case None{}:
              lines.sp_first(rest)
            case Some{e}:
              Some{e}

# the carry of a projection: its first ending, else LF
def lines.sp_carry(p: Dl.Proj) -> Dl.End:
  match p:
    case Dl.Proj{b, ls}:
      lines.OrLf(lines.sp_first(ls))

def lines.sp_load_done(p: Dl.Proj, whole: Bool) -> String:
  match whole:
    case True{}:
      LawsBase.proj_spell_end(lines.sp_carry(p), "")
    case False{}:
      Wr.err("doc_lines: input left over")

def lines.sp_load(r: Wr.Dec<Dl.Proj>) -> String:
  match r:
    case Wr.Got{p, s}:
      lines.sp_load_done(p, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("doc_lines: malformed projection")

def lines.sp_line.end(n: Nat, r: Wr.Dec<Maybe<&2, Dl.End>>) -> Wr.Dec<Dl.Line>:
  match r:
    case Wr.Got{o, s}:
      Wr.Got{Dl.Line{n, o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def lines.sp_line.len(r: Wr.Dec<Nat>) -> Wr.Dec<Dl.Line>:
  match r:
    case Wr.Got{n, s}:
      lines.sp_line.end(n, lines.sp_mend(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a line of a projection: its length, then its own ending (a Maybe<End>)
def lines.sp_line(s: String) -> Wr.Dec<Dl.Line>:
  lines.sp_line.len(Wr.get_nat(s))

def lines.sp_proj.lines(b: Bool, r: Wr.Dec<List<&2, Dl.Line>>) -> Wr.Dec<Dl.Proj>:
  match r:
    case Wr.Got{ls, s}:
      Wr.Got{Dl.Proj{b, ls}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def lines.sp_proj.bom(r: Wr.Dec<Bool>) -> Wr.Dec<Dl.Proj>:
  match r:
    case Wr.Got{b, s}:
      lines.sp_proj.lines(b, Wr.get_list(~Dl.Line, ~lines.sp_line, s))
    case Wr.Bad{}:
      Wr.Bad{}

# a projection: the BOM flag, then its lines
def lines.sp_proj(s: String) -> Wr.Dec<Dl.Proj>:
  lines.sp_proj.bom(Wr.get_bool(s))

# what a whole-file write of q over p keeps: p's BOM, p's first ending
# (else LF), and a warning when both have an ending and they differ
def lines.sp_kept(p: Dl.Proj, q: Dl.Proj) -> Dl.Kept:
  match p q:
    case Dl.Proj{b, +ls} Dl.Proj{c, ms}:
      Dl.Kept{b, lines.OrLf(lines.sp_first(ls)), lines.Warn(lines.sp_first(ls), lines.sp_first(ms))}

def lines.sp_write_done(p: Dl.Proj, q: Dl.Proj, whole: Bool) -> String:
  match whole:
    case True{}:
      lines.spell_kept(lines.sp_kept(p, q))
    case False{}:
      Wr.err("doc_lines: input left over")

def lines.sp_write_next(p: Dl.Proj, r: Wr.Dec<Dl.Proj>) -> String:
  match r:
    case Wr.Got{q, s}:
      lines.sp_write_done(p, q, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("doc_lines: malformed projection")

def lines.sp_write(r: Wr.Dec<Dl.Proj>) -> String:
  match r:
    case Wr.Got{p, s}:
      lines.sp_write_next(p, lines.sp_proj(s))
    case Wr.Bad{}:
      Wr.err("doc_lines: malformed projection")

def lines.sp_kind.pick(l: Bool, w: Bool, t: String) -> String:
  match l:
    case True{}:
      lines.sp_load(lines.sp_proj(t))
    case False{}:
      match w:
        case True{}:
          lines.sp_write(lines.sp_proj(t))
        case False{}:
          Wr.err("doc_lines: malformed runs")

# an input that is no plan: `L` (code 76) then a projection, or `W` (code
# 87) then two
def lines.sp_kind(s: String) -> String:
  match s:
    case SNil{}:
      Wr.err("doc_lines: malformed runs")
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          lines.sp_kind.pick(U32.is_eq(x, 76), U32.is_eq(x, 87), t)

# the separator after a line whose origin has the ending o, c the one
# before it: its own ending, else c
def lines.sp_sep(o: Maybe<&2, Dl.End>, c: Dl.End) -> Dl.End:
  match o:
    case None{}:
      c
    case Some{e}:
      e

# the separators of the runs rs, the carry c before them: one Seps per
# run that holds lines (an empty run neither appears nor moves the carry)
def lines.sp_plan(rs: List<&2, Dl.Run>, c: Dl.End) -> List<&2, Dl.Seps>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Dl.Run{o, n}:
          match n:
            case 0n:
              lines.sp_plan(rest, c)
            case 1n+m:
              +s = lines.sp_sep(o, c)
              Dl.Seps{s, 1n+m} <> lines.sp_plan(rest, s)

def lines.sp_plan_done(rs: List<&2, Dl.Run>, c: Dl.End, whole: Bool) -> String:
  match whole:
    case True{}:
      Wr.put_list(~Dl.Seps, ~lines.spell_seps, lines.sp_plan(rs, c), "")
    case False{}:
      Wr.err("doc_lines: input left over")

def lines.sp_plan_carry(rs: List<&2, Dl.Run>, r: Wr.Dec<Dl.End>) -> String:
  match r:
    case Wr.Got{c, s}:
      lines.sp_plan_done(rs, c, Wr.end(s))
    case Wr.Bad{}:
      Wr.err("doc_lines: malformed carry")

def lines.sp_runs(r: Wr.Dec<List<&2, Dl.Run>>, s: String) -> String:
  match r:
    case Wr.Got{rs, t}:
      lines.sp_plan_carry(rs, lines.sp_end(t))
    case Wr.Bad{}:
      lines.sp_kind(s)

# the entry's answer to the input s: a plan (its runs, then the carry),
# else a load or a write
def lines.sp_entry(+s: String) -> String:
  lines.sp_runs(Wr.get_list(~Dl.Run, ~lines.sp_run, s), s)

# LAW doc_lines_ffi_exact (compiled core): on every input the line-ending
# entry answers the spec: for a plan (runs, then the carry) the carry
# rule's separators, one per run that holds lines; for `L` and a
# projection its first own ending, else LF; for `W` and two projections
# the first one's BOM and first ending (else LF), and a warning exactly
# when both have an ending and they differ; for any projection, not only
# a file's; and exactly the error form of each malformed part (runs,
# carry, projection) or of input left over
# EXCLUDES: a separator other than the carry rule's, a run split, merged
#   or dropped otherwise, a carry or a kept ending from another line than
#   the first with one, a warning by another rule, a field misread, a
#   default for malformed input, input left over ignored, another error
#   text
law doc_lines_ffi_exact:
  for +s: String
  {Fdl.ffi(s) == lines.sp_entry(s) : String}
