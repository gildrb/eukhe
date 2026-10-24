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

# LAW load_persist_roundtrip: a file loaded and persisted with no edit is the same bytes: every
# line keeps its own ending, a lone `\r` stays content, the BOM stays
law load_persist_roundtrip:
  for +f: Dl.Doc
  {Dl.persist(Dl.load(f)) == f : Dl.Doc}

# LAW edit_keeps_untouched_bytes: an edit of the lines [s, s+k) keeps every byte outside them: the
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

# LAW grep_line_is_read_line: grep and read number the lines of a text the same way and show
# the same text for each line (a text that is not empty: grep shows no
# row of an empty text, read shows one empty row)
law grep_line_is_read_line:
  for +b: Dl.B
  for +bs: List<&2, Dl.B>
  {Dl.grep_rows(b <> bs) == Dl.read_rows(b <> bs) : List<&2, List<&2, Dl.B>>}

# the texts of the pieces of an edited file
def lines.Texts(ps: List<&2, Dl.Piece>) -> List<&2, List<&2, Dl.B>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      match p:
        case Dl.Piece{t, en}:
          t <> lines.Texts(rest)

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

# LAW persist_weaves_carry: persist writes each piece, and after each piece but the last the
# separator that the carry rule gives: its own ending, else the one
# written before it
# EXCLUDES: a persist whose separators follow another rule than the plan
# the Rust weaves with
law persist_weaves_carry:
  for +ps: List<&2, Dl.Piece>
  for +c: Dl.End
  {Dl.start(ps, c) == lines.Weave(ps, lines.Carry(lines.Owns(ps), c)) : List<&2, Dl.B>}

# LAW persist_plan_refines: the plan over runs gives, line for line, the separators of the
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

# LAW lines_entry_refines: the plan's entry of the compiled core answers, for every request
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

# LAW lines_carry_is_first: the carry the entry decides from a file's
# projection is the first ending persist starts from (the model's load)
# EXCLUDES: a carry read from another line than the first, LF for a CRLF
# file, a carry that ignores the projection
law lines_carry_is_first:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  {Dl.carry(Dl.proj(Dl.Doc{bom, bs})) == Dl.first(Dl.split(bs)) : Dl.End}

# LAW lines_carry_is_first_end: the carry the entry decides from a file's projection is its
# first ending scanned byte by byte (a `\n`, CRLF when a `\r` comes right
# before it), LF when the file has no `\n`
# EXCLUDES: the carry of another line than the first (the last line's
#   ending), which lines_carry_is_first lets through when the model's own
#   load agrees with it
law lines_carry_is_first_end:
  for +bom: Bool
  for +bs: List<&2, Dl.B>
  {Dl.carry(Dl.proj(Dl.Doc{bom, bs})) == lines.OrLf(lines.FirstEnd(bs, False{})) : Dl.End}

# LAW lines_write_keeps: a whole-file write keeps the BOM of the file on
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

# LAW lines_entry_answers: the entry answers every request whose numbers
# fit the wire, spelled from the wire primitives, with the spelling of the
# model's decision
# EXCLUDES: a codec that loses, reorders or misreads a field (a run, an
# ending, a line's length or ending, the BOM, which projection is which),
# a reply of another decision or in another spelling
law lines_entry_answers:
  for +r: lines.Req
  for h: {lines.ReqFits(r) == True{} : Bool}
  {Fdl.ffi(lines.spell_req(r)) == lines.answer(r) : String}

# LAW lines_entry_exact: every input the entry does not answer with the
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
