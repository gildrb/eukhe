# eukhe: the laws of area doc_rows
#
# Requirements (section F5 of the documents laws: what a read shows;
# bend/doc_rows.bend, bend/ffi_doc_rows.bend; Rust crates/eukhe-docs
# read/mod.rs, read/view.rs):
# R1 the lines a read numbers are the rows of the model's read (each
#    `\r\n` made `\n`, split on `\n`, no row after a final `\n`), in order
#    and length; a raw read counts every piece.
# R2 the spans, gap markers, notices and tag a read shows follow the read
#    rule of the section header below (window, ranges, past-the-end and
#    remain notices, a gap marker before every span that does not follow
#    the one before, no tag over the size limit or for a file that is not
#    UTF-8).
# R3 a read goes on exactly when it is raw, or the bytes are UTF-8 and the
#    sniffed head has no NUL (the requirement: a head with a NUL or not
#    UTF-8 is refused, `:raw` never is).
# R4 a refused read names its cause: a UTF-16 file (a UTF-16 BOM, bytes
#    not UTF-8) is named by its encoding even with the NUL bytes of its
#    ASCII, any other refused file with a NUL in its head is binary, a
#    refused file with no NUL is not UTF-8 (Rust read/tests.rs 114-130:
#    latin.txt not UTF-8, wide.txt UTF-16 (little endian); read/tests.rs
#    214: a file with a NUL is binary).
# R5 the entry answers each request Rust writes (bend/ffi_doc_rows.bend
#    header; every number within the wire) with the model's answer
#    spelled, reads exactly the request and nothing after it, and answers
#    any other input with exactly one of its two error forms.
# Coverage: R1 rows_lines_are_read_rows, rows_raw_lines_are_pieces; R2
# rows_view_shows, rows_gap_marks_every_jump; R3 rows_gate_goes_as_required; R4
# rows_gate_names_the_refusal; R5 rows_entry_answers, rows_entry_exact,
# rows_entry_left_over_spelled, rows_entry_malformed_unless_request,
# rows_entry_left_over, rows_entry_left_over_exact, rows_entry_errors.
# Anchors (no coverage): rows_view_example, rows_gap_example,
# rows_entry_errors_example_spec, rows_entry_example,
# rows_entry_errors_example; witness: rows_req_fits_example.

import Base
import ../bend/doc_lines.bend as Dl
import ../bend/doc_rows.bend as Dr
import ../bend/ffi_doc_rows.bend as Fdr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F5) What a read shows
# ----------------------
# bend/doc_rows.bend `gate`, `view`; bend/ffi_doc_rows.bend. Rust reads
# the bytes, scans them into their projection (bend/doc_lines.bend
# `proj`) and writes the rows of the lines the entry shows. Every input is
# free: any file, any selector (ranges in any order, any numbers), any
# facts about the bytes, any request text.
# The lines read numbers: the pieces of the file, but the empty piece
# after a final `\n` is no line; a raw read counts every piece. A window
# (no selector or one range) shows from its start (and the line before it
# when the start is past line 1) to its end (and 3 lines after it when it
# has an end), cut at the end of the file; a range with an end that stops
# before the last line gets the notice of the lines that remain; a window
# that starts past the end shows nothing and gets its notice. Ranges (two
# or more) show each range cut at the end of the file, drop a range that
# starts past the end with its notice, and put a gap marker before a span
# that does not follow the one before (raw: before every span but the
# first). A file over the size limit gets no tag and its notice; a file
# that is not UTF-8 gets no tag. A read that is not raw refuses a file
# that is not UTF-8 (a UTF-16 BOM, or no NUL in the sniffed head) and then
# a binary one (a NUL in the sniffed head).
# NOT PINNED here: the row text (Rust copies line i of the file); the
# notice wording.

# the lengths of lines and of byte lists
def rows.Lens(ls: List<&2, Dl.Line>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      match l:
        case Dl.Line{n, en}:
          n <> rows.Lens(rest)

def rows.LensB(xs: List<&2, List<&2, Dl.B>>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      List.length(&2, Dl.B, x) <> rows.LensB(rest)

def rows.Empty(l: Dl.Line) -> Bool:
  match l:
    case Dl.Line{n, en}:
      Nat.is_eq(n, 0n)

# the last line is empty
def rows.LastEmpty(ls: List<&2, Dl.Line>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> rest:
      match rest:
        case Nil{}:
          rows.Empty(l)
        case m <> more:
          rows.LastEmpty(m <> more)

def rows.If(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

def rows.Pick(-A: Type, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

# the lines read numbers: every piece but an empty last one after another
def rows.Count(+ls: List<&2, Dl.Line>) -> Nat:
  +n = List.length(&2, Dl.Line, ls)
  rows.If(Nat, Bool.and(Nat.is_le(2n, n), rows.LastEmpty(ls)), Nat.sub(n, 1n), n)

# the lines of a file, as Rust's scan sees them
def rows.Pieces(bs: List<&2, Dl.B>) -> List<&2, Dl.Line>:
  Dl.proj.lines(Dl.pieces(Dl.split(bs)))

# LAW rows_lines_are_read_rows (R1): the lines a read numbers are, in order and
# length, the rows of the model's read (each `\r\n` made `\n`, split on
# `\n`, no row after a final `\n`): Rust's row i is line i of its scan
# EXCLUDES: a lost or extra last row, a row that keeps the `\r` of a
# `\r\n`, a lone `\r` taken as an ending, rows shifted by one
law rows_lines_are_read_rows:
  for +bs: List<&2, Dl.B>
  {rows.Lens(List.take(&2, Dl.Line, rows.Pieces(bs), rows.Count(rows.Pieces(bs)))) == rows.LensB(Dl.read_rows(bs)) : List<&2, Nat>}

# LAW rows_raw_lines_are_pieces (R1): the lines a raw read counts are the
# pieces of the text with each `\r\n` made `\n`, split on `\n`
# EXCLUDES: a raw read that drops the empty piece after a final `\n`
law rows_raw_lines_are_pieces:
  for +bs: List<&2, Dl.B>
  {rows.Lens(rows.Pieces(bs)) == rows.LensB(Dl.splitN(Dl.norm(bs))) : List<&2, Nat>}

# Gate
# ----

# the gate lets the read go on
def rows.Goes(g: Dr.Gate) -> Bool:
  match g:
    case Dr.Go{}:
      True{}
    case Dr.NotUtf8{}:
      False{}
    case Dr.Binary{}:
      False{}

# the gate refuses the read as binary
def rows.IsBinary(g: Dr.Gate) -> Bool:
  match g:
    case Dr.Go{}:
      False{}
    case Dr.NotUtf8{}:
      False{}
    case Dr.Binary{}:
      True{}

# LAW rows_gate_goes_as_required (R3): for any facts about a read (raw or not,
# the bytes UTF-8 or not, a UTF-16 BOM or not, a NUL in the sniffed head
# or not) it goes on exactly when it is raw, or the bytes are UTF-8 and
# the head has no NUL (the requirement's read: binary is a NUL in the head
# or bytes that are not UTF-8; `:raw` reads every file)
# EXCLUDES: a raw read refused; a file with a NUL, or one that is not
#   UTF-8 (UTF-16, Latin-1), shown as text; a UTF-8 file with no NUL
#   refused
law rows_gate_goes_as_required:
  for +raw: Bool
  for +utf8: Bool
  for +utf16: Bool
  for +nul: Bool
  {rows.Goes(Dr.gate(raw, utf8, utf16, nul)) == Bool.or(raw, Bool.and(utf8, Bool.not(nul))) : Bool}

# LAW rows_gate_names_the_refusal (R4): for any facts about a read that
# does not go on, it is refused as binary exactly when the head has a NUL
# and the file is not UTF-16 text (a UTF-16 BOM and bytes that are not
# UTF-8); else it is refused as not UTF-8
# EXCLUDES: a UTF-16 file (its ASCII has NUL bytes) called binary; a
#   UTF-8 or Latin-1 file with a NUL called not UTF-8; a Latin-1 file
#   with no NUL called binary
law rows_gate_names_the_refusal:
  for +raw: Bool
  for +utf8: Bool
  for +utf16: Bool
  for +nul: Bool
  for refused: {rows.Goes(Dr.gate(raw, utf8, utf16, nul)) == False{} : Bool}
  {rows.IsBinary(Dr.gate(raw, utf8, utf16, nul)) == Bool.and(nul, Bool.not(Bool.and(utf16, Bool.not(utf8)))) : Bool}

# View
# ----

def rows.Span(+f: Nat, +l: Nat) -> List<&2, Dr.Span>:
  rows.If(List<&2, Dr.Span>, Nat.is_le(f, l), [Dr.Span{f, l, False{}}], Nil{})

# the first line a window shows: the line before f too when not raw and
# f is past line 1
def rows.Window.first(+raw: Bool, +f: Nat) -> Nat:
  rows.If(Nat, Bool.and(Bool.not(raw), Nat.is_lt(1n, f)), Nat.sub(f, 1n), f)

# a window that ends at line want (an explicit end), from line sf
def rows.Window.ends(raw: Bool, +sf: Nat, +want: Nat, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match raw:
    case True{}:
      (rows.Span(sf, want), Nil{})
    case False{}:
      +sl = Nat.min(Nat.add(want, 3n), t)
      (rows.Span(sf, sl), rows.If(List<&2, Dr.Note>, Nat.is_lt(sl, t), [Dr.Remain{Nat.sub(t, sl), Nat.add(sl, 1n)}], Nil{}))

# a window of a file of t lines from line f (st as asked; m: its end,
# None: to the end of the file)
def rows.Window.in(+raw: Bool, +f: Nat, m: Maybe<&2, Nat>, +st: Nat, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match m:
    case None{}:
      (rows.Span(rows.Window.first(raw, f), t), Nil{})
    case Some{+en}:
      rows.Window.ends(raw, rows.Window.first(raw, f), Nat.min(Nat.add(f, Nat.sub(en, st)), t), t)

def rows.Window(+raw: Bool, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  +f = Nat.max(st, 1n)
  rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, Nat.is_lt(t, f), (Nil{}, [Dr.Beyond{f}]), rows.Window.in(raw, f, m, st, t))

def rows.Ranges.step(+raw: Bool, +prev: Maybe<&2, Nat>, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat, r: List<&2, Dr.Span> & List<&2, Dr.Note>) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match r:
    case (+sp, +ns):
      +en = Maybe.default(&2, Nat, m, t)
      +last = Nat.min(en, t)
      +gap = Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st))))
      rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, Nat.is_lt(t, st), (sp, Dr.RangeBeyond{st, m} <> ns), (Dr.Span{st, last, gap} <> sp, ns))

# the end of the span a range shows (None: it starts past the end)
def rows.Ranges.end(+st: Nat, m: Maybe<&2, Nat>, +t: Nat) -> Maybe<&2, Nat>:
  rows.If(Maybe<&2, Nat>, Nat.is_lt(t, st), None{}, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)})

# ranges in order; prev: the end of the last span shown before
def rows.Ranges(xs: List<&2, Dr.Range>, +raw: Bool, +prev: Maybe<&2, Nat>, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case x <> rest:
      match x:
        case Dr.Range{+st, +m}:
          rows.Ranges.step(raw, prev, st, m, t, rows.Ranges(rest, raw, Maybe.or(&2, Nat, rows.Ranges.end(st, m, t), prev), t))

def rows.Window.of(+raw: Bool, x: Dr.Range, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match x:
    case Dr.Range{st, m}:
      rows.Window(raw, st, m, t)

def rows.Shown(s: Dr.Sel, +t: Nat) -> List<&2, Dr.Span> & List<&2, Dr.Note>:
  match s:
    case Dr.Whole{}:
      rows.Window(False{}, 1n, None{}, t)
    case Dr.Raw{}:
      (rows.Span(1n, t), Nil{})
    case Dr.Lines{xs, raw}:
      match xs:
        case Nil{}:
          rows.Window(raw, 1n, None{}, t)
        case x <> rest:
          match rest:
            case Nil{}:
              rows.Window.of(raw, x, t)
            case y <> more:
              rows.Ranges(x <> y <> more, raw, None{}, t)

def rows.Raw(s: Dr.Sel) -> Bool:
  match s:
    case Dr.Whole{}:
      False{}
    case Dr.Raw{}:
      True{}
    case Dr.Lines{xs, raw}:
      raw

def rows.View.fin(+t: Nat, raw: Bool, utf8: Bool, +over: Bool, r: List<&2, Dr.Span> & List<&2, Dr.Note>) -> Dr.View:
  match r:
    case (sp, +ns):
      Dr.View{t, raw, sp, rows.If(List<&2, Dr.Note>, over, List.append(&2, Dr.Note, ns, [Dr.TooBig{}]), ns), Bool.and(Bool.not(over), utf8)}

# what a read shows of a file whose lines are ls
def rows.View(+s: Dr.Sel, utf8: Bool, over: Bool, +ls: List<&2, Dl.Line>) -> Dr.View:
  +raw = rows.Raw(s)
  +t = rows.If(Nat, raw, List.length(&2, Dl.Line, ls), rows.Count(ls))
  rows.View.fin(t, raw, utf8, over, rows.Shown(s, t))

# LAW rows_view_shows (R2): what the entry decides a read shows is the read
# rule: the lines it counts, the spans with their context and gap
# markers, the notices in order, and the tag
# EXCLUDES: a lost or doubled context line, context on a raw read, a span
# past the end of the file, a missing or extra notice, a tag on a file
# over the limit or not UTF-8, ranges reordered or merged, a gap marker
# between adjacent spans
law rows_view_shows:
  for +s: Dr.Sel
  for +utf8: Bool
  for +over: Bool
  for b: Bool
  for +ls: List<&2, Dl.Line>
  {Dr.view(s, utf8, over, Dl.Proj{b, ls}) == rows.View(s, utf8, over, ls) : Dr.View}

# LAW rows_view_example (anchor): a 9-line file with a final `\n` read at
# 4-5 shows lines 3-8 and the notice of line 9; read at 12 it shows
# nothing; ranges 2-3, 5-, 20-30 show 2-3, a gap, 5-9, and the notice of
# 20-30
# EXCLUDES: off-by-one context or remain counts
law rows_view_example:
  for b: Bool
  {[Dr.view(Dr.Lines{[Dr.Range{4n, Some{5n}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]}), Dr.view(Dr.Lines{[Dr.Range{12n, None{}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]}), Dr.view(Dr.Lines{[Dr.Range{2n, Some{3n}}, Dr.Range{5n, None{}}, Dr.Range{20n, Some{30n}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]})] == [Dr.View{9n, False{}, [Dr.Span{3n, 8n, False{}}], [Dr.Remain{1n, 9n}], True{}}, Dr.View{1n, False{}, Nil{}, [Dr.Beyond{12n}], True{}}, Dr.View{9n, False{}, [Dr.Span{2n, 3n, False{}}, Dr.Span{5n, 9n, True{}}], [Dr.RangeBeyond{20n, Some{30n}}], True{}}] : List<&2, Dr.View>}

# the gap marker a span after the span that ended at prev (None: the
# first span) gets: none for the first; else one when the read is raw or
# the span does not start right after line prev
def rows.Marked(raw: Bool, prev: Maybe<&2, Nat>, s: Nat) -> Bool:
  match prev:
    case None{}:
      False{}
    case Some{pe}:
      Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(pe, 1n), s)))

def rows.Same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# every span of sps, after the span that ended at prev, has exactly the
# gap marker rows.Marked gives it
def rows.Marks(sps: List<&2, Dr.Span>, +raw: Bool, prev: Maybe<&2, Nat>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case x <> rest:
      match x:
        case Dr.Span{s, e, g}:
          Bool.and(rows.Same(g, rows.Marked(raw, prev, s)), rows.Marks(rest, raw, Some{e}))

def rows.Spans(v: Dr.View) -> List<&2, Dr.Span>:
  match v:
    case Dr.View{t, raw, sp, ns, tag}:
      sp

# LAW rows_gap_marks_every_jump (R2): in every read, the first span shown has
# no gap marker and every later span has one exactly when it does not
# start right after the span shown before it (a later span, an earlier one
# or an overlapping one; raw: every later span)
# EXCLUDES: ranges given backwards (5-6 then 1-2) or overlapping (1-5 then
# 3-6) shown with no marker between them; a marker between adjacent spans;
# a marker before the first span
law rows_gap_marks_every_jump:
  for +s: Dr.Sel
  for +utf8: Bool
  for +over: Bool
  for +p: Dl.Proj
  {rows.Marks(rows.Spans(Dr.view(s, utf8, over, p)), rows.Raw(s), None{}) == True{} : Bool}

# LAW rows_gap_example (anchor): a 9-line file read at 5-6 then 1-2 shows
# 5-6, a gap, 1-2; at 1-5 then 3-6 it shows 1-5, a gap, 3-6; at 1-2 then
# 3-4 it shows 1-2 and 3-4 with no gap
# EXCLUDES: the old rule (a marker only before a span past the one
# before), which shows the first two with no marker
law rows_gap_example:
  for b: Bool
  {[rows.Spans(Dr.view(Dr.Lines{[Dr.Range{5n, Some{6n}}, Dr.Range{1n, Some{2n}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]})), rows.Spans(Dr.view(Dr.Lines{[Dr.Range{1n, Some{5n}}, Dr.Range{3n, Some{6n}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]})), rows.Spans(Dr.view(Dr.Lines{[Dr.Range{1n, Some{2n}}, Dr.Range{3n, Some{4n}}], False{}}, True{}, False{}, Dl.Proj{b, [Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{1n, Some{Dl.Lf{}}}, Dl.Line{0n, None{}}]}))] == [[Dr.Span{5n, 6n, False{}}, Dr.Span{1n, 2n, True{}}], [Dr.Span{1n, 5n, False{}}, Dr.Span{3n, 6n, True{}}], [Dr.Span{1n, 2n, False{}}, Dr.Span{3n, 4n, False{}}]] : List<&2, List<&2, Dr.Span>>}

# The entry
# ---------

def rows.spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def rows.spell_range(r: Dr.Range, rest: String) -> String:
  match r:
    case Dr.Range{st, m}:
      Wr.put_nat(st, rows.spell_mnat(m, rest))

def rows.spell_sel(s: Dr.Sel, rest: String) -> String:
  match s:
    case Dr.Whole{}:
      Wr.put_nat(0n, rest)
    case Dr.Raw{}:
      Wr.put_nat(1n, rest)
    case Dr.Lines{xs, raw}:
      Wr.put_nat(2n, Wr.put_list(~Dr.Range, ~rows.spell_range, xs, Wr.put_bool(raw, rest)))

def rows.spell_span(x: Dr.Span, rest: String) -> String:
  match x:
    case Dr.Span{s, e, g}:
      Wr.put_nat(s, Wr.put_nat(e, Wr.put_bool(g, rest)))

def rows.spell_note(n: Dr.Note, rest: String) -> String:
  match n:
    case Dr.Beyond{l}:
      Wr.put_nat(0n, Wr.put_nat(l, rest))
    case Dr.Remain{c, x}:
      Wr.put_nat(1n, Wr.put_nat(c, Wr.put_nat(x, rest)))
    case Dr.RangeBeyond{s, m}:
      Wr.put_nat(2n, Wr.put_nat(s, rows.spell_mnat(m, rest)))
    case Dr.TooBig{}:
      Wr.put_nat(3n, rest)

def rows.spell_view(v: Dr.View) -> String:
  match v:
    case Dr.View{t, raw, sp, ns, tag}:
      Wr.put_nat(t, Wr.put_bool(raw, Wr.put_list(~Dr.Span, ~rows.spell_span, sp, Wr.put_list(~Dr.Note, ~rows.spell_note, ns, Wr.put_bool(tag, "")))))

def rows.spell_gate(g: Dr.Gate) -> String:
  match g:
    case Dr.Go{}:
      Wr.put_nat(0n, "")
    case Dr.NotUtf8{}:
      Wr.put_nat(1n, "")
    case Dr.Binary{}:
      Wr.put_nat(2n, "")

# the requests of the entry
type rows.Req is Data:
  rows.GateReq{raw: Bool, utf8: Bool, utf16: Bool, nul: Bool}
  rows.ViewReq{sel: Dr.Sel, utf8: Bool, over: Bool, p: Dl.Proj}

# the spelling of a request: its tag (0 gate, 1 view), then its fields
def rows.spell_req(r: rows.Req) -> String:
  match r:
    case rows.GateReq{raw, u8, u16, nul}:
      Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, "")))))
    case rows.ViewReq{sel, u8, over, p}:
      Wr.put_nat(1n, rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, "")))))

# the spelling of the model's answer (Dr.gate: rows_gate_goes_as_required and
# rows_gate_names_the_refusal; Dr.view is rows.View for every input,
# rows_view_shows)
def rows.answer(r: rows.Req) -> String:
  match r:
    case rows.GateReq{raw, u8, u16, nul}:
      rows.spell_gate(Dr.gate(raw, u8, u16, nul))
    case rows.ViewReq{sel, u8, over, p}:
      rows.spell_view(Dr.view(sel, u8, over, p))

def rows.RangesFit(xs: List<&2, Dr.Range>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      match x:
        case Dr.Range{+st, m}:
          Bool.and(Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m)), rows.RangesFit(rest))

def rows.SelFits(s: Dr.Sel) -> Bool:
  match s:
    case Dr.Whole{}:
      True{}
    case Dr.Raw{}:
      True{}
    case Dr.Lines{+xs, raw}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), rows.RangesFit(xs))

# every number of a request fits the wire
def rows.ReqFits(r: rows.Req) -> Bool:
  match r:
    case rows.GateReq{raw, u8, u16, nul}:
      True{}
    case rows.ViewReq{sel, u8, over, p}:
      Bool.and(rows.SelFits(sel), LawsBase.proj_fits(p))

# LAW rows_entry_answers (R5): the entry answers every request whose numbers
# fit the wire, spelled from the wire primitives, with the spelling of the
# model's decision
# EXCLUDES: a codec that loses, reorders or misreads a field (a range, the
# raw flag, a fact about the bytes, a line), a reply of another decision
# or in another spelling
law rows_entry_answers:
  for +r: rows.Req
  for h: {rows.ReqFits(r) == True{} : Bool}
  {Fdr.ffi(rows.spell_req(r)) == rows.answer(r) : String}

# LAW rows_entry_exact (R5): every input the entry does not answer with the
# error form is the spelling of a request whose numbers fit
# EXCLUDES: a default answer to malformed input, an unknown tag read as a
# known one, input left over ignored
law rows_entry_exact:
  for +s: String
  for h: {LawsBase.wire_opens_err(Fdr.ffi(s)) == False{} : Bool}
  exs r: rows.Req
  {s == rows.spell_req(r) : String} & {rows.ReqFits(r) == True{} : Bool}

# the spelling of a request, then rest (rows.spell_req is it before
# nothing)
def rows.spell_req_then(r: rows.Req, rest: String) -> String:
  match r:
    case rows.GateReq{raw, u8, u16, nul}:
      Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, rest)))))
    case rows.ViewReq{sel, u8, over, p}:
      Wr.put_nat(1n, rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, rest)))))

# LAW rows_entry_left_over_spelled: a spelled request whose numbers fit,
# followed by any more input, answers exactly the error form "doc_rows:
# input left over" (a gate and a view alike)
# EXCLUDES: trailing input ignored or read as part of the request, the
# left-over error reworded or swapped with the malformed one
law rows_entry_left_over_spelled:
  for +r: rows.Req
  for h: {rows.ReqFits(r) == True{} : Bool}
  for +c: Char
  for +t: String
  {Fdr.ffi(rows.spell_req_then(r, SCon{c, t})) == Wr.err("doc_rows: input left over") : String}

# LAW rows_entry_malformed_unless_request: every answer but the error form
# "doc_rows: malformed request" comes from an input that begins with a
# spelled request whose numbers fit
# EXCLUDES: the left-over error (or any answer) for input that does not
# begin with a request (an unknown tag, a malformed field anywhere), the
# malformed error reworded
law rows_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(Fdr.ffi(s), Wr.err("doc_rows: malformed request")) == False{} : Bool}
  exs r: rows.Req
  exs rest: String
  {(s, rows.ReqFits(r)) == (rows.spell_req_then(r, rest), True{}) : String & Bool}

# LAW rows_entry_errors_example_spec (anchor): the error texts Rust reads: an
# unknown tag is malformed; a gate and a view with input left over are
# refused as such
# EXCLUDES: the two texts swapped or reworded
law rows_entry_errors_example_spec:
  {[Fdr.ffi("9,"), Fdr.ffi("0,FFTFx"), Fdr.ffi("1,0,TFF3,1,1,0,1,1,0,0,0,x")] == [Wr.err("doc_rows: malformed request"), Wr.err("doc_rows: input left over"), Wr.err("doc_rows: input left over")] : List<&2, String>}

# LAW rows_entry_example (anchor): the requests Rust writes, as text: the
# gate of a UTF-16 file; a whole read of a 2-line file with a final `\n`;
# a read at 4-5 of it; one over the limit; an unknown tag
# EXCLUDES: another spelling of the requests or replies Rust reads
law rows_entry_example:
  {[Fdr.ffi("0,FFTF"), Fdr.ffi("1,0,TFF3,1,1,0,1,1,0,0,0,"), Fdr.ffi("1,2,1,4,1,5,FTFF3,1,1,0,1,1,0,0,0,"), Fdr.ffi("1,0,TTF1,0,0,"), Fdr.ffi("9,")] == ["1,", "2,F1,1,2,F0,T", "2,F0,1,0,4,T", "1,F1,1,1,F1,3,F", Wr.err("doc_rows: malformed request")] : List<&2, String>}

# LAW rows_req_fits_example (witness): requests of each kind fit the wire
# (rows_entry_answers is not vacuous)
law rows_req_fits_example:
  {[rows.ReqFits(rows.GateReq{False{}, True{}, False{}, False{}}), rows.ReqFits(rows.ViewReq{Dr.Lines{[Dr.Range{4n, Some{5n}}], False{}}, True{}, False{}, Dl.Proj{False{}, [Dl.Line{1n, None{}}]}})] == [True{}, True{}] : List<&2, Bool>}

# The error forms
# ---------------

# the spelling of a request, then the rest of the input
def rows.spell_req_on(r: rows.Req, rest: String) -> String:
  match r:
    case rows.GateReq{raw, u8, u16, nul}:
      Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, rest)))))
    case rows.ViewReq{sel, u8, over, p}:
      Wr.put_nat(1n, rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, rest)))))

# a request with more input after it: the request, then a char and the
# rest
type rows.LeftOver is Data:
  rows.LeftOver{req: rows.Req, head: Char, tail: String}

def rows.left_req(w: rows.LeftOver) -> rows.Req:
  match w:
    case rows.LeftOver{q, h, t}:
      q

def rows.spell_left_over(w: rows.LeftOver) -> String:
  match w:
    case rows.LeftOver{q, h, t}:
      rows.spell_req_on(q, SCon{h, t})

# LAW rows_entry_left_over (R5): a request whose numbers fit, followed by more
# input, answers the left-over error form
# EXCLUDES: the input after the request ignored or read as part of it
law rows_entry_left_over:
  for +r: rows.Req
  for +h: Char
  for +t: String
  for fit: {rows.ReqFits(r) == True{} : Bool}
  {Fdr.ffi(rows.spell_req_on(r, SCon{h, t})) == Wr.err("doc_rows: input left over") : String}

# LAW rows_entry_left_over_exact (R5): the entry answers the left-over error
# form only to a spelled request whose numbers fit, followed by more input
# EXCLUDES: the left-over text for a malformed request
law rows_entry_left_over_exact:
  for +s: String
  for e: {Fdr.ffi(s) == Wr.err("doc_rows: input left over") : String}
  exs w: rows.LeftOver
  {s == rows.spell_left_over(w) : String} & {rows.ReqFits(rows.left_req(w)) == True{} : Bool}

# LAW rows_entry_errors (R5): every error the entry answers is the malformed or
# the left-over error form; with rows_entry_exact, rows_entry_left_over
# and rows_entry_left_over_exact, every input that spells no request
# answers exactly "doc_rows: malformed request"
# EXCLUDES: another error text, a text that varies with the input
law rows_entry_errors:
  for +s: String
  for e: {LawsBase.wire_opens_err(Fdr.ffi(s)) == True{} : Bool}
  {Bool.or(LawsBase.text_same(Fdr.ffi(s), Wr.err("doc_rows: malformed request")), LawsBase.text_same(Fdr.ffi(s), Wr.err("doc_rows: input left over"))) == True{} : Bool}

# LAW rows_entry_errors_example (anchor): a gate and a view with input
# left over; a gate one flag short and a selector tag of 3 are malformed
# EXCLUDES: the two error texts swapped
law rows_entry_errors_example:
  {[Fdr.ffi("0,FFTFx"), Fdr.ffi("1,0,TFF0,x"), Fdr.ffi("0,FFT"), Fdr.ffi("1,3,TFF0,")] == [Wr.err("doc_rows: input left over"), Wr.err("doc_rows: input left over"), Wr.err("doc_rows: malformed request"), Wr.err("doc_rows: malformed request")] : List<&2, String>}
