# doc_lines: the model of the lines of a file, as the documents tools see
# them (crates/eukhe-docs/src/text.rs, hashline/patcher.rs persist,
# hashline/apply.rs materialize, read/mod.rs addressable_lines,
# grep/engine.rs rows).
#
# A file is an optional UTF-8 BOM and a body of bytes. The model uses
# three bytes: `a` (any content byte), `\r` and `\n`.
#
# Load: the body splits on `\n` into pieces. A `\r` right before `\n` is
# that line's CRLF ending; a lone `\r` is content. Each piece but the last
# has an ending; the last piece has none.
#
# Edit: an edit replaces the pieces [s, s+k) with new pieces. A new piece
# has no ending of its own. Persist writes the BOM, then each piece, and
# after each piece but the last a separator: the piece's own ending when
# it has one, else the separator written before it (the carry). The carry
# starts as the file's first ending, else LF.
#
# Rows: read turns each `\r\n` into `\n`, splits on `\n` and drops the
# empty piece after a final `\n`. Grep splits on `\n`, strips the `\r` of
# each `\r\n` terminator, and shows no row after a final `\n`.
#
# Rust scans a file into its projection (`proj` below) and the compiled
# core decides on it: the separators of an edit (`plan`), the carry of a
# loaded file (`carry`), what a write keeps (`write`), and what a read
# shows (bend/doc_rows.bend). The laws tie the projection to the bytes.

import Base

# Bytes and lines
# ---------------

type B is Data:
  A{}   # a content byte
  R{}   # \r
  N{}   # \n

type End is Data:
  Lf{}
  CrLf{}

# the lines of a body: each line but the last has an ending
type Lines is Data:
  More{text: List<&2, B>, end: End, rest: Lines}
  Last{text: List<&2, B>}

# a piece of an edited body: its text and the ending of the line it came
# from (None: a new line, or the last line of the file)
type Piece is Data:
  Piece{text: List<&2, B>, end: Maybe<&2, End>}

type Doc is Data:
  Doc{bom: Bool, body: List<&2, B>}

# a file being edited: its BOM, its first ending (the first carry) and
# its pieces
type Ed is Data:
  Ed{bom: Bool, first: End, pieces: List<&2, Piece>}

def ebytes(e: End) -> List<&2, B>:
  match e:
    case Lf{}:
      [N{}]
    case CrLf{}:
      [R{}, N{}]

# Load
# ----

# put b at the start of the first line
def push(b: B, ls: Lines) -> Lines:
  match ls:
    case More{t, e, r}:
      More{b <> t, e, r}
    case Last{t}:
      Last{b <> t}

# the lines of b <> bs, from the lines ls of bs
def cons(b: B, ls: Lines) -> Lines:
  match b:
    case A{}:
      push(A{}, ls)
    case N{}:
      More{[], Lf{}, ls}
    case R{}:
      match ls:
        case More{t, e, r}:
          match t:
            case Nil{}:
              match e:
                case Lf{}:
                  More{[], CrLf{}, r}
                case CrLf{}:
                  More{[R{}], CrLf{}, r}
            case h <> tt:
              More{R{} <> (h <> tt), e, r}
        case Last{t}:
          Last{R{} <> t}

def split(bs: List<&2, B>) -> Lines:
  match bs:
    case Nil{}:
      Last{[]}
    case b <> rest:
      cons(b, split(rest))

def pieces(ls: Lines) -> List<&2, Piece>:
  match ls:
    case More{t, e, r}:
      Piece{t, Some{e}} <> pieces(r)
    case Last{t}:
      [Piece{t, None{}}]

def first(ls: Lines) -> End:
  match ls:
    case More{t, e, r}:
      e
    case Last{t}:
      Lf{}

def load(f: Doc) -> Ed:
  match f:
    case Doc{bom, +bs}:
      Ed{bom, first(split(bs)), pieces(split(bs))}

# Edit
# ----

def fresh(xs: List<&2, List<&2, B>>) -> List<&2, Piece>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Piece{x, None{}} <> fresh(rest)

# replace the pieces [s, s+k) with the new lines xs
def edit(d: Ed, +s: Nat, k: Nat, xs: List<&2, List<&2, B>>) -> Ed:
  match d:
    case Ed{bom, c, +ps}:
      Ed{bom, c, List.append(&2, Piece, List.take(&2, Piece, ps, s), List.append(&2, Piece, fresh(xs), List.drop(&2, Piece, ps, Nat.add(s, k))))}

# Persist
# -------

# the separator after a piece: its own ending, else the carry
def sep(en: Maybe<&2, End>, c: End) -> End:
  match en:
    case None{}:
      c
    case Some{e}:
      e

# the bytes of p, then of rest, with the carry c before p
def emit(rest: List<&2, Piece>, c: End, p: Piece) -> List<&2, B>:
  match rest:
    case Nil{}:
      match p:
        case Piece{t, en}:
          t
    case q <> more:
      match p:
        case Piece{t, en}:
          +s = sep(en, c)
          List.append(&2, B, t, List.append(&2, B, ebytes(s), emit(more, s, q)))

def start(ps: List<&2, Piece>, c: End) -> List<&2, B>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      emit(rest, c, p)

def persist(d: Ed) -> Doc:
  match d:
    case Ed{bom, c, ps}:
      Doc{bom, start(ps, c)}

# The separators of persist, as runs
# ----------------------------------
# What persist writes between the lines of an edited file, without their
# bytes (patcher.rs `FileRead::persist`, through the compiled core:
# bend/ffi_doc_lines.bend, hashline/endings.rs): for each line of the edited text
# but the last, the ending of the file line it came from (None: a new
# line, or a line with no ending), as runs of equal values; the answer is
# the separator after each of those lines, as runs. Rust writes each line
# and then its separator. Runs keep the call small: an edit of a file with
# one kind of ending is a few runs, whatever its length.

# n lines in a row whose origin has this ending
type Run is Data:
  Run{end: Maybe<&2, End>, n: Nat}

# n separators in a row
type Seps is Data:
  Seps{end: End, n: Nat}

# the separators of the runs rs, with the carry c before them
def plan(rs: List<&2, Run>, c: End) -> List<&2, Seps>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Run{o, n}:
          match n:
            case 0n:
              plan(rest, c)
            case 1n+m:
              +s = sep(o, c)
              Seps{s, 1n+m} <> plan(rest, s)

# The bytes of a body
# -------------------

def isN(b: B) -> Bool:
  match b:
    case A{}:
      False{}
    case R{}:
      False{}
    case N{}:
      True{}

# the number of `\n` bytes
def lfs(bs: List<&2, B>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> rest:
      match b:
        case A{}:
          lfs(rest)
        case R{}:
          lfs(rest)
        case N{}:
          1n+lfs(rest)

# the bytes up to and with the n-th `\n` (all of them when there are fewer)
def upto(bs: List<&2, B>, n: Nat) -> List<&2, B>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case A{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              A{} <> upto(rest, 1n+m)
        case R{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              R{} <> upto(rest, 1n+m)
        case N{}:
          match n:
            case 0n:
              Nil{}
            case 1n+m:
              N{} <> upto(rest, m)

# the bytes after the n-th `\n` (none when there are fewer)
def from(bs: List<&2, B>, n: Nat) -> List<&2, B>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> rest:
      match b:
        case A{}:
          match n:
            case 0n:
              A{} <> rest
            case 1n+m:
              from(rest, 1n+m)
        case R{}:
          match n:
            case 0n:
              R{} <> rest
            case 1n+m:
              from(rest, 1n+m)
        case N{}:
          match n:
            case 0n:
              N{} <> rest
            case 1n+m:
              from(rest, m)

# Rows of read
# ------------

def lead(p: Bool, xs: List<&2, B>) -> List<&2, B>:
  match p:
    case True{}:
      R{} <> xs
    case False{}:
      xs

# each `\r\n` made `\n`; p: a `\r` is pending before bs
def nm(bs: List<&2, B>, p: Bool) -> List<&2, B>:
  match bs:
    case Nil{}:
      lead(p, Nil{})
    case b <> rest:
      match b:
        case A{}:
          lead(p, A{} <> nm(rest, False{}))
        case R{}:
          lead(p, nm(rest, True{}))
        case N{}:
          N{} <> nm(rest, False{})

def norm(bs: List<&2, B>) -> List<&2, B>:
  nm(bs, False{})

# put b at the start of the first piece
def pushN(b: B, ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match ps:
    case Nil{}:
      [[b]]
    case q <> m:
      (b <> q) <> m

def step(b: B, ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match b:
    case A{}:
      pushN(A{}, ps)
    case R{}:
      pushN(R{}, ps)
    case N{}:
      Nil{} <> ps

# the pieces between the `\n` bytes
def splitN(bs: List<&2, B>) -> List<&2, List<&2, B>>:
  match bs:
    case Nil{}:
      [[]]
    case b <> rest:
      step(b, splitN(rest))

def endsN.go(rest: List<&2, B>, b: B) -> Bool:
  match rest:
    case Nil{}:
      isN(b)
    case c <> more:
      endsN.go(more, c)

# whether the last byte is `\n`
def endsN(bs: List<&2, B>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> rest:
      endsN.go(rest, b)

def init.go(m: List<&2, List<&2, B>>, p: List<&2, B>) -> List<&2, List<&2, B>>:
  match m:
    case Nil{}:
      Nil{}
    case q <> more:
      p <> init.go(more, q)

# every piece but the last
def init(ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> m:
      init.go(m, p)

def fin(e: Bool, ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match e:
    case True{}:
      init(ps)
    case False{}:
      ps

# read: `\r\n` made `\n`, split on `\n`; a final `\n` adds no row
def read_rows(bs: List<&2, B>) -> List<&2, List<&2, B>>:
  +ys = norm(bs)
  fin(endsN(ys), splitN(ys))

# Rows of grep
# ------------

def stripR.go(rest: List<&2, B>, b: B) -> List<&2, B>:
  match rest:
    case Nil{}:
      match b:
        case A{}:
          [A{}]
        case R{}:
          Nil{}
        case N{}:
          [N{}]
    case c <> more:
      b <> stripR.go(more, c)

# a piece without its last byte when that byte is `\r`
def stripR(xs: List<&2, B>) -> List<&2, B>:
  match xs:
    case Nil{}:
      Nil{}
    case b <> rest:
      stripR.go(rest, b)

def lines.go(m: List<&2, List<&2, B>>, p: List<&2, B>) -> List<&2, List<&2, B>>:
  match m:
    case Nil{}:
      [p]
    case q <> more:
      stripR(p) <> lines.go(more, q)

# each piece that a `\n` ends, without the `\r` of a `\r\n`; the last
# piece (no terminator) as it is
def lines(ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> m:
      lines.go(m, p)

def lastrow.go(m: List<&2, List<&2, B>>, p: List<&2, B>) -> List<&2, List<&2, B>>:
  match m:
    case Nil{}:
      match p:
        case Nil{}:
          Nil{}
        case c <> cs:
          [c <> cs]
    case q <> more:
      p <> lastrow.go(more, q)

# the pieces, but an empty last piece (after a final `\n`) is no row
def lastrow(ps: List<&2, List<&2, B>>) -> List<&2, List<&2, B>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> m:
      lastrow.go(m, p)

# grep: split on `\n`, each line's terminator stripped, no row after a
# final `\n`
def grep_rows(bs: List<&2, B>) -> List<&2, List<&2, B>>:
  lastrow(lines(splitN(bs)))

# The projection Rust scans
# -------------------------
# Rust does not send the bytes of a file: it scans them into their
# projection (crates/eukhe-docs/src/text.rs `Projection`): the BOM flag
# and each line (each piece of `load`) as its length in chars and its
# own ending (None: the last piece). The decisions over the lines of a
# file run on the projection (bend/ffi_doc_lines.bend `L` and `W`
# requests, bend/doc_rows.bend).

type Line is Data:
  Line{len: Nat, end: Maybe<&2, End>}

type Proj is Data:
  Proj{bom: Bool, lines: List<&2, Line>}

def proj.line(p: Piece) -> Line:
  match p:
    case Piece{t, en}:
      Line{List.length(&2, B, t), en}

def proj.lines(ps: List<&2, Piece>) -> List<&2, Line>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      proj.line(p) <> proj.lines(rest)

# the projection of a file: what Rust's scan answers
def proj(f: Doc) -> Proj:
  match f:
    case Doc{bom, bs}:
      Proj{bom, proj.lines(pieces(split(bs)))}

# the first ending among the lines (None: no line has one)
def first_end(ls: List<&2, Line>) -> Maybe<&2, End>:
  match ls:
    case Nil{}:
      None{}
    case l <> rest:
      match l:
        case Line{n, en}:
          match en:
            case None{}:
              first_end(rest)
            case Some{e}:
              Some{e}

def or_lf(m: Maybe<&2, End>) -> End:
  match m:
    case None{}:
      Lf{}
    case Some{e}:
      e

# the carry of a loaded file (the separator before its first new line):
# its first ending, else LF
def carry(p: Proj) -> End:
  match p:
    case Proj{b, ls}:
      or_lf(first_end(ls))

def End.same(a: End, b: End) -> Bool:
  match a b:
    case Lf{} Lf{}:
      True{}
    case Lf{} CrLf{}:
      False{}
    case CrLf{} Lf{}:
      False{}
    case CrLf{} CrLf{}:
      True{}

# what `write` keeps of the file it replaces (write.rs): its BOM and its
# first ending (else LF) for every line of the new content; warn: both
# texts have line endings and the content's first one is another
type Kept is Data:
  Kept{bom: Bool, sep: End, warn: Bool}

def warn(k: Maybe<&2, End>, a: Maybe<&2, End>) -> Bool:
  match k:
    case None{}:
      False{}
    case Some{e}:
      match a:
        case None{}:
          False{}
        case Some{f}:
          Bool.not(End.same(e, f))

# the decision of a whole-file write: prev is the file on disk, next the
# content written over it
def write(prev: Proj, next: Proj) -> Kept:
  match prev next:
    case Proj{b, ls} Proj{c, ms}:
      +k = first_end(ls)
      Kept{b, or_lf(k), warn(k, first_end(ms))}
