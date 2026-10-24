# bound: the bounder of a tool's output (docs/runtime.md S2, limits 1 and
# 2): which bytes of the output it keeps under a cap, what it counts as
# dropped, what it stores while the output streams, and the truncation
# notice. Rust (crates/eukhe-durable/src/harness/output.rs) moves the
# bytes; this model decides, run as the compiled Bend core
# (bend/ffi_bound.bend). Laws: laws/bound.bend.
#
# The opt-out (`Truncation::Off`) keeps every byte and drops none: it has
# no cap, so nothing here runs for it.

import Base

# A cap: keep at most `bytes` bytes in at most `lines` lines, from the
# start of the output (head) or from its end (tail)
type Cap is Data:
  Cap{bytes: Nat, lines: Nat, tail: Bool}

def Cap.bytes(c: Cap) -> Nat:
  match c:
    case Cap{b, l, t}:
      b

def Cap.lines(c: Cap) -> Nat:
  match c:
    case Cap{b, l, t}:
      l

def Cap.tail(c: Cap) -> Bool:
  match c:
    case Cap{b, l, t}:
      t

# A text as Rust reads it: the byte length of each of its lines in order
# (a line ends after its newline; the last line has none when the text
# does not end with one: `open`), and three cuts at character boundaries:
# the bytes of the longest start of the text within the cap's bytes
# (head), of the longest end within them (tail), and of the shortest end
# past them (margin; the whole text when it is not longer)
type Body is Data:
  Body{lines: List<&2, Nat>, open: Bool, head: Nat, tail: Nat, margin: Nat}

def Body.lines(x: Body) -> List<&2, Nat>:
  match x:
    case Body{xs, o, h, t, m}:
      xs

def Body.head(x: Body) -> Nat:
  match x:
    case Body{xs, o, h, t, m}:
      h

def Body.tail(x: Body) -> Nat:
  match x:
    case Body{xs, o, h, t, m}:
      t

# A window: the bytes and the lines it keeps
type Win is Data:
  Win{bytes: Nat, lines: Nat}

def Win.bytes(w: Win) -> Nat:
  match w:
    case Win{b, l}:
      b

def Win.lines(w: Win) -> Nat:
  match w:
    case Win{b, l}:
      l

# The window
# ----------

# the bytes of the lines xs
def total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, total(rest))

def fill.more(+x: Nat, w: Win) -> Win:
  match w:
    case Win{b, l}:
      Win{Nat.add(x, b), 1n+l}

def fill.pick(fits: Bool, +x: Nat, w: Win) -> Win:
  match fits:
    case True{}:
      fill.more(x, w)
    case False{}:
      Win{0n, 0n}

# the most whole lines of xs, from the first, at most k of them, within b
# bytes
def fill(xs: List<&2, Nat>, k: Nat, +b: Nat) -> Win:
  match xs:
    case Nil{}:
      Win{0n, 0n}
    case +x <> rest:
      match k:
        case 0n:
          Win{0n, 0n}
        case 1n+j:
          fill.pick(Nat.is_le(x, b), x, fill(rest, j, Nat.sub(b, x)))

# the first line cut to c bytes
def keep.cut(c: Nat) -> Win:
  match c:
    case 0n:
      Win{0n, 0n}
    case 1n+p:
      Win{1n+p, 1n}

def keep.none(xs: List<&2, Nat>, c: Nat) -> Win:
  match xs:
    case Nil{}:
      Win{0n, 0n}
    case x <> rest:
      keep.cut(c)

def keep.of(w: Win, xs: List<&2, Nat>, c: Nat) -> Win:
  match w:
    case Win{b, l}:
      match l:
        case 0n:
          keep.none(xs, c)
        case 1n+m:
          Win{b, 1n+m}

# the window of the lines xs, from the end the cap keeps: the most whole
# lines, at most k, within b bytes; when not even the first line fits, it
# is cut to c bytes (a character boundary within b); nothing under a cap
# of no line or no byte
def keep(+xs: List<&2, Nat>, k: Nat, b: Nat, c: Nat) -> Win:
  match k:
    case 0n:
      Win{0n, 0n}
    case 1n+j:
      match b:
        case 0n:
          Win{0n, 0n}
        case 1n+q:
          keep.of(fill(xs, 1n+j, 1n+q), xs, c)

def window.go(t: Bool, +k: Nat, +b: Nat, xs: List<&2, Nat>, +hc: Nat, +tc: Nat) -> Win:
  match t:
    case False{}:
      keep(xs, k, b, hc)
    case True{}:
      keep(List.reverse(&2, Nat, xs), k, b, tc)

# the window a cap keeps of a text: its first lines (head) or its last
# (tail)
def window(c: Cap, x: Body) -> Win:
  match c:
    case Cap{b, k, t}:
      match x:
        case Body{xs, o, hc, tc, mc}:
          window.go(t, k, b, xs, hc, tc)

# Where the window lies in the text: from, to (byte offsets)
type Span is Data:
  Span{from: Nat, to: Nat}

def Span.from(s: Span) -> Nat:
  match s:
    case Span{f, t}:
      f

def Span.to(s: Span) -> Nat:
  match s:
    case Span{f, t}:
      t

def span.of(t: Bool, +len: Nat, +kept: Nat) -> Span:
  match t:
    case False{}:
      Span{0n, kept}
    case True{}:
      Span{Nat.sub(len, kept), len}

# One bounded text, whole: where its window lies, then the bytes and the
# lines it drops
type Slice is Data:
  Slice{span: Span, bytes: Nat, lines: Nat}

def Slice.span(s: Slice) -> Span:
  match s:
    case Slice{sp, b, l}:
      sp

def Slice.bytes(s: Slice) -> Nat:
  match s:
    case Slice{sp, b, l}:
      b

def slice.of(t: Bool, +len: Nat, +n: Nat, w: Win) -> Slice:
  match w:
    case Win{+kb, kl}:
      Slice{span.of(t, len, kb), Nat.sub(len, kb), Nat.sub(n, kl)}

# the window of a whole text under a cap, and what it drops of it
def slice(+c: Cap, +x: Body) -> Slice:
  match x:
    case Body{+xs, o, hc, tc, mc}:
      slice.of(Cap.tail(c), total(xs), List.length(&2, Nat, xs), window(c, Body{xs, o, hc, tc, mc}))

# The notice
# ----------

# Where a notice says the output was cut
type At is Data:
  AtEnd{}
  AtStart{}

def notice.at(t: Bool) -> At:
  match t:
    case False{}:
      AtEnd{}
    case True{}:
      AtStart{}

def notice.go(still: Bool, t: Bool) -> Maybe<&2, At>:
  match still:
    case True{}:
      Some{notice.at(t)}
    case False{}:
      None{}

# the truncation notice of an output that dropped `dropped` bytes, while
# the result still holds that output (`still`): none when nothing was
# dropped; else at its end for a head cap, at its start for a tail cap
def notice(t: Bool, dropped: Nat, still: Bool) -> Maybe<&2, At>:
  match dropped:
    case 0n:
      None{}
    case 1n+p:
      notice.go(still, t)

# The stream
# ----------
# Rust feeds the output's texts as they come (their bytes, newlines, and
# whether the output then ends inside a line), the output a shell left out
# (tail only), and, to read the window, the text it stores. A head stores
# the start of the output until its window is full; a tail stores the end,
# trimmed to a margin that every later window still finds.

# The state: the cap, the bytes and newlines of the whole output so far,
# whether it ends inside a line, and the bytes Rust stores
type St is Data:
  St{cap: Cap, bytes: Nat, newlines: Nat, open: Bool, stored: Nat}

# What Rust does with a text: drop it (the head window is full), store it,
# or store it and then trim (send the stored text)
type Act is Data:
  Drop{}
  Store{}
  Trim{}

# the lines of an output of n newlines that ends inside a line or not
def lines(+n: Nat, o: Bool) -> Nat:
  match o:
    case False{}:
      n
    case True{}:
      1n+n

# a head window is full once more than its bytes, or its lines' newlines,
# came: no later byte is in it
def full(c: Cap, +bytes: Nat, +newlines: Nat) -> Bool:
  match c:
    case Cap{b, l, t}:
      Bool.or(Nat.is_lt(b, bytes), Nat.is_le(l, newlines))

# a tail trims once it stores more than twice its bytes and the widest
# character
def over(c: Cap, +stored: Nat) -> Bool:
  match c:
    case Cap{+b, l, t}:
      Nat.is_lt(Nat.add(Nat.add(b, b), 8n), stored)

def out.tail(tr: Bool, +c: Cap, +bytes: Nat, +newlines: Nat, o: Bool, +stored: Nat) -> St & Act:
  match tr:
    case True{}:
      (St{c, bytes, newlines, o, stored}, Trim{})
    case False{}:
      (St{c, bytes, newlines, o, stored}, Store{})

def out.head(f: Bool, +c: Cap, +bytes: Nat, +newlines: Nat, o: Bool, +stored: Nat, +n: Nat) -> St & Act:
  match f:
    case True{}:
      (St{c, bytes, newlines, o, stored}, Drop{})
    case False{}:
      (St{c, bytes, newlines, o, Nat.add(stored, n)}, Store{})

def out.go(t: Bool, +c: Cap, +b: Nat, +nl: Nat, +sd: Nat, +n: Nat, +k: Nat, o: Bool) -> St & Act:
  match t:
    case False{}:
      out.head(full(c, b, nl), c, Nat.add(b, n), Nat.add(nl, k), o, sd, n)
    case True{}:
      out.tail(over(c, Nat.add(sd, n)), c, Nat.add(b, n), Nat.add(nl, k), o, Nat.add(sd, n))

# a text of n bytes and k newlines comes; o: the output now ends inside a
# line
def out(s: St, +n: Nat, +k: Nat, o: Bool) -> St & Act:
  match s:
    case St{+c, +b, +nl, op, +sd}:
      out.go(Cap.tail(c), c, b, nl, sd, n, k, o)

def skip.tail(+c: Cap, +b: Nat, +nl: Nat, op: Bool, +sd: Nat, n: Nat, +k: Nat, o: Bool) -> St & Bool:
  match n:
    case 0n:
      (St{c, b, nl, op, sd}, False{})
    case 1n+p:
      (St{c, Nat.add(b, 1n+p), Nat.add(nl, k), o, 0n}, True{})

# a shell left out n bytes of k newlines before its next text (tail only);
# o: the output then ends inside a line. The answer: Rust clears what it
# stores (no stored byte is in a later window); a skip of no byte changes
# nothing, and a head never skips
def skip.go(t: Bool, +c: Cap, +b: Nat, +nl: Nat, op: Bool, +sd: Nat, n: Nat, +k: Nat, o: Bool) -> St & Bool:
  match t:
    case False{}:
      (St{c, b, nl, op, sd}, False{})
    case True{}:
      skip.tail(c, b, nl, op, sd, n, k, o)

def skip(s: St, n: Nat, +k: Nat, o: Bool) -> St & Bool:
  match s:
    case St{+c, +b, +nl, op, +sd}:
      skip.go(Cap.tail(c), c, b, nl, op, sd, n, k, o)

# The margin: the end of a stored text a tail keeps, so that every later
# window finds its lines and bytes
# ---------------------------------------------------------------------

# the bytes from the newline of the (q+1)-th line of rs (the lines from
# the end) to the end, newline included: none when there are not so many
def mline.add(+r: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Nat.add(r, v)}

def mline(rs: List<&2, Nat>, q: Nat) -> Maybe<&2, Nat>:
  match rs:
    case Nil{}:
      None{}
    case +r <> rest:
      match q:
        case 0n:
          Some{1n}
        case 1n+p:
          mline.add(r, mline(rest, p))

def least.pick(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

def least(+a: Nat, +b: Nat) -> Nat:
  least.pick(Nat.is_le(a, b), a, b)

def margin.lines(m: Maybe<&2, Nat>, +len: Nat) -> Nat:
  match m:
    case None{}:
      len
    case Some{v}:
      v

# the bytes a tail keeps stored: the shortest end of the text with more
# than the cap's bytes or more than its lines' newlines (the whole text
# when it has neither)
def margin(c: Cap, x: Body) -> Nat:
  match c:
    case Cap{b, k, t}:
      match x:
        case Body{+xs, o, hc, tc, mc}:
          least(mc, margin.lines(mline(List.reverse(&2, Nat, xs), lines(k, o)), total(xs)))

# What Rust reads of the stored text: where the window lies in it, the
# bytes and the lines the whole output dropped, and where the stored text
# now starts (a head keeps it all; a tail keeps its margin)
type Seen is Data:
  Seen{span: Span, bytes: Nat, lines: Nat, cut: Nat}

def look.cut(t: Bool, +c: Cap, +x: Body, +len: Nat) -> Nat:
  match t:
    case False{}:
      0n
    case True{}:
      Nat.sub(len, margin(c, x))

def look.of(+c: Cap, +b: Nat, +nl: Nat, +op: Bool, +x: Body, +len: Nat, w: Win) -> St & Seen:
  match w:
    case Win{+kb, kl}:
      +cut = look.cut(Cap.tail(c), c, x, len)
      (St{c, b, nl, op, Nat.sub(len, cut)}, Seen{span.of(Cap.tail(c), len, kb), Nat.sub(b, kb), Nat.sub(lines(nl, op), kl), cut})

# Rust sends the text it stores: the window of the whole output is the
# window of that text
def look(s: St, +x: Body) -> St & Seen:
  match s:
    case St{+c, +b, +nl, +op, sd}:
      match x:
        case Body{+xs, o, hc, tc, mc}:
          look.of(c, b, nl, op, Body{xs, o, hc, tc, mc}, total(xs), window(c, Body{xs, o, hc, tc, mc}))

# a new stream under the cap c: nothing came, nothing is stored
def start(c: Cap) -> St:
  St{c, 0n, 0n, False{}, 0n}
