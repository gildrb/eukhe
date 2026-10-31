# eukhe: the laws of the bounder of a tool's output (limits 1 and 2; the
# model bend/bound.bend, the entry bend/ffi_bound.bend)

import Base
import ../bend/bound.bend as Bd
import ../bend/ffi_bound.bend as FBd
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Fields, read by the spec itself (never through the model's accessors)
# ---------------------------------------------------------------------

def bd_cap_bytes(c: Bd.Cap) -> Nat:
  match c:
    case Bd.Cap{b, k, t}:
      b

def bd_cap_lines(c: Bd.Cap) -> Nat:
  match c:
    case Bd.Cap{b, k, t}:
      k

def bd_cap_tail(c: Bd.Cap) -> Bool:
  match c:
    case Bd.Cap{b, k, t}:
      t

def bd_body_lines(x: Bd.Body) -> List<&2, Nat>:
  match x:
    case Bd.Body{xs, o, h, t, m}:
      xs

def bd_body_head(x: Bd.Body) -> Nat:
  match x:
    case Bd.Body{xs, o, h, t, m}:
      h

def bd_body_tail(x: Bd.Body) -> Nat:
  match x:
    case Bd.Body{xs, o, h, t, m}:
      t

def bd_win_bytes(w: Bd.Win) -> Nat:
  match w:
    case Bd.Win{b, l}:
      b

def bd_win_lines(w: Bd.Win) -> Nat:
  match w:
    case Bd.Win{b, l}:
      l

def bd_span_from(s: Bd.Span) -> Nat:
  match s:
    case Bd.Span{f, t}:
      f

def bd_span_to(s: Bd.Span) -> Nat:
  match s:
    case Bd.Span{f, t}:
      t

def bd_slice_span(s: Bd.Slice) -> Bd.Span:
  match s:
    case Bd.Slice{sp, b, l}:
      sp

def bd_slice_bytes(s: Bd.Slice) -> Nat:
  match s:
    case Bd.Slice{sp, b, l}:
      b

# (S2) The window
# ---------------
# A cap keeps at most its bytes in at most its lines, from the start of
# the output (head) or from its end (tail): whole lines, unless not even
# the first line from that end fits, which is then cut at a character
# boundary (the cut Rust reads at the cap's byte limit). Every line is
# free (any count, any lengths), every cap is free, every cut is free.

# the bytes of the lines xs
def bd_total(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(x, bd_total(rest))

# the first n lines of xs
def bd_take(xs: List<&2, Nat>, n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          x <> bd_take(rest, p)

# xs from its last line to its first
def bd_rev(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      List.append(&2, Nat, bd_rev(rest), [x])

def bd_count.pick(fits: Bool, m: Nat) -> Nat:
  match fits:
    case True{}:
      1n+m
    case False{}:
      0n

# how many of the first lines of xs, at most k, fit within b bytes
def bd_count(xs: List<&2, Nat>, k: Nat, +b: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> rest:
      match k:
        case 0n:
          0n
        case 1n+j:
          bd_count.pick(Nat.is_le(x, b), bd_count(rest, j, Nat.sub(b, x)))

# the first line cut to c bytes: no line when c is 0
def bd_cut(c: Nat) -> Bd.Win:
  match c:
    case 0n:
      Bd.Win{0n, 0n}
    case 1n+p:
      Bd.Win{1n+p, 1n}

def bd_keep.none(xs: List<&2, Nat>, c: Nat) -> Bd.Win:
  match xs:
    case Nil{}:
      Bd.Win{0n, 0n}
    case x <> rest:
      bd_cut(c)

def bd_keep.lines(m: Nat, +xs: List<&2, Nat>, c: Nat) -> Bd.Win:
  match m:
    case 0n:
      bd_keep.none(xs, c)
    case 1n++p:
      Bd.Win{bd_total(bd_take(xs, 1n+p)), 1n+p}

# the window of the lines xs (from the end the cap keeps) under k lines,
# b bytes and the cut c: the first m lines when m of them fit (the most,
# at most k), else the first line cut to c; nothing for no line or no byte
def bd_keep(+xs: List<&2, Nat>, k: Nat, b: Nat, c: Nat) -> Bd.Win:
  match k:
    case 0n:
      Bd.Win{0n, 0n}
    case 1n+j:
      match b:
        case 0n:
          Bd.Win{0n, 0n}
        case 1n+q:
          bd_keep.lines(bd_count(xs, 1n+j, 1n+q), xs, c)

def bd_window.go(t: Bool, +k: Nat, +b: Nat, xs: List<&2, Nat>, hc: Nat, tc: Nat) -> Bd.Win:
  match t:
    case False{}:
      bd_keep(xs, k, b, hc)
    case True{}:
      bd_keep(bd_rev(xs), k, b, tc)

# the window of a body: of its lines from the first (head) with its head
# cut, or from the last (tail) with its tail cut
def bd_window(c: Bd.Cap, x: Bd.Body) -> Bd.Win:
  match c:
    case Bd.Cap{b, k, t}:
      match x:
        case Bd.Body{xs, o, hc, tc, mc}:
          bd_window.go(t, k, b, xs, hc, tc)

def bd_span(t: Bool, +len: Nat, +kept: Nat) -> Bd.Span:
  match t:
    case False{}:
      Bd.Span{0n, kept}
    case True{}:
      Bd.Span{Nat.sub(len, kept), len}

def bd_slice.of(t: Bool, +len: Nat, +n: Nat, w: Bd.Win) -> Bd.Slice:
  match w:
    case Bd.Win{+kb, kl}:
      Bd.Slice{bd_span(t, len, kb), Nat.sub(len, kb), Nat.sub(n, kl)}

# a whole body's slice: its window at the start (head) or the end (tail),
# then the bytes and lines it drops
def bd_slice(c: Bd.Cap, x: Bd.Body) -> Bd.Slice:
  match c:
    case Bd.Cap{+b, +k, +t}:
      match x:
        case Bd.Body{+xs, o, +hc, +tc, mc}:
          bd_slice.of(t, bd_total(xs), List.length(&2, Nat, xs), bd_window(Bd.Cap{b, k, t}, Bd.Body{xs, o, hc, tc, mc}))

# LAW bound_keep_exact: the window of lines is exactly the spec's: the most whole lines that fit (at most k, within b bytes), else the first line cut, nothing under no line or no byte
# EXCLUDES: a window that skips a line, takes one past the cap, keeps a
#   line that does not fit, cuts a line that fits or cuts at another byte
law bound_keep_exact:
  for +xs: List<&2, Nat>
  for +k: Nat
  for +b: Nat
  for +c: Nat
  {Bd.keep(xs, k, b, c) == bd_keep(xs, k, b, c) : Bd.Win}

# LAW bound_window_exact: a body's window is its lines' window from the start under the head cut (head), or from the end under the tail cut (tail)
# EXCLUDES: a tail that keeps the first lines, a head that keeps the last,
#   the wrong cut, the lines read out of order
law bound_window_exact:
  for +c: Bd.Cap
  for +x: Bd.Body
  {Bd.window(c, x) == bd_window(c, x) : Bd.Win}

# LAW bound_slice_exact: a whole text's slice is its window, where it lies (from the start for head, at the end for tail), and the bytes and lines left out of it
# EXCLUDES: a window placed at the wrong end, dropped counts other than
#   the text's bytes and lines less the window's
law bound_slice_exact:
  for +c: Bd.Cap
  for +x: Bd.Body
  {Bd.slice(c, x) == bd_slice(c, x) : Bd.Slice}

# LAW bound_window_within: under cuts within the cap's bytes, a window keeps at most the cap's bytes and at most its lines
# EXCLUDES: a window past the cap (limits 1)
law bound_window_within:
  for +c: Bd.Cap
  for +x: Bd.Body
  for hc: {Nat.is_le(bd_body_head(x), bd_cap_bytes(c)) == True{} : Bool}
  for tc: {Nat.is_le(bd_body_tail(x), bd_cap_bytes(c)) == True{} : Bool}
  {Nat.is_le(bd_win_bytes(Bd.window(c, x)), bd_cap_bytes(c)) == True{} : Bool} & {Nat.is_le(bd_win_lines(Bd.window(c, x)), bd_cap_lines(c)) == True{} : Bool}

# LAW bound_window_keeps_what_fits: a text within the cap's bytes and lines is kept whole: every byte and every line, nothing dropped
# EXCLUDES: a cap that drops output that fits (limits 2)
law bound_window_keeps_what_fits:
  for +c: Bd.Cap
  for +x: Bd.Body
  for some: {Nat.is_lt(0n, bd_cap_bytes(c)) == True{} : Bool}
  for bytes: {Nat.is_le(bd_total(bd_body_lines(x)), bd_cap_bytes(c)) == True{} : Bool}
  for lines: {Nat.is_le(List.length(&2, Nat, bd_body_lines(x)), bd_cap_lines(c)) == True{} : Bool}
  {Bd.slice(c, x) == Bd.Slice{Bd.Span{0n, bd_total(bd_body_lines(x))}, 0n, 0n} : Bd.Slice}

# LAW bound_slice_conserves: under cuts within the text, the bytes kept and the bytes dropped are every byte of the text
# EXCLUDES: a silent loss: bytes neither kept nor counted (limits 2)
law bound_slice_conserves:
  for +c: Bd.Cap
  for +x: Bd.Body
  for hc: {Nat.is_le(bd_body_head(x), bd_total(bd_body_lines(x))) == True{} : Bool}
  for tc: {Nat.is_le(bd_body_tail(x), bd_total(bd_body_lines(x))) == True{} : Bool}
  {Nat.add(Nat.sub(bd_span_to(bd_slice_span(Bd.slice(c, x))), bd_span_from(bd_slice_span(Bd.slice(c, x)))), bd_slice_bytes(Bd.slice(c, x))) == bd_total(bd_body_lines(x)) : Nat}

# the lines a head stored up to a point of the output: whole lines, then p
# bytes of the next line (no piece when p is 0)
def bd_part(p: Nat) -> List<&2, Nat>:
  match p:
    case 0n:
      Nil{}
    case 1n+q:
      [1n+q]

# LAW bound_head_full_keeps: once a head's window is full (more than its bytes, or as many newlines as its lines, came), the window of what it stored (whole lines ys, then p bytes of the next line, of x bytes) is the window of the whole output, whatever came after: a head that drops later texts loses nothing its window holds
# EXCLUDES: a head that drops a text its window still needs, or keeps a
#   window that reaches past what it stored
law bound_head_full_keeps:
  for +ys: List<&2, Nat>
  for +p: Nat
  for +x: Nat
  for +rest: List<&2, Nat>
  for +k: Nat
  for +b: Nat
  for +c: Nat
  for part: {Nat.is_le(p, x) == True{} : Bool}
  for full: {Bool.or(Nat.is_lt(b, Nat.add(bd_total(ys), p)), Nat.is_le(k, List.length(&2, Nat, ys))) == True{} : Bool}
  {Bd.keep(List.append(&2, Nat, ys, bd_part(p)), k, b, c) == Bd.keep(List.append(&2, Nat, ys, x <> rest), k, b, c) : Bd.Win}

# (S2) The notice
# ---------------

def bd_notice.at(t: Bool) -> Bd.At:
  match t:
    case False{}:
      Bd.AtEnd{}
    case True{}:
      Bd.AtStart{}

def bd_notice(t: Bool, d: Nat, s: Bool) -> Maybe<&2, Bd.At>:
  match d:
    case 0n:
      None{}
    case 1n+p:
      match s:
        case False{}:
          None{}
        case True{}:
          Some{bd_notice.at(t)}

# LAW bound_notice_exact: a truncation notice comes exactly when bytes were dropped and the result still holds the output: at its end under a head cap, at its start under a tail cap
# EXCLUDES: a silent truncation, a notice for output kept whole or for an
#   output the result no longer holds, a notice at the wrong end
law bound_notice_exact:
  for +t: Bool
  for +d: Nat
  for +s: Bool
  {Bd.notice(t, d, s) == bd_notice(t, d, s) : Maybe<&2, Bd.At>}

# (S2) The stream
# ---------------
# Rust feeds an output's texts as they come; the model counts the whole
# output and decides what Rust stores. Every text, skip and stored text
# is free.

def bd_lines(n: Nat, o: Bool) -> Nat:
  match o:
    case False{}:
      n
    case True{}:
      1n+n

def bd_out.tail(over: Bool) -> Bd.Act:
  match over:
    case True{}:
      Bd.Trim{}
    case False{}:
      Bd.Store{}

def bd_out.head(full: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, o: Bool, +sd: Nat, +n: Nat) -> Bd.St & Bd.Act:
  match full:
    case True{}:
      (Bd.St{c, b, nl, o, sd}, Bd.Drop{})
    case False{}:
      (Bd.St{c, b, nl, o, Nat.add(sd, n)}, Bd.Store{})

def bd_out.go(t: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, +sd: Nat, +n: Nat, +k: Nat, o: Bool) -> Bd.St & Bd.Act:
  match t:
    case False{}:
      bd_out.head(Bool.or(Nat.is_lt(bd_cap_bytes(c), b), Nat.is_le(bd_cap_lines(c), nl)), c, Nat.add(b, n), Nat.add(nl, k), o, sd, n)
    case True{}:
      (Bd.St{c, Nat.add(b, n), Nat.add(nl, k), o, Nat.add(sd, n)}, bd_out.tail(Nat.is_lt(Nat.add(Nat.add(bd_cap_bytes(c), bd_cap_bytes(c)), 8n), Nat.add(sd, n))))

# a text of n bytes and k newlines: the whole output's counts grow by it
# and it ends inside a line or not (o); a head drops it once its window
# is full (more bytes than the cap's, or as many newlines as its lines,
# before it), else stores it; a tail stores it, and trims once it stores
# more than twice the cap's bytes and 8 (twice the widest character)
def bd_out(s: Bd.St, +n: Nat, +k: Nat, o: Bool) -> Bd.St & Bd.Act:
  match s:
    case Bd.St{+c, +b, +nl, op, +sd}:
      bd_out.go(bd_cap_tail(c), c, b, nl, sd, n, k, o)

def bd_skip.go(t: Bool, +c: Bd.Cap, +b: Nat, +nl: Nat, op: Bool, +sd: Nat, n: Nat, +k: Nat, o: Bool) -> Bd.St & Bool:
  match t:
    case False{}:
      (Bd.St{c, b, nl, op, sd}, False{})
    case True{}:
      match n:
        case 0n:
          (Bd.St{c, b, nl, op, sd}, False{})
        case 1n+p:
          (Bd.St{c, Nat.add(b, 1n+p), Nat.add(nl, k), o, 0n}, True{})

# output a shell left out: a tail counts it and clears what it stores; a
# skip of no byte, or under a head, changes nothing
def bd_skip(s: Bd.St, n: Nat, +k: Nat, o: Bool) -> Bd.St & Bool:
  match s:
    case Bd.St{+c, +b, +nl, op, +sd}:
      bd_skip.go(bd_cap_tail(c), c, b, nl, op, sd, n, k, o)

def bd_least(le: Bool, a: Nat, b: Nat) -> Nat:
  match le:
    case True{}:
      a
    case False{}:
      b

def bd_mline.go(more: Bool, +rs: List<&2, Nat>, +q: Nat) -> Maybe<&2, Nat>:
  match more:
    case True{}:
      Some{Nat.add(bd_total(bd_take(rs, q)), 1n)}
    case False{}:
      None{}

# the bytes from the newline of line q+1 of rs (lines from the end) to the
# end, its newline included: none when rs has q lines or fewer
def bd_mline(+rs: List<&2, Nat>, +q: Nat) -> Maybe<&2, Nat>:
  bd_mline.go(Nat.is_lt(q, List.length(&2, Nat, rs)), rs, q)

def bd_margin.lines(m: Maybe<&2, Nat>, +len: Nat) -> Nat:
  match m:
    case None{}:
      len
    case Some{v}:
      v

def bd_margin.go(+mc: Nat, +ml: Nat) -> Nat:
  bd_least(Nat.is_le(mc, ml), mc, ml)

# the end of a body a tail keeps stored: the shorter of its margin cut (the
# shortest end past the cap's bytes) and its end from the newline after
# which it holds more lines than the cap's (counting a last open line)
def bd_margin(c: Bd.Cap, x: Bd.Body) -> Nat:
  match c:
    case Bd.Cap{b, k, t}:
      match x:
        case Bd.Body{+xs, o, hc, tc, mc}:
          bd_margin.go(mc, bd_margin.lines(bd_mline(bd_rev(xs), bd_lines(k, o)), bd_total(xs)))

def bd_look.cut(t: Bool, +c: Bd.Cap, +x: Bd.Body, +len: Nat) -> Nat:
  match t:
    case False{}:
      0n
    case True{}:
      Nat.sub(len, bd_margin(c, x))

def bd_look.of(+c: Bd.Cap, +b: Nat, +nl: Nat, +op: Bool, +x: Bd.Body, +len: Nat, w: Bd.Win) -> Bd.St & Bd.Seen:
  match w:
    case Bd.Win{+kb, kl}:
      +cut = bd_look.cut(bd_cap_tail(c), c, x, len)
      (Bd.St{c, b, nl, op, Nat.sub(len, cut)}, Bd.Seen{bd_span(bd_cap_tail(c), len, kb), Nat.sub(b, kb), Nat.sub(bd_lines(nl, op), kl), cut})

# the stored text Rust sends: the window of the whole output is that
# text's window; the output dropped its bytes and lines less the
# window's; a head keeps the text stored, a tail keeps its margin
def bd_look(s: Bd.St, +x: Bd.Body) -> Bd.St & Bd.Seen:
  match s:
    case Bd.St{+c, +b, +nl, +op, sd}:
      bd_look.of(c, b, nl, op, x, bd_total(bd_body_lines(x)), bd_window(c, x))

# LAW bound_out_exact: a text of the output is exactly: counted into the whole output, then dropped by a full head, stored by a head that is not full, stored by a tail, trimmed by a tail that stores more than twice its bytes and 8
# EXCLUDES: a count that loses a text, a head that stores past its window
#   or drops a text its window needs, a tail that never trims (memory
#   grows with the output) or trims early
law bound_out_exact:
  for +s: Bd.St
  for +n: Nat
  for +k: Nat
  for +o: Bool
  {Bd.out(s, n, k, o) == bd_out(s, n, k, o) : Bd.St & Bd.Act}

# LAW bound_skip_exact: output a shell left out is exactly: counted into a tail's output, which clears what it stores; nothing for a skip of no byte or under a head
# EXCLUDES: skipped bytes lost from the count, a stored text kept before a
#   skip (a window across the gap)
law bound_skip_exact:
  for +s: Bd.St
  for +n: Nat
  for +k: Nat
  for +o: Bool
  {Bd.skip(s, n, k, o) == bd_skip(s, n, k, o) : Bd.St & Bool}

# LAW bound_margin_exact: a tail keeps stored exactly the shorter of the stored text's margin cut and its end from the newline before its last lines past the cap's
# EXCLUDES: a trim that cuts into a later window
law bound_margin_exact:
  for +c: Bd.Cap
  for +x: Bd.Body
  {Bd.margin(c, x) == bd_margin(c, x) : Nat}

# LAW bound_look_exact: the stored text Rust sends gives exactly: where its window lies, the whole output's bytes and lines less the window's, and where the stored text now starts (all of it for a head, its margin for a tail)
# EXCLUDES: dropped counts of the stored text instead of the whole output,
#   a trim of a head, a stored size the next text cannot grow from
law bound_look_exact:
  for +s: Bd.St
  for +x: Bd.Body
  {Bd.look(s, x) == bd_look(s, x) : Bd.St & Bd.Seen}

# The step against the whole output: a stream of texts Rust stored whole
# reads the window and the counts of that whole text

type BdText is Data:
  BdText{n: Nat, k: Nat, o: Bool}

def bd_fst.act(r: Bd.St & Bd.Act) -> Bd.St:
  match r:
    case (s, a):
      s

# the stream after the texts es
def bd_drive(es: List<&2, BdText>, s: Bd.St) -> Bd.St:
  match es:
    case Nil{}:
      s
    case e <> rest:
      match e:
        case BdText{n, k, o}:
          bd_drive(rest, bd_fst.act(Bd.out(s, n, k, o)))

def bd_sum_n(es: List<&2, BdText>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case BdText{n, k, o}:
          Nat.add(n, bd_sum_n(rest))

def bd_sum_k(es: List<&2, BdText>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case BdText{n, k, o}:
          Nat.add(k, bd_sum_k(rest))

# whether the output ends inside a line: as its last text
def bd_last(es: List<&2, BdText>, d: Bool) -> Bool:
  match es:
    case Nil{}:
      d
    case e <> rest:
      match e:
        case BdText{n, k, o}:
          bd_last(rest, o)

def bd_seen_slice(r: Bd.St & Bd.Seen) -> Bd.Slice:
  match r:
    case (s, v):
      match v:
        case Bd.Seen{sp, b, l, cut}:
          Bd.Slice{sp, b, l}

# LAW bound_steps_whole: the texts of an output fed one at a time, then the whole output's text (its bytes those of the texts, its lines their newlines and an open last line) sent as stored: the window and the counts read are the whole text's slice
# EXCLUDES: a stream whose counts drift from the output it was fed, a look
#   that reads the stored text's counts in place of the stream's
law bound_steps_whole:
  for +c: Bd.Cap
  for +es: List<&2, BdText>
  for +x: Bd.Body
  for bytes: {bd_total(bd_body_lines(x)) == bd_sum_n(es) : Nat}
  for lines: {List.length(&2, Nat, bd_body_lines(x)) == bd_lines(bd_sum_k(es), bd_last(es, False{})) : Nat}
  {bd_seen_slice(Bd.look(bd_drive(es, Bd.St{c, 0n, 0n, False{}, 0n}), x)) == Bd.slice(c, x) : Bd.Slice}

# (S2) The compiled entry
# -----------------------
# bend/ffi_bound.bend, for every request and event that fits the wire:
# its replies are the model's answers, spelled by the spec spellers here
# (bd_spell over the Wr primitives, whose round trips laws/wire.bend
# proves). Requests and replies are lists of Nats: a Bool is 0 or 1.

# the whole input or reply of a list of Nats
def bd_spell(+xs: List<&2, Nat>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, "")

# a list that fits the wire: its count and every item
def bd_fits(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

def bd_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# a cap: [bytes, lines, tail]
def bd_cap(c: Bd.Cap, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case Bd.Cap{b, k, t}:
      b <> k <> bd_bit(t) <> rest

# a body: [open, head, tail, margin, line ...]
def bd_body(x: Bd.Body) -> List<&2, Nat>:
  match x:
    case Bd.Body{xs, o, hc, tc, mc}:
      bd_bit(o) <> hc <> tc <> mc <> xs

def bd_span.nats(s: Bd.Span, rest: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case Bd.Span{f, t}:
      f <> t <> rest

# the reply to a slice: [from, to, bytes, lines]
def bd_slice.nats(s: Bd.Slice) -> List<&2, Nat>:
  match s:
    case Bd.Slice{sp, b, l}:
      bd_span.nats(sp, [b, l])

# the reply to a notice: [] or [at]: 0 its end, 1 its start
def bd_notice.nats(m: Maybe<&2, Bd.At>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{a}:
      match a:
        case Bd.AtEnd{}:
          [0n]
        case Bd.AtStart{}:
          [1n]

# the reply to a text: [0 drop | 1 store | 2 store, then send the stored text]
def bd_act(a: Bd.Act) -> Nat:
  match a:
    case Bd.Drop{}:
      0n
    case Bd.Store{}:
      1n
    case Bd.Trim{}:
      2n

# the reply to the stored text: [from, to, bytes, lines, cut]
def bd_seen.nats(v: Bd.Seen) -> List<&2, Nat>:
  match v:
    case Bd.Seen{sp, b, l, cut}:
      bd_span.nats(sp, [b, l, cut])

def bd_snd.act(r: Bd.St & Bd.Act) -> Bd.Act:
  match r:
    case (s, a):
      a

def bd_fst.skip(r: Bd.St & Bool) -> Bd.St:
  match r:
    case (s, a):
      s

def bd_snd.skip(r: Bd.St & Bool) -> Bool:
  match r:
    case (s, a):
      a

def bd_fst.look(r: Bd.St & Bd.Seen) -> Bd.St:
  match r:
    case (s, a):
      s

def bd_snd.look(r: Bd.St & Bd.Seen) -> Bd.Seen:
  match r:
    case (s, a):
      a

# LAW bound_ffi_slice: a slice request [0, cap ..., body ...] answers the model's slice of the body: where its window lies, the bytes and lines it drops
# EXCLUDES: a window of another cap or body, fields swapped or misread
law bound_ffi_slice:
  for +c: Bd.Cap
  for +x: Bd.Body
  for h: {bd_fits(0n <> bd_cap(c, bd_body(x))) == True{} : Bool}
  {FBd.ffi(bd_spell(0n <> bd_cap(c, bd_body(x)))) == bd_spell(bd_slice.nats(Bd.slice(c, x))) : String}

# LAW bound_ffi_notice: a notice request [1, tail, dropped, still] answers the model's notice
# EXCLUDES: a notice of another retention, count or holding
law bound_ffi_notice:
  for +t: Bool
  for +d: Nat
  for +s: Bool
  for h: {bd_fits([1n, bd_bit(t), d, bd_bit(s)]) == True{} : Bool}
  {FBd.ffi(bd_spell([1n, bd_bit(t), d, bd_bit(s)])) == bd_spell(bd_notice.nats(Bd.notice(t, d, s))) : String}

# the list s spells, whole
def bd_whole.end(done: Bool, xs: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match done:
    case True{}:
      Some{xs}
    case False{}:
      None{}

def bd_whole(r: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case Wr.Got{xs, rest}:
      bd_whole.end(Wr.end(rest), xs)
    case Wr.Bad{}:
      None{}

def bd_read(s: String) -> Maybe<&2, List<&2, Nat>>:
  bd_whole(Wr.get_list(~Nat, ~Wr.get_nat, s))

# the third item of xs (a cap's tail, a notice's still) is a Bool
def bd_third_bit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      match r:
        case Nil{}:
          False{}
        case b <> q:
          match q:
            case Nil{}:
              False{}
            case c <> z:
              Nat.is_le(c, 1n)

def bd_first_bit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      Nat.is_le(a, 1n)

def bd_len_is(xs: List<&2, Nat>, n: Nat) -> Bool:
  Nat.is_eq(List.length(&2, Nat, xs), n)

# a body's shape: [open 0 or 1, head, tail, margin, line ...]
def bd_body_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case o <> a:
      match a:
        case Nil{}:
          False{}
        case h <> b:
          match b:
            case Nil{}:
              False{}
            case t <> c:
              match c:
                case Nil{}:
                  False{}
                case m <> ls:
                  Nat.is_le(o, 1n)

# a cap then a body: [bytes, lines, tail 0 or 1, body ...]
def bd_cap_body_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case b <> r:
      match r:
        case Nil{}:
          False{}
        case l <> q:
          match q:
            case Nil{}:
              False{}
            case t <> rest:
              Bool.and(Nat.is_le(t, 1n), bd_body_ok(rest))

# a notice: [tail 0 or 1, dropped, still 0 or 1]
def bd_notice_ok(+xs: List<&2, Nat>) -> Bool:
  Bool.and(bd_len_is(xs, 3n), Bool.and(bd_first_bit(xs), bd_third_bit(xs)))

# the shape of a call: [0, cap ..., body ...] or [1, tail, dropped, still]
def bd_call_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +tag <> +t:
      Bool.or(Bool.and(Nat.is_eq(tag, 0n), bd_cap_body_ok(t)), Bool.and(Nat.is_eq(tag, 1n), bd_notice_ok(t)))

def bd_call_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      bd_call_ok(xs)

# LAW bound_ffi_malformed_exact: any input that is not exactly a call's list answers exactly the error form 'E bound: malformed request'
# EXCLUDES: a default window or notice for bad input, input left over
#   read, a Bool of 2 or an unknown tag taken for a call
law bound_ffi_malformed_exact:
  for +s: String
  for no: {bd_call_of(bd_read(s)) == False{} : Bool}
  {FBd.ffi(s) == Wr.err("bound: malformed request") : String}

# LAW bound_open_answers: an open [bytes, lines, tail] starts the output under that cap with nothing come and nothing stored; the reply says whether it takes skipped output (a tail does)
# EXCLUDES: a cap read wrong, a stream that starts with counts, a head
#   that takes skips or a tail that refuses them
law bound_open_answers:
  for +c: Bd.Cap
  for h: {bd_fits(bd_cap(c, Nil{})) == True{} : Bool}
  {FBd.open(bd_spell(bd_cap(c, Nil{}))) == (FBd.Run{Bd.St{c, 0n, 0n, False{}, 0n}}, bd_spell([bd_bit(bd_cap_tail(c))])) : FBd.St & String}

def bd_open_ok(+xs: List<&2, Nat>) -> Bool:
  Bool.and(bd_len_is(xs, 3n), bd_third_bit(xs))

def bd_open_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      bd_open_ok(xs)

# LAW bound_open_refuses: any other open opens the refused state, with exactly the error form 'E bound: malformed open'
# EXCLUDES: a stream on a default cap for a bad open
law bound_open_refuses:
  for +s: String
  for no: {bd_open_of(bd_read(s)) == False{} : Bool}
  {FBd.open(s) == (FBd.Shut{}, Wr.err("bound: malformed open")) : FBd.St & String}

# LAW bound_shut_refuses: the refused state answers every event with exactly the error form 'E bound: the open was refused'
# EXCLUDES: a stream run on a made-up cap after a refused open
law bound_shut_refuses:
  for s: String
  {FBd.step(FBd.Shut{}, s) == (FBd.Shut{}, Wr.err("bound: the open was refused")) : FBd.St & String}

# LAW bound_step_out: a text [0, bytes, newlines, open] answers the model's decision on it [0 drop | 1 store | 2 trim], and the stream goes on as the model's
# EXCLUDES: a text read with its counts swapped, a decision or a stream
#   other than the model's
law bound_step_out:
  for +s: Bd.St
  for +n: Nat
  for +k: Nat
  for +o: Bool
  for h: {bd_fits([0n, n, k, bd_bit(o)]) == True{} : Bool}
  {FBd.step(FBd.Run{s}, bd_spell([0n, n, k, bd_bit(o)])) == (FBd.Run{bd_fst.act(Bd.out(s, n, k, o))}, bd_spell([bd_act(bd_snd.act(Bd.out(s, n, k, o)))])) : FBd.St & String}

# LAW bound_step_skip: a skip [1, bytes, newlines, open] answers whether to clear the stored text, and the stream goes on as the model's
# EXCLUDES: a skip read as a text, a clear the model does not give
law bound_step_skip:
  for +s: Bd.St
  for +n: Nat
  for +k: Nat
  for +o: Bool
  for h: {bd_fits([1n, n, k, bd_bit(o)]) == True{} : Bool}
  {FBd.step(FBd.Run{s}, bd_spell([1n, n, k, bd_bit(o)])) == (FBd.Run{bd_fst.skip(Bd.skip(s, n, k, o))}, bd_spell([bd_bit(bd_snd.skip(Bd.skip(s, n, k, o)))])) : FBd.St & String}

# LAW bound_step_look: the stored text [2, body ...] answers the model's look [from, to, bytes, lines, cut], and the stream goes on as the model's
# EXCLUDES: a window of another body, a cut Rust would misplace
law bound_step_look:
  for +s: Bd.St
  for +x: Bd.Body
  for h: {bd_fits(2n <> bd_body(x)) == True{} : Bool}
  {FBd.step(FBd.Run{s}, bd_spell(2n <> bd_body(x))) == (FBd.Run{bd_fst.look(Bd.look(s, x))}, bd_spell(bd_seen.nats(bd_snd.look(Bd.look(s, x))))) : FBd.St & String}

# the shape of an event: [0 or 1, bytes, newlines, open 0 or 1] or [2, body ...]
def bd_event_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +tag <> +t:
      Bool.or(Bool.and(Nat.is_le(tag, 1n), Bool.and(bd_len_is(t, 3n), bd_third_bit(t))), Bool.and(Nat.is_eq(tag, 2n), bd_body_ok(t)))

def bd_event_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      bd_event_ok(xs)

# LAW bound_step_refuses: an event that is not exactly an event's list answers exactly the error form 'E bound: malformed event' and keeps the stream
# EXCLUDES: a guessed event, a stream changed by a bad event
law bound_step_refuses:
  for +s: Bd.St
  for +x: String
  for no: {bd_event_of(bd_read(x)) == False{} : Bool}
  {FBd.step(FBd.Run{s}, x) == (FBd.Run{s}, Wr.err("bound: malformed event")) : FBd.St & String}

# LAW bound_entry_example: anchor: the bytes Rust sends and reads: a head of 100 bytes and 10 lines stores a text after 3 bytes and drops one after 101; a tail of 100 bytes stores up to 208 bytes and trims at 209; the head and tail windows of "ab\ncde\n" under 5 bytes; a notice at the start; none for an output the result no longer holds; a tail of 5 bytes opens taking skips, stores a text, trims after one past 18 stored bytes, and reads its stored "ab\n" and 30 bytes: the last 5, 28 bytes and 1 line dropped, the stored text cut to its last 6; a Bool of 2 and input left over are refused
# EXCLUDES: a codec that reads other fields or writes another reply
law bound_entry_example:
  {[FBd.ffi("10,0,5,10,0,0,5,4,7,3,4,"), FBd.ffi("10,0,5,10,1,0,5,4,7,3,4,"), FBd.ffi("4,1,1,4,1,"), FBd.ffi("4,1,0,4,0,"), FBd.ffi("4,1,2,4,1,"), FBd.ffi("4,1,1,4,1,x")] == ["4,0,3,4,1,", "4,3,7,3,1,", "1,1,", "0,", Wr.err("bound: malformed request"), Wr.err("bound: malformed request")] : List<&2, String>} & {FBd.open("3,5,10,1,") == (FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 0n, 0n, False{}, 0n}}, "1,1,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 0n, 0n, False{}, 0n}}, "4,0,3,1,0,") == (FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 3n, 1n, False{}, 3n}}, "1,1,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 3n, 1n, False{}, 3n}}, "4,0,30,0,1,") == (FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 33n, 1n, True{}, 33n}}, "1,2,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 33n, 1n, True{}, 33n}}, "7,2,1,5,5,6,3,30,") == (FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 33n, 1n, True{}, 6n}}, "5,28,33,28,1,27,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{100n, 10n, False{}}, 3n, 1n, False{}, 3n}}, "4,0,3,1,0,") == (FBd.Run{Bd.St{Bd.Cap{100n, 10n, False{}}, 6n, 2n, False{}, 6n}}, "1,1,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{100n, 10n, False{}}, 101n, 2n, False{}, 101n}}, "4,0,3,1,0,") == (FBd.Run{Bd.St{Bd.Cap{100n, 10n, False{}}, 104n, 3n, False{}, 101n}}, "1,0,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 0n, 0n, False{}, 0n}}, "4,0,9,1,0,") == (FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 9n, 1n, False{}, 9n}}, "1,1,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 200n, 0n, False{}, 200n}}, "4,0,8,0,0,") == (FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 208n, 0n, False{}, 208n}}, "1,1,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 200n, 0n, False{}, 200n}}, "4,0,9,0,0,") == (FBd.Run{Bd.St{Bd.Cap{100n, 10n, True{}}, 209n, 0n, False{}, 209n}}, "1,2,") : FBd.St & String} & {FBd.step(FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 0n, 0n, False{}, 0n}}, "4,0,3,1,2,") == (FBd.Run{Bd.St{Bd.Cap{5n, 10n, True{}}, 0n, 0n, False{}, 0n}}, Wr.err("bound: malformed event")) : FBd.St & String}
