# eukhe: lemmas of area privacy, section token: a text scrubbed, restored
# and sent (bend/privacy/token.bend) is the spec's text over the map
# (spec/harness/privacy_map.bend, M5): the code's values, fill and raw
# text are the spec's, piece by piece

import Base
import ../../../bend/privacy/token.bend as Tk
import ../../../spec/harness/privacy.bend as S
import ../../../spec/harness/privacy_map.bend as Sm
import ./map.bend as LMp
import ./text.bend as LPx

# Scrub
# -----

# the code's values of a text are the spec's
def pst.vals(xs: List<&2, Tk.Piece>) -> {Tk.vals(xs) == Sm.vals(xs) : List<&2, Tk.Val>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          pst.vals(rest)
        case Tk.Value{c, v}:
          %pst.vals(rest) : {Tk.Val{c, v} <> Tk.vals(rest) == Tk.Val{c, v} <> _ : List<&2, Tk.Val>}
          {==}

# the code's fill of a text is the spec's
def pst.fill(xs: List<&2, Tk.Piece>, +ts: List<&2, Tk.Tok>) -> {Tk.fill(xs, ts) == Sm.fill(xs, ts) : List<&2, Tk.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          %pst.fill(rest, ts) : {Tk.Txt{s} <> Tk.fill(rest, ts) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{+c, +v}:
          match ts:
            case Nil{}:
              %pst.fill(rest, Nil{}) : {Tk.Clear{c, v} <> Tk.fill(rest, Nil{}) == Tk.Clear{c, v} <> _ : List<&2, Tk.Seg>}
              {==}
            case t <> +more:
              match t:
                case Tk.Mapped{i}:
                  %pst.fill(rest, more) : {Tk.Tok{c, i} <> Tk.fill(rest, more) == Tk.Tok{c, i} <> _ : List<&2, Tk.Seg>}
                  {==}
                case Tk.OneWay{}:
                  %pst.fill(rest, more) : {Tk.Hash{c, v} <> Tk.fill(rest, more) == Tk.Hash{c, v} <> _ : List<&2, Tk.Seg>}
                  {==}

# a text filled with the tokens r is the spec's
def pst.text(+xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Tk.scrub.fill(xs, r) == Sm.text(xs, r) : Tk.Out}:
  match r:
    case Tk.Toks{m, +ts}:
      %pst.fill(xs, ts) : {Tk.Out{m, Tk.fill(xs, ts)} == Tk.Out{m, _} : Tk.Out}
      {==}

# a text scrubbed is the text filled with the stepper's tokens of its
# values
def pst.stepper(+m: Tk.Book, +xs: List<&2, Tk.Piece>) -> {Tk.scrub(m, xs) == Sm.text(xs, Tk.scrub_vals(Sm.vals(xs), m)) : Tk.Out}:
  %pst.vals(xs) : {Tk.scrub(m, xs) == Sm.text(xs, Tk.scrub_vals(_, m)) : Tk.Out}
  pst.text(xs, Tk.scrub_vals(Tk.vals(xs), m))

# from a map with no value held twice, a text scrubbed is the spec's
def pst.scrub(+m: Tk.Book, +xs: List<&2, Tk.Piece>, +ok: {Sm.book_distinct(m) == True{} : Bool}) -> {Tk.scrub(m, xs) == Sm.scrub_text(xs, m) : Tk.Out}:
  %LMp.pmp.scrub_vals(Sm.vals(xs), m, ok) : {Tk.scrub(m, xs) == Sm.text(xs, _) : Tk.Out}
  pst.stepper(m, xs)

# the map after a text the spec scrubs is the stepper's map after its
# values
def pst.text_book(-xs: List<&2, Tk.Piece>, r: Tk.Toks) -> {Sm.out_book(Sm.text(xs, r)) == Sm.toks_book(r) : Tk.Book}:
  match r:
    case Tk.Toks{m, ts}:
      {==}

# from a map with no value held twice, the map after a text again holds
# none twice
def pst.kept(+xs: List<&2, Tk.Piece>, +m: Tk.Book, +ok: {Sm.book_distinct(m) == True{} : Bool}) -> {Sm.book_distinct(Sm.out_book(Sm.scrub_text(xs, m))) == True{} : Bool}:
  +r = Sm.scrub_vals(Sm.vals(xs), m)
  %Equal.sym(Tk.Book, Sm.out_book(Sm.text(xs, r)), Sm.toks_book(r), pst.text_book(xs, r)) : {Sm.book_distinct(_) == True{} : Bool}
  LMp.pmp.dk(Sm.vals(xs), m, ok)

# Restore
# -------

def pst.rtok(+c: Tk.Class, +i: Nat, f: Maybe<&2, String>) -> {LPx.ptx.restore1.tok(c, i, f) == Sm.restore_seg.tok(c, i, f) : Tk.Seg}:
  match f:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a piece restored is the spec's
def pst.rseg(+m: Tk.Book, y: Tk.Seg) -> {LPx.ptx.restore1(m, y) == Sm.restore_seg(m, y) : Tk.Seg}:
  match y:
    case Tk.Txt{s}:
      {==}
    case Tk.Clear{c, v}:
      {==}
    case Tk.Tok{+c, +i}:
      %LMp.pmp.tok(m, c, i) : {LPx.ptx.restore1.tok(c, i, Tk.restore_tok(m, c, i)) == Sm.restore_seg.tok(c, i, _) : Tk.Seg}
      pst.rtok(c, i, Tk.restore_tok(m, c, i))
    case Tk.Hash{c, v}:
      {==}

# a text restored is the spec's
def pst.restore(+m: Tk.Book, ys: List<&2, Tk.Seg>) -> {Tk.restore(m, ys) == Sm.restore_text(ys, m) : List<&2, Tk.Seg>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      %pst.restore(m, rest) : {Tk.restore(m, y <> rest) == Sm.restore_seg(m, y) <> _ : List<&2, Tk.Seg>}
      %pst.rseg(m, y) : {Tk.restore(m, y <> rest) == _ <> Tk.restore(m, rest) : List<&2, Tk.Seg>}
      LPx.ptx.restore_cons(m, y, rest)

# Failover
# --------

# the code's raw text is the spec's
def pst.raw(xs: List<&2, Tk.Piece>) -> {Tk.raw(xs) == S.raw(xs) : List<&2, Tk.Seg>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Tk.Plain{s}:
          %pst.raw(rest) : {Tk.Txt{s} <> Tk.raw(rest) == Tk.Txt{s} <> _ : List<&2, Tk.Seg>}
          {==}
        case Tk.Value{c, v}:
          %pst.raw(rest) : {Tk.Clear{c, v} <> Tk.raw(rest) == Tk.Clear{c, v} <> _ : List<&2, Tk.Seg>}
          {==}

def pst.sc(-y: List<&2, Tk.Seg>, r: Tk.Sent) -> {Tk.send.cons(y, r) == Sm.send.cons(y, r) : Tk.Sent}:
  match r:
    case Tk.Sent{m, yss}:
      {==}

def pst.remote.k(+mm: Tk.Book, +ys: List<&2, Tk.Seg>, +rest: List<&2, Bool>, +xs: List<&2, Tk.Piece>, ih: {Tk.send(rest, mm, xs) == Sm.send(rest, mm, xs) : Tk.Sent}) -> {Tk.send.cons(ys, Tk.send(rest, mm, xs)) == Sm.send.cons(ys, Sm.send(rest, mm, xs)) : Tk.Sent}:
  %ih : {Tk.send.cons(ys, Tk.send(rest, mm, xs)) == Sm.send.cons(ys, _) : Tk.Sent}
  pst.sc(ys, Tk.send(rest, mm, xs))

# a remote attempt: its text, then the attempts after it from the map it
# left
def pst.remote(o: Tk.Out, +rest: List<&2, Bool>, +xs: List<&2, Tk.Piece>) -> {Tk.send(rest, Sm.out_book(o), xs) == Sm.send(rest, Sm.out_book(o), xs) : Tk.Sent} -> {Tk.send.cons(Tk.Out.ys(o), Tk.send(rest, Tk.Out.m(o), xs)) == Sm.send.cons(Sm.out_ys(o), Sm.send(rest, Sm.out_book(o), xs)) : Tk.Sent}:
  match o:
    case Tk.Out{+mm, +ys}:
      ih => pst.remote.k(mm, ys, rest, xs, ih)

# from a map with no value held twice, the attempts of a failover send the
# spec's texts and leave the spec's map
def pst.send(ts: List<&2, Bool>, +m: Tk.Book, +xs: List<&2, Tk.Piece>, +ok: {Sm.book_distinct(m) == True{} : Bool}) -> {Tk.send(ts, m, xs) == Sm.send(ts, m, xs) : Tk.Sent}:
  match ts:
    case Nil{}:
      {==}
    case t <> +rest:
      match t:
        case True{}:
          +o = Sm.scrub_text(xs, m)
          %Equal.sym(Tk.Out, Tk.scrub(m, xs), o, pst.scrub(m, xs, ok)) : {Tk.send.cons(Tk.Out.ys(_), Tk.send(rest, Tk.Out.m(_), xs)) == Sm.send.cons(Sm.out_ys(o), Sm.send(rest, Sm.out_book(o), xs)) : Tk.Sent}
          pst.remote(o, rest, xs)(pst.send(rest, Sm.out_book(o), xs, pst.kept(xs, m, ok)))
        case False{}:
          %pst.send(rest, m, xs, ok) : {Tk.send.cons(Tk.raw(xs), Tk.send(rest, m, xs)) == Sm.send.cons(S.raw(xs), _) : Tk.Sent}
          %pst.raw(xs) : {Tk.send.cons(Tk.raw(xs), Tk.send(rest, m, xs)) == Sm.send.cons(_, Tk.send(rest, m, xs)) : Tk.Sent}
          pst.sc(Tk.raw(xs), Tk.send(rest, m, xs))
