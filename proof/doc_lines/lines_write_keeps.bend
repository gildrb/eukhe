# eukhe: the proof of LAW lines_write_keeps

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

# the first ending scanned from lines with a `\r` just before them: CRLF
# when the first line is empty (its `\n` comes right after that `\r`)
def lwk.cr(ls: Dl.Lines) -> Maybe<&2, Dl.End>:
  match ls:
    case Dl.More{t, e, r}:
      match t:
        case Nil{}:
          Some{Dl.CrLf{}}
        case h <> tt:
          Some{e}
    case Dl.Last{t}:
      None{}

# the first ending scanned from lines (r: a `\r` came just before them)
def lwk.at(r: Bool, ls: Dl.Lines) -> Maybe<&2, Dl.End>:
  match r:
    case True{}:
      lwk.cr(ls)
    case False{}:
      Dl.first_end(Dl.proj.lines(Dl.pieces(ls)))

# a content byte before the lines forgets the pending `\r`
def lwk.push(r: Bool, ls: Dl.Lines) -> {lwk.at(r, Dl.push(Dl.A{}, ls)) == lwk.at(False{}, ls) : Maybe<&2, Dl.End>}:
  match r:
    case True{}:
      match ls:
        case Dl.More{t, e, rs}:
          {==}
        case Dl.Last{t}:
          {==}
    case False{}:
      match ls:
        case Dl.More{t, e, rs}:
          {==}
        case Dl.Last{t}:
          {==}

# a `\r` before the lines is the pending `\r` of what follows
def lwk.cons_r(r: Bool, ls: Dl.Lines) -> {lwk.at(r, Dl.cons(Dl.R{}, ls)) == lwk.at(True{}, ls) : Maybe<&2, Dl.End>}:
  match r:
    case True{}:
      match ls:
        case Dl.More{t, e, rs}:
          match t:
            case Nil{}:
              match e:
                case Dl.Lf{}:
                  {==}
                case Dl.CrLf{}:
                  {==}
            case h <> tt:
              {==}
        case Dl.Last{t}:
          {==}
    case False{}:
      match ls:
        case Dl.More{t, e, rs}:
          match t:
            case Nil{}:
              match e:
                case Dl.Lf{}:
                  {==}
                case Dl.CrLf{}:
                  {==}
            case h <> tt:
              {==}
        case Dl.Last{t}:
          {==}

# the first ending of the projected lines of a body is its first ending,
# scanned byte by byte (r: a `\r` came just before the body)
def lwk.first(bs: List<&2, Dl.B>, r: Bool) -> {lwk.at(r, Dl.split(bs)) == DocLines.lines.FirstEnd(bs, r) : Maybe<&2, Dl.End>}:
  match bs:
    case Nil{}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case b <> +rest:
      match b:
        case Dl.A{}:
          %lwk.first(rest, False{}) : {lwk.at(r, Dl.push(Dl.A{}, Dl.split(rest))) == _ : Maybe<&2, Dl.End>}
          lwk.push(r, Dl.split(rest))
        case Dl.R{}:
          %lwk.first(rest, True{}) : {lwk.at(r, Dl.cons(Dl.R{}, Dl.split(rest))) == _ : Maybe<&2, Dl.End>}
          lwk.cons_r(r, Dl.split(rest))
        case Dl.N{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}

# the decision over two first endings is the law's
def lwk.kept(b: Bool, k: Maybe<&2, Dl.End>, a: Maybe<&2, Dl.End>) -> {Dl.Kept{b, Dl.or_lf(k), Dl.warn(k, a)} == Dl.Kept{b, DocLines.lines.OrLf(k), DocLines.lines.Warn(k, a)} : Dl.Kept}:
  match k:
    case None{}:
      {==}
    case Some{e}:
      match e:
        case Dl.Lf{}:
          match a:
            case None{}:
              {==}
            case Some{f}:
              match f:
                case Dl.Lf{}:
                  {==}
                case Dl.CrLf{}:
                  {==}
        case Dl.CrLf{}:
          match a:
            case None{}:
              {==}
            case Some{f}:
              match f:
                case Dl.Lf{}:
                  {==}
                case Dl.CrLf{}:
                  {==}

def DocLines.lines_write_keeps(b1, bs1, b2, bs2):
  %lwk.first(bs1, False{}) : {Dl.write(Dl.proj(Dl.Doc{b1, bs1}), Dl.proj(Dl.Doc{b2, bs2})) == Dl.Kept{b1, DocLines.lines.OrLf(_), DocLines.lines.Warn(_, DocLines.lines.FirstEnd(bs2, False{}))} : Dl.Kept}
  %lwk.first(bs2, False{}) : {Dl.write(Dl.proj(Dl.Doc{b1, bs1}), Dl.proj(Dl.Doc{b2, bs2})) == Dl.Kept{b1, DocLines.lines.OrLf(lwk.at(False{}, Dl.split(bs1))), DocLines.lines.Warn(lwk.at(False{}, Dl.split(bs1)), _)} : Dl.Kept}
  lwk.kept(b1, lwk.at(False{}, Dl.split(bs1)), lwk.at(False{}, Dl.split(bs2)))
