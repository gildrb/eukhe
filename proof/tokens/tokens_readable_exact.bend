# eukhe: the proof of LAW tokens_readable_exact
# The colors of both tones are the spec's (tokens_find_exact); the need's
# ratio is 9/2 or 3/1 by cases.

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens
import ./tokens_find_exact.bend as PTFE

def tre.of(x: Maybe<&2, Tk.Col>, y: Maybe<&2, Tk.Col>, n: Tk.Need) -> {Tk.meets(x, y, n) == Tokens.readable_spec.of(x, y, n) : Bool}:
  match x:
    case None{}:
      match y:
        case None{}:
          {==}
        case Some{b}:
          {==}
    case Some{a}:
      match a:
        case Tk.Col{xa, aa}:
          match y:
            case None{}:
              {==}
            case Some{b}:
              match b:
                case Tk.Col{yb, bb}:
                  match n:
                    case Tk.Prose{}:
                      {==}
                    case Tk.Caption{}:
                      {==}

def Tokens.tokens_readable_exact(m, p):
  match p:
    case Tk.Ink{+fg, +bg, +n}:
      %Equal.sym(Maybe<&2, Tk.Col>, Tk.find(fg, Tk.palette(m)), Tokens.find_spec(fg, Tk.palette(m)), Tokens.tokens_find_exact(fg, Tk.palette(m))) : {Tk.meets(_, Tk.find(bg, Tk.palette(m)), n) == Tokens.readable_spec(m, Tk.Ink{fg, bg, n}) : Bool}
      %Equal.sym(Maybe<&2, Tk.Col>, Tk.find(bg, Tk.palette(m)), Tokens.find_spec(bg, Tk.palette(m)), Tokens.tokens_find_exact(bg, Tk.palette(m))) : {Tk.meets(Tokens.find_spec(fg, Tk.palette(m)), _, n) == Tokens.readable_spec(m, Tk.Ink{fg, bg, n}) : Bool}
      tre.of(Tokens.find_spec(fg, Tk.palette(m)), Tokens.find_spec(bg, Tk.palette(m)), n)
