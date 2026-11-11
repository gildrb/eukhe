# eukhe: the proof of LAW tokens_ascends_exact
# Induction on the steps after the first: ascends.from compares each value
# with the one before it, as the spec does.

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tae.from(rest: List<&2, Tk.Step>, +n: String, +v: U32) -> {Tk.ascends.from(rest, v) == Tokens.ascends_spec(Tk.Step{n, v} <> rest) : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Tk.Step{+m, +w} <> +more:
      %Equal.sym(Bool, Tk.ascends.from(more, w), Tokens.ascends_spec(Tk.Step{m, w} <> more), tae.from(more, m, w)) : {Bool.and(U32.is_lt(v, w), _) == Bool.and(U32.is_lt(v, w), Tokens.ascends_spec(Tk.Step{m, w} <> more)) : Bool}
      {==}

def Tokens.tokens_ascends_exact(xs):
  match xs:
    case Nil{}:
      {==}
    case Tk.Step{n, v} <> rest:
      tae.from(rest, n, v)
