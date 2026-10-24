# eukhe: the proof of LAW sel_word_bounds

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# The second press counts 2 (LS.ls.clicks: next(1)) and picks M.word at
# the press's column. The model walks the glyphs once, keeping the column
# its current run started at; the spec cuts the row into runs and finds
# the one that covers the column. swb.go walks both together:
# - before a run (cur None) the model's run start is the column;
# - inside a run (cur Some{s, e}) the model's run start is s and the run
#   so far ends at e, the column before;
# the column x is never left of the walk. A blank at x: no word (swb.miss:
# every later run starts right of x); a glyph that reaches x: the run goes
# on to M.word.last (swb.found).

def swb.found(gs: List<&2, Nat>, +s: Nat, +e: Nat, +x: Nat, +hs: {Nat.is_le(s, x) == True{} : Bool}, +hx: {Nat.is_le(x, e) == True{} : Bool}) -> {Selection.sl_find(Selection.sl_runs(gs, 1n+e, Some{Selection.SlRun{s, e}}), x) == Some{Selection.SlRun{s, M.word.last(gs, e)}} : Maybe<&2, Selection.SlRun>}:
  match gs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_le(s, x), True{}, hs) : {Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, None{}) == Some{Selection.SlRun{s, e}} : Maybe<&2, Selection.SlRun>}
      %Equal.sym(Bool, Nat.is_le(x, e), True{}, hx) : {Selection.sl_find.k(_, Selection.SlRun{s, e}, None{}) == Some{Selection.SlRun{s, e}} : Maybe<&2, Selection.SlRun>}
      {==}
    case Con{g, rest}:
      match g:
        case 0n:
          %Equal.sym(Bool, Nat.is_le(s, x), True{}, hs) : {Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, Selection.sl_find(Selection.sl_runs(rest, 2n+e, None{}), x)) == Some{Selection.SlRun{s, e}} : Maybe<&2, Selection.SlRun>}
          %Equal.sym(Bool, Nat.is_le(x, e), True{}, hx) : {Selection.sl_find.k(_, Selection.SlRun{s, e}, Selection.sl_find(Selection.sl_runs(rest, 2n+e, None{}), x)) == Some{Selection.SlRun{s, e}} : Maybe<&2, Selection.SlRun>}
          {==}
        case 1n++p:
          swb.found(rest, s, Nat.add(p, 1n+e), x, hs, LS.ls.le_trans(x, e, Nat.add(p, 1n+e), hx, LS.ls.le_trans(e, 1n+e, Nat.add(p, 1n+e), LS.ls.le_succ(e), LS.ls.le_add(p, 1n+e))))

# x is left of the open run's start
def swb.below(cur: Maybe<&2, Selection.SlRun>, x: Nat) -> Type:
  match cur:
    case None{}:
      Unit
    case Some{w}:
      match w:
        case Selection.SlRun{s, e}:
          {Nat.is_lt(x, s) == True{} : Bool}

def swb.miss(gs: List<&2, Nat>, +c: Nat, cur: Maybe<&2, Selection.SlRun>, +x: Nat, +hc: {Nat.is_lt(x, c) == True{} : Bool}, hb: swb.below(cur, x)) -> {Selection.sl_find(Selection.sl_runs(gs, c, cur), x) == None{} : Maybe<&2, Selection.SlRun>}:
  match gs:
    case Nil{}:
      match cur:
        case None{}:
          {==}
        case Some{w}:
          match w:
            case Selection.SlRun{+s, e}:
              %Equal.sym(Bool, Nat.is_le(s, x), False{}, LS.ls.lt_not_le(x, s, hb)) : {Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, None{}) == None{} : Maybe<&2, Selection.SlRun>}
              {==}
    case Con{g, rest}:
      match g:
        case 0n:
          match cur:
            case None{}:
              swb.miss(rest, 1n+c, None{}, x, LS.ls.lt_succ(x, c, hc), Unit{})
            case Some{w}:
              match w:
                case Selection.SlRun{+s, e}:
                  %Equal.sym(Bool, Nat.is_le(s, x), False{}, LS.ls.lt_not_le(x, s, hb)) : {Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, Selection.sl_find(Selection.sl_runs(rest, 1n+c, None{}), x)) == None{} : Maybe<&2, Selection.SlRun>}
                  swb.miss(rest, 1n+c, None{}, x, LS.ls.lt_succ(x, c, hc), Unit{})
        case 1n++p:
          match cur:
            case None{}:
              swb.miss(rest, 1n+Nat.add(p, c), Some{Selection.SlRun{c, Nat.add(p, c)}}, x, LS.ls.lt_succ(x, Nat.add(p, c), LS.ls.lt_le(x, c, Nat.add(p, c), hc, LS.ls.le_add(p, c))), hc)
            case Some{w}:
              match w:
                case Selection.SlRun{s, e}:
                  swb.miss(rest, 1n+Nat.add(p, c), Some{Selection.SlRun{s, Nat.add(p, c)}}, x, LS.ls.lt_succ(x, Nat.add(p, c), LS.ls.lt_le(x, c, Nat.add(p, c), hc, LS.ls.le_add(p, c))), hb)

# what swb.go proves of gs: before a run, from column c; inside a run
# started at s whose last cell so far is e
def swb.stmt(gs: List<&2, Nat>, cur: Maybe<&2, Selection.SlRun>, +c: Nat, +x: Nat, +r: Nat) -> Type:
  match cur:
    case None{}:
      {Nat.is_le(c, x) == True{} : Bool} -> {M.word(gs, c, c, x, r) == Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(gs, c, None{}), x), r) : Maybe<&2, M.Rng>}
    case Some{w}:
      match w:
        case Selection.SlRun{+s, +e}:
          {Nat.is_le(s, x) == True{} : Bool} -> {Nat.is_le(1n+e, x) == True{} : Bool} -> {M.word(gs, 1n+e, s, x, r) == Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(gs, 1n+e, Some{Selection.SlRun{s, e}}), x), r) : Maybe<&2, M.Rng>}

# a blank at column c, the walk before a run
def swb.blank(b: Bool, +c: Nat, +x: Nat, +r: Nat, rest: List<&2, Nat>, eb: {Nat.is_le(x, c) == b : Bool}, ih: swb.stmt(rest, None{}, 1n+c, x, r)) -> {M.word.blank(b, M.word(rest, 1n+c, 1n+c, x, r)) == Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(rest, 1n+c, None{}), x), r) : Maybe<&2, M.Rng>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Selection.SlRun>, Selection.sl_find(Selection.sl_runs(rest, 1n+c, None{}), x), None{}, swb.miss(rest, 1n+c, None{}, x, LS.ls.le_lt_succ(x, c, eb), Unit{})) : {None{} == Selection.sl_word.k(_, r) : Maybe<&2, M.Rng>}
      {==}
    case False{}:
      ih(LS.ls.nle_lt(x, c, eb))

# a glyph whose last cell is e, in a run started at s
def swb.glyph(b: Bool, +s: Nat, +e: Nat, +x: Nat, +r: Nat, +rest: List<&2, Nat>, eb: {Nat.is_le(x, e) == b : Bool}, +hs: {Nat.is_le(s, x) == True{} : Bool}, ih: swb.stmt(rest, Some{Selection.SlRun{s, e}}, 0n, x, r)) -> {M.word.glyph(b, r, s, rest, e, M.word(rest, 1n+e, s, x, r)) == Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(rest, 1n+e, Some{Selection.SlRun{s, e}}), x), r) : Maybe<&2, M.Rng>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Selection.SlRun>, Selection.sl_find(Selection.sl_runs(rest, 1n+e, Some{Selection.SlRun{s, e}}), x), Some{Selection.SlRun{s, M.word.last(rest, e)}}, swb.found(rest, s, e, x, hs, eb)) : {Some{M.Rng{M.Cell{r, s}, M.Cell{r, M.word.last(rest, e)}}} == Selection.sl_word.k(_, r) : Maybe<&2, M.Rng>}
      {==}
    case False{}:
      ih(hs, LS.ls.nle_lt(x, e, eb))

def swb.go(gs: List<&2, Nat>, cur: Maybe<&2, Selection.SlRun>, +c: Nat, +x: Nat, +r: Nat) -> swb.stmt(gs, cur, c, x, r):
  match gs:
    case Nil{}:
      match cur:
        case None{}:
          hc => {==}
        case Some{w}:
          match w:
            case Selection.SlRun{+s, +e}:
              hs => hc =>
                %Equal.sym(Bool, Nat.is_le(s, x), True{}, hs) : {None{} == Selection.sl_word.k(Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, None{}), r) : Maybe<&2, M.Rng>}
                %Equal.sym(Bool, Nat.is_le(x, e), False{}, LS.ls.succ_le_nle(e, x, hc)) : {None{} == Selection.sl_word.k(Selection.sl_find.k(_, Selection.SlRun{s, e}, None{}), r) : Maybe<&2, M.Rng>}
                {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          match cur:
            case None{}:
              hc => swb.blank(Nat.is_le(x, c), c, x, r, rest, {==}, swb.go(rest, None{}, 1n+c, x, r))
            case Some{w}:
              match w:
                case Selection.SlRun{+s, +e}:
                  hs => hc =>
                    %Equal.sym(Bool, Nat.is_le(s, x), True{}, hs) : {M.word.blank(Nat.is_le(x, 1n+e), M.word(rest, 2n+e, 2n+e, x, r)) == Selection.sl_word.k(Selection.sl_find.k(Bool.and(_, Nat.is_le(x, e)), Selection.SlRun{s, e}, Selection.sl_find(Selection.sl_runs(rest, 2n+e, None{}), x)), r) : Maybe<&2, M.Rng>}
                    %Equal.sym(Bool, Nat.is_le(x, e), False{}, LS.ls.succ_le_nle(e, x, hc)) : {M.word.blank(Nat.is_le(x, 1n+e), M.word(rest, 2n+e, 2n+e, x, r)) == Selection.sl_word.k(Selection.sl_find.k(_, Selection.SlRun{s, e}, Selection.sl_find(Selection.sl_runs(rest, 2n+e, None{}), x)), r) : Maybe<&2, M.Rng>}
                    swb.blank(Nat.is_le(x, 1n+e), 1n+e, x, r, rest, {==}, swb.go(rest, None{}, 2n+e, x, r))
        case 1n++p:
          match cur:
            case None{}:
              hc => swb.glyph(Nat.is_le(x, Nat.add(p, c)), c, Nat.add(p, c), x, r, rest, {==}, hc, swb.go(rest, Some{Selection.SlRun{c, Nat.add(p, c)}}, 0n, x, r))
            case Some{w}:
              match w:
                case Selection.SlRun{+s, +e}:
                  hs => hc => swb.glyph(Nat.is_le(x, Nat.add(p, 1n+e)), s, Nat.add(p, 1n+e), x, r, rest, {==}, hs, swb.go(rest, Some{Selection.SlRun{s, Nat.add(p, 1n+e)}}, 0n, x, r))

def swb.fin(m: Maybe<&2, M.Rng>, +r: Nat, +x: Nat, t: Nat) -> {M.press.go(M.picked_or(m, M.Cell{r, x}), M.Click{M.Cell{r, x}, t, 2n}) == Selection.sl_pressed(m, M.Cell{r, x}, t, 2n) : M.Res}:
  match m:
    case None{}:
      {==}
    case Some{g}:
      {==}

def Selection.sel_word_bounds(m, at, t1, t2, gs, near):
  match at:
    case M.Cell{+r, +x}:
      %Equal.sym(Nat, M.clicks(Some{M.Click{M.Cell{r, x}, t1, 1n}}, M.Cell{r, x}, t2), 2n, LS.ls.clicks(r, x, t1, t2, 1n, near)) : {M.press.go(M.press.mode(_, M.Cell{r, x}, gs), M.Click{M.Cell{r, x}, t2, _}) == Selection.sl_pressed(Selection.sl_word(gs, M.Cell{r, x}), M.Cell{r, x}, t2, 2n) : M.Res}
      %Equal.sym(Maybe<&2, M.Rng>, M.word(gs, 0n, 0n, x, r), Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(gs, 0n, None{}), x), r), swb.go(gs, None{}, 0n, x, r)(LS.ls.le_zero(x))) : {M.press.go(M.picked_or(_, M.Cell{r, x}), M.Click{M.Cell{r, x}, t2, 2n}) == Selection.sl_pressed(Selection.sl_word(gs, M.Cell{r, x}), M.Cell{r, x}, t2, 2n) : M.Res}
      swb.fin(Selection.sl_word.k(Selection.sl_find(Selection.sl_runs(gs, 0n, None{}), x), r), r, x, t2)
