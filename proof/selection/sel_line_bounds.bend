# eukhe: the proof of LAW sel_line_bounds

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# The third press counts 3 (LS.ls.clicks: next(2)) and picks the row by
# its width; the model folds the width from column 0 (slb.width: the fold
# from column c is the spec's sum plus c).

def slb.width(gs: List<&2, Nat>, +c: Nat) -> {M.width(gs, c) == Nat.add(Selection.sl_width(gs), c) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          Equal.trans(Nat, M.width(rest, 1n+c), Nat.add(Selection.sl_width(rest), 1n+c), 1n+Nat.add(Selection.sl_width(rest), c),
            slb.width(rest, 1n+c), LS.ls.add_succ(Selection.sl_width(rest), c))
        case 1n++p:
          +W = Selection.sl_width(rest)
          %Equal.sym(Nat, M.width(rest, 1n+Nat.add(p, c)), Nat.add(W, 1n+Nat.add(p, c)), slb.width(rest, 1n+Nat.add(p, c))) : {_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %Equal.sym(Nat, Nat.add(W, 1n+Nat.add(p, c)), 1n+Nat.add(W, Nat.add(p, c)), LS.ls.add_succ(W, Nat.add(p, c))) : {_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %LS.ls.add_assoc(W, p, c) : {1n+_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %LS.ls.add_comm(p, W) : {1n+Nat.add(_, c) == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          {==}

def slb.fin(w: Nat, +r: Nat, +x: Nat, t: Nat) -> {M.press.go(M.line.of(w, r, x), M.Click{M.Cell{r, x}, t, 3n}) == Selection.sl_pressed(Selection.sl_line.k(w, r), M.Cell{r, x}, t, 3n) : M.Res}:
  match w:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Selection.sel_line_bounds(m, at, t1, t2, gs, near):
  match at:
    case M.Cell{+r, +x}:
      %Equal.sym(Nat, M.clicks(Some{M.Click{M.Cell{r, x}, t1, 2n}}, M.Cell{r, x}, t2), 3n, LS.ls.clicks(r, x, t1, t2, 2n, near)) : {M.press.go(M.press.mode(_, M.Cell{r, x}, gs), M.Click{M.Cell{r, x}, t2, _}) == Selection.sl_pressed(Selection.sl_line(gs, M.Cell{r, x}), M.Cell{r, x}, t2, 3n) : M.Res}
      %Equal.sym(Nat, M.width(gs, 0n), Selection.sl_width(gs), Equal.trans(Nat, M.width(gs, 0n), Nat.add(Selection.sl_width(gs), 0n), Selection.sl_width(gs), slb.width(gs, 0n), LS.ls.add_zero(Selection.sl_width(gs)))) : {M.press.go(M.line.of(_, r, x), M.Click{M.Cell{r, x}, t2, 3n}) == Selection.sl_pressed(Selection.sl_line(gs, M.Cell{r, x}), M.Cell{r, x}, t2, 3n) : M.Res}
      slb.fin(Selection.sl_width(gs), r, x, t2)
