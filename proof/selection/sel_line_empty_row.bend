# eukhe: the proof of LAW sel_line_empty_row
#
# The third press counts 3 (LS.ls.clicks: next(2)); an empty row ends at
# column 0, so the press picks nothing and stays pressed.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

def Selection.sel_line_empty_row(m, at, t1, t2, near):
  match at:
    case M.Cell{+r, +x}:
      %Equal.sym(Nat, M.clicks(Some{M.Click{M.Cell{r, x}, t1, 2n}}, M.Cell{r, x}, t2), 3n, LS.ls.clicks(r, x, t1, t2, 2n, near)) : {M.press.go(M.press.mode(_, M.Cell{r, x}, Nil{}), M.Click{M.Cell{r, x}, t2, _}) == Selection.sl_pressed(None{}, M.Cell{r, x}, t2, 3n) : M.Res}
      {==}
