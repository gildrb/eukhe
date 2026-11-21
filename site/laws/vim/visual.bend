# eukhe.com's Neovim: the laws of yanking (R9)
# =============================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ../../vim/visual.bend as Vi
import ./base.bend as Laws

# Laws
# ----

# LAW yank_line: after any events and an Esc, Y on a file copies the
# cursor's line and its line break (R9).
law yank_line:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.yank_line(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW yank_char: after any events and an Esc, v then y on a file copies the
# character under the cursor, or on an empty line its line break (R9).
law yank_char:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.yank_char(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW vis_label: after any events, in visual mode on a screen of at least
# 17 columns, the command line shows "-- VISUAL --" or "-- VISUAL LINE --"
# (R10).
law vis_label:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.vis_label(Laws.Spec.run(fs, rows, cols, evs)) == True{} : Bool}

# LAW v_v: after any events and an Esc, v then v on a file leaves visual
# mode: nothing is selected (R10).
law v_v:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.v_v(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW V_v: after any events and an Esc, V then v on a file selects by
# characters (R10).
law V_v:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.V_v(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW v_V: after any events and an Esc, v then V on a file selects by
# lines (R10).
law v_V:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.v_V(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW V_V: after any events and an Esc, V then V on a file leaves visual
# mode: nothing is selected (R10).
law V_V:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.V_V(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW v_minus: after any events and an Esc, v then - on a file leaves
# visual mode: Oil shows the folder and nothing is selected (R10).
law v_minus:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.v_minus(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW v_j: after any events and an Esc, v then j on a file stays in visual
# mode (R10).
law v_j:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.v_j(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW yank_either_way: what a selection holds is the same whichever end it
# started from: v then a motion back copies what the motion forward and v
# would (R9).
law yank_either_way:
  for k: T.Vis
  for ls: List<&2, String>
  for a: T.Pos
  for b: T.Pos
  {Vi.Vis.text(k, ls, a, b) == Vi.Vis.text(k, ls, b, a) : String}

# LAW sel_cells: after any events, in visual mode, a cell of a text row is
# shown selected exactly when its column of its line lies between where
# the selection started and the cursor (R10).
law sel_cells:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  for +r: Nat
  for +x: Nat
  {Laws.Claim.sel_cells(Laws.Spec.run(fs, rows, cols, evs), r, x) == True{} : Bool}
