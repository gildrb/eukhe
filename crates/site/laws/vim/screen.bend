# eukhe.com's Neovim: the laws of the cursor and the screen
# =========================================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW cursor_ok: after any events from the start, the cursor is inside
# the picker's float when one is open, else on the command line or on a
# character of the window's text (R1).
law cursor_ok:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.cursor_ok(fs, Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}

# LAW cursor_on_text: after any events and an Esc, the cursor is on a
# character of the window's text, and the frame names that character
# (R1, A3).
law cursor_on_text:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.on_text(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}

# LAW scrolloff: after any events, in normal mode, the cursor keeps
# min(8, (h - 1) / 2) lines on screen above and below it unless the
# buffer ends first (R3).
law scrolloff:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.scrolled(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}

# LAW fits: after any events, the screen is the last size asked for (at
# least 3 x 12) and every part of the frame fits it (R4).
law fits:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.fits(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}

# LAW cmdline_cursor: after any events, a cursor on the command line
# (no float open) sits right after the text it shows, on screen (R1).
law cmdline_cursor:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.on_cmdline(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}

# LAW edges: after any events, the scrollbar is in the last column, the
# command line fits the screen, and the cursorline shows exactly when no
# float is open (R4).
law edges:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.edges(Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}

# LAW scrolloff_any: after any events, with no float open and the cursor
# in the text rows, scrolloff holds (R3).
law scrolloff_any:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Spec.scrolled_any(fs, Laws.Spec.run(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}
