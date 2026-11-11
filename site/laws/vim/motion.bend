# eukhe.com's Neovim: the laws of motions (R2), from normal mode after any events
# ===============================================================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW key_j: j moves to the next line, and stays on the last.
law key_j:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.j(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_k: k moves to the line before, and stays on the first.
law key_k:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.k(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_gg: gg moves to the first line.
law key_gg:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.gg(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_G: G moves to the last line.
law key_G:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.G(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_0: 0 moves to the line's first character.
law key_0:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.zero(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_dollar: $ moves to the line's last character.
law key_dollar:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.dollar(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_h: h moves one character left, and stays on the first.
law key_h:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.h(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW key_l: l moves one character right, and stays on the last.
law key_l:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.l(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_j: j keeps the column (A4).
law col_j:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.vcol_j(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_k: k keeps the column (A4).
law col_k:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.vcol_k(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_gg: gg keeps the column (A4).
law col_gg:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.vcol_gg(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW col_G: G keeps the column (A4).
law col_G:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.vcol_G(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW j_view: j scrolls the view only as far as scrolloff needs (R3).
law j_view:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.j_view(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}
