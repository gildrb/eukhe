# eukhe.com's Neovim: the laws of Oil (R6)
# ========================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW oil_up_entry: after any events, an Oil listing starts with "../".
law oil_up_entry:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.up_entry(Laws.Spec.run(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_parent: in a listing, "-" shows the parent folder; at the root
# it stays.
law oil_parent:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.parent(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_open: in a file (one of fs, its path naming a file: not empty,
# not ending in "/"), "-" shows the file's folder with the cursor on the
# file's entry.
law oil_open:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.open(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_back: from a file, "-" then Ctrl-c returns to that file (R6).
law oil_back:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.back(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}

# LAW oil_listing: after any events, a listing holds every child (file or folder) of its folder and nothing else (R6).
law oil_listing:
  for fs: List<&2, T.Buf>
  for +rows: Nat
  for +cols: Nat
  for +evs: List<&2, T.Ev>
  {Laws.Claim.listing(fs, Laws.Spec.run(fs, rows, cols, evs)) == True{} : Bool}
