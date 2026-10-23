# eukhe: the laws of area tokens

import Base
import ../bend/tokens.bend as Tk

# ---- dashboard_tokens ----

# LAWS (T2): the dashboard's presentation tokens. Each law is an open
# claim about the model in bend/tokens.bend; PROOF.bend proves them (as
# Tokens.<law>) with the lemmas of proof/tokens/.

# (T2) Dashboard tokens
# ---------------------
# docs/dashboard.md "Tokens", the model in bend/tokens.bend. The web app
# writes every presentation value once, in
# crates/eukhe-dashboard/ui/src/tokens.stylex.ts; its test
# src/tokens.test.ts checks that the token values there equal the tables
# of bend/tokens.bend (through bridge/bridge_tokens.bend).

# LAW tokens_paired: every color token has a value in both modes, light and dark
law tokens_paired:
  for t: Tk.Tone
  for m: Tk.Mode
  {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(m))) == True{} : Bool}

# LAW tokens_legible: in both modes, every text pair meets the contrast it needs (4.5:1
# for text, 3:1 for a caption on a fill), as exact rationals
law tokens_legible:
  for m: Tk.Mode
  for +pre: List<&2, Tk.Ink>
  for p: Tk.Ink
  for +post: List<&2, Tk.Ink>
  for split: {Tk.pairs() == List.append(&2, Tk.Ink, pre, p <> post) : List<&2, Tk.Ink>}
  {Tk.readable(m, p) == True{} : Bool}

# LAW tokens_layers_ordered: the stacking layers are strictly ordered, bottom to top
law tokens_layers_ordered:
  {Tk.ascends(Tk.layers()) == True{} : Bool}

# LAW tokens_space_ascends: the spacing scale strictly ascends
law tokens_space_ascends:
  {Tk.ascends(Tk.space()) == True{} : Bool}

# LAW tokens_type_ascends: the type sizes strictly ascend, and so do the line heights
law tokens_type_ascends:
  {Bool.and(Tk.ascends(Tk.sizes()), Tk.ascends(Tk.lines())) == True{} : Bool}
