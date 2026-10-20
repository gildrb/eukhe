# proof_documents_laws: the fills of the laws of laws/documents.bend
# (as Docs.<law>). The lemmas are in bend/proof_documents.bend (edits,
# writes, moves, temporary files, seen lines, grep, continuations, tags)
# and bend/proof_doc_lines.bend (lines and their endings).

import Base
import ../laws/documents.bend as Docs
import ./doc_commit.bend as Cm
import ./doc_seen.bend as Ds
import ./doc_search.bend as Sr
import ./doc_lines.bend as Dl
import ./doc_tags.bend as Dt
import ./proof_documents.bend as Pd
import ./proof_doc_lines.bend as Pdl

# (F1, F9) An edit of many files

def Docs.edit_reports_what_landed(fs):
  Pd.pc.reports_what_landed(fs)

def Docs.edit_all_or_nothing_on_conflict(pre, k, x, post):
  Pd.pc.all_or_nothing(pre, k, x, post)

def Docs.edit_lands_every_file(fs, same, sound):
  Pd.pc.lands_every_file(fs, same, sound)

# (F2) The write tool

def Docs.write_never_loses_unseen(d, s, c, lost):
  Pd.pc.write_refused(d, s, c, lost)

def Docs.write_writes_seen(d, s, c, kept):
  Pd.pc.write_writes(d, s, c, kept)

# (F5) A move

def Docs.move_never_overwrites(s, t, es, taken):
  Pd.pc.move_taken(s, t, es, taken)

def Docs.move_moves(s, t, es, free, from):
  Pd.pc.move_moves(s, t, es, free, from)

# (F10) Temporary files

def Docs.temp_sweep_never_held(pre, i, k, post):
  Pd.pc.sweep_never_held(pre, i, k, post)

def Docs.temp_sweep_only_own(pre, i, k, h, post, other):
  Pd.pc.sweep_only_own(pre, i, k, h, post, other)

def Docs.temp_sweep_removes_free(pre, i, post):
  Pd.pc.sweep_removes_free(pre, i, post)

# (F4) Lines and their endings

def Docs.load_persist_roundtrip(f):
  Pdl.pdl.roundtrip(f)

def Docs.edit_keeps_untouched_bytes(bom, bs, s, k, xs, fits):
  Pdl.pdl.edit_keeps(bom, bs, s, k, xs, fits)

def Docs.grep_line_is_read_line(b, bs):
  Pdl.pdl.grep_is_read(b, bs)

# (F3) Tags

def Docs.tag_names_shown_text(t, op):
  Pd.pdt.tag_names(t, op)

# (F11) Seen lines

def Docs.edit_only_seen_lines(seen, anchors, ok):
  Pd.pv.edit_only_seen_lines(seen, anchors, ok)

def Docs.edit_seen_applies(seen, anchors, all):
  Pd.pv.edit_seen_applies(seen, anchors, all)

def Docs.reveal_then_retry(seen, anchors, few):
  Pd.pv.reveal_then_retry(seen, anchors, few)

# (F6) What grep searched

def Docs.grep_accounts_every_file(es, p, s, k, rem, n):
  Pd.ps.accounts_every_file(es, p, s, k, rem, n)

def Docs.grep_notes_every_gap(os, t):
  Pd.ps.notes_every_gap(os, t)

def Docs.grep_notes_every_cut(pre, i, pa, post):
  Pd.ps.notes_every_cut(pre, i, pa, post)

# (F7) Continuations

def Docs.continuation_progresses(ps, s, k, c, h):
  Pd.ps.progresses(ps, s, k, c, h)

def Docs.continuation_contiguous(ps, s, k, c, h):
  Pd.ps.contiguous(ps, s, k, c, h)

def Docs.continuation_disjoint(ps, s, k, c, x, h, nd):
  Pd.ps.disjoint(ps, s, k, c, x, h, nd)
