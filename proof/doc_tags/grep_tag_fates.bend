# eukhe: the proof of LAW grep_tag_fates
#
# PROOF: by induction on ss, `fates` maps each scan on its own; the three
# one-file pages and the empty one compute.

import Base
import ../../bend/doc_tags.bend as Dt
import ../../laws/doc_tags.bend as DocTags

def gtf.app(ss: List<&2, Dt.Scan>, +tt: List<&2, Dt.Scan>) -> {Dt.fates(List.append(&2, Dt.Scan, ss, tt)) == List.append(&2, Dt.Fate, Dt.fates(ss), Dt.fates(tt)) : List<&2, Dt.Fate>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> r:
      %Equal.sym(List<&2, Dt.Fate>, Dt.fates(List.append(&2, Dt.Scan, r, tt)), List.append(&2, Dt.Fate, Dt.fates(r), Dt.fates(tt)), gtf.app(r, tt)) : {Dt.fate(s) <> _ == Dt.fate(s) <> List.append(&2, Dt.Fate, Dt.fates(r), Dt.fates(tt)) : List<&2, Dt.Fate>}
      {==}

def DocTags.grep_tag_fates(ss, tt):
  (gtf.app(ss, tt), {==})
