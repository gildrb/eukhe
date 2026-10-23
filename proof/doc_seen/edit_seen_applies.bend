# eukhe: the proof of LAW edit_seen_applies

import Base
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA

def DocSeen.edit_seen_applies(seen, ats, all):
  LA.pv.edit_seen_applies(seen, ats, all)
