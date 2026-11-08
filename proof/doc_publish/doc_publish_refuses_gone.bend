# eukhe: the proof of LAW doc_publish_refuses_gone
#
# PROOF: a re-read that met no file is Gone; the code refuses it, and the
# run ends refused, whatever re-reads are left (dpb.done).

import Base
import ../../laws/doc_publish.bend as DocPublish
import ../../spec/harness/doc_publish.bend as S
import ./base.bend as LA

def DocPublish.doc_publish_refuses_gone(n, b, c, r, ls):
  LA.dpb.done(ls, 1n+n, S.Refused{})
