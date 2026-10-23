# eukhe: the proof of LAW retry_few_witness

import Base
import ../../bend/doc_seen.bend as Ds
import ../../laws/doc_seen.bend as DocSeen

def DocSeen.retry_few_witness():
  ([Ds.At{1n, Some{3n}}], {==})
