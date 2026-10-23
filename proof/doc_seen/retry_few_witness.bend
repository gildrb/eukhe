# eukhe: the proof of LAW retry_few_witness

import Base
import ../../bend/doc_seen.bend as Ds
import ../../LAWS.bend as Laws

def Laws.retry_few_witness():
  ([Ds.At{1n, Some{3n}}], {==})
