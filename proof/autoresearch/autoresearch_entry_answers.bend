# eukhe: the proof of LAW autoresearch_entry_answers

import Base
import ../../bend/ffi_autoresearch.bend as FAr
import ../../laws/autoresearch/entry.bend as AutoresearchEntry
import ./base/entry.bend as LAE

def AutoresearchEntry.autoresearch_entry_answers(s, q, fits):
  %LAE.ae.req(q, fits) : {FAr.step.q(s, _) == (FAr.Live{AutoresearchEntry.ar_next(s, q)}, AutoresearchEntry.ar_reply(s, q)) : FAr.St & String}
  LAE.ae.serve(s, q)
