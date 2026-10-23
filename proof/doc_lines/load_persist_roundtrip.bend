# eukhe: the proof of LAW load_persist_roundtrip

import Base
import ../../bend/doc_lines.bend as Dl
import ../../LAWS.bend as Laws
import ./base.bend as LA

# the law load_persist_roundtrip
def pdl.roundtrip(+f: Dl.Doc) -> {Dl.persist(Dl.load(f)) == f : Dl.Doc}:
  match f:
    case Dl.Doc{+bom, +bs}:
      %LA.pdl.start_cat(Dl.split(bs), Dl.first(Dl.split(bs))) : {Dl.Doc{bom, _} == Dl.Doc{bom, bs} : Dl.Doc}
      %LA.pdl.split_cat(bs) : {Dl.Doc{bom, LA.pdl.cat(Dl.split(bs))} == Dl.Doc{bom, _} : Dl.Doc}
      {==}

# (F4) Lines and their endings

def Laws.load_persist_roundtrip(f):
  pdl.roundtrip(f)
