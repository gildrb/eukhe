# eukhe: the proof of LAW first_leaves_push

import Base
import ../../bend/optchat.bend as O
import ../../LAWS.bend as Laws

def first_leaves_push() -> {O.agree(O.First{}, 11n) == False{} : Bool}:
  {==}

def Laws.first_leaves_push():
  first_leaves_push()
