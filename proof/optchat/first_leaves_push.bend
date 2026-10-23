# eukhe: the proof of LAW first_leaves_push

import Base
import ../../bend/optchat.bend as O
import ../../laws/optchat.bend as Optchat

def first_leaves_push() -> {O.agree(O.First{}, 11n) == False{} : Bool}:
  {==}

def Optchat.first_leaves_push():
  first_leaves_push()
