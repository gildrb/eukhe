# eukhe: the proof of LAW first_leaves_push

import Base
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/push.bend as OPush
import ../../laws/optchat.bend as Optchat

def first_leaves_push() -> {OPush.agree(OFit.First{}, 11n) == False{} : Bool}:
  {==}

def Optchat.first_leaves_push():
  first_leaves_push()
