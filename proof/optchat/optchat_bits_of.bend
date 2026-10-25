# eukhe: the proof of LAW optchat_bits_of
# Its bits' value is the number (LAB.ob.val_of); its last bit is the 1 of
# the number's top (LAB.ob.canon_of).

import Base
import ../../laws/optchat.bend as Optchat
import ./base/bits.bend as LAB

def Optchat.optchat_bits_of(n):
  (LAB.ob.val_of(n), LAB.ob.canon_of(n))
