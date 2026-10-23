# eukhe: the proof of LAW push_agrees_always

import Base
import ../../laws/optchat.bend as Optchat
import ./push_agrees_always/optchat.bend as LLOptchat

def Optchat.push_agrees_always(n):
  LLOptchat.push_agrees_always(n)
