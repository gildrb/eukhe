# eukhe: the proof of LAW facts_fit_answer_room

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts/model.bend as Facts
import ./facts_room_leaves_the_answer.bend as PRoom

def Facts.facts_fit_answer_room(base, mm, b, a, win, h):
  PRoom.pf.facts_room_leaves_the_answer(b, Fx.cap.shrink(Fx.fit.cap(base, mm, b), win), a, h)
