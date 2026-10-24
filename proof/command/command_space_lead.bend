# eukhe: the proof of LAW command_space_lead
#
# PROOF of LAW command_space_lead: a leading space splits off an empty
# first word (words of 32 <> line is Nil <> words(line)), and the walk
# skips an empty word at the root (step.empty of Top is Top), so the
# walk over the words of the spaced line is the walk over the words of
# the line itself: both sides compute to the same term.

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command

def Command.command_space_lead(t, line):
  {==}
