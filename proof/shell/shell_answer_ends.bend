# eukhe: the proof of LAW shell_answer_ends
# The decoder reads back the answer request (LASh.sh.rt); the model's gate on a yes adds the step (the script ends Finished: 0), on a no ends Denied at the step (1, id).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./base.bend as LASh

def Shell.shell_answer_ends(i, fits):
  +f = fits
  +y = LASh.sh.rt(FSh.QAnswer{i, True{}}, "", f)
  +n = LASh.sh.rt(FSh.QAnswer{i, False{}}, "", f)
  +ey = Equal.cong(Wr.Dec<FSh.Req>, String, z => FSh.run(z), FSh.get_req(Shell.spell_req(FSh.QAnswer{i, True{}}, "")), Wr.Got{FSh.QAnswer{i, True{}}, ""}, y)
  +en = Equal.cong(Wr.Dec<FSh.Req>, String, z => FSh.run(z), FSh.get_req(Shell.spell_req(FSh.QAnswer{i, False{}}, "")), Wr.Got{FSh.QAnswer{i, False{}}, ""}, n)
  (ey, en)
