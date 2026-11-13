# eukhe: the proof of LAW once_key_reads_back
#
# PROOF: the entry answers each spelled request with its key
# (LE.oe.key_answers): the scope spelled before the id spelled; the
# wire reads a string that fits back (wire_str_round_trip), twice, and
# nothing is left after the id.

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base/entry.bend as LE

def Once.once_key_reads_back(a, b, fa, fb):
  %Equal.sym(String, FO.ffi(Once.on_spell_key(a, b)), O.key(a, b), LE.oe.key_answers(a, b, fa, fb)) : {Once.on_read_key(_) == Some{Once.OnKey{a, b}} : Maybe<&2, Once.OnKey>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, Wr.put_str(b, ""))), Wr.Got{a, Wr.put_str(b, "")}, Wire.wire_str_round_trip(a, Wr.put_str(b, ""), fa)) : {Once.on_read_key.scope(_) == Some{Once.OnKey{a, b}} : Maybe<&2, Once.OnKey>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(b, "")), Wr.Got{b, ""}, Wire.wire_str_round_trip(b, "", fb)) : {Once.on_read_key.id(a, _) == Some{Once.OnKey{a, b}} : Maybe<&2, Once.OnKey>}
  {==}
