# eukhe: the proof of LAW once_key_never_err
#
# PROOF: the entry answers each spelled request with its key
# (LE.oe.key_answers); a key is the scope spelled before the id spelled,
# and a string's spelling opens with its length, which never opens with
# 'E' (DW.dcw.sfin_ok).

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ../../laws/base.bend as LawsBase
import ../base/wire_dec.bend as DW
import ./base/entry.bend as LE

def Once.once_key_never_err(a, b, fa, fb):
  %Equal.sym(String, FO.ffi(Once.on_spell_key(a, b)), O.key(a, b), LE.oe.key_answers(a, b, fa, fb)) : {LawsBase.wire_opens_err(_) == False{} : Bool}
  DW.dcw.sfin_ok(Wr.put_str.go(a, SNil{}, 0n), Wr.put_str(b, ""))
