# eukhe: the proof of LAW once_key_malformed_exact
#
# PROOF: the entry and the laws' reader read the two strings with the
# same wire decoder; where that reader finds no whole request, the entry
# answers its error form.

import Base
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ./base.bend as LA

def om.id(a: String, d: Wr.Dec<String>, no: {Once.on_read_key.id(a, d) == None{} : Maybe<&2, Once.OnKey>}) -> {FO.ffi.id(a, d) == SCon{'E', SCon{' ', "once: malformed key"}} : String}:
  match d:
    case Wr.Got{b, rest}:
      match rest:
        case SNil{}:
          LA.ob.none_some(Once.OnKey, {FO.ffi.end(True{}, a, b) == SCon{'E', SCon{' ', "once: malformed key"}} : String}, Once.OnKey{a, b}, Equal.sym(Maybe<&2, Once.OnKey>, Some{Once.OnKey{a, b}}, None{}, no))
        case SCon{h, t}:
          {==}
    case Wr.Bad{}:
      {==}

def om.scope(d: Wr.Dec<String>, no: {Once.on_read_key.scope(d) == None{} : Maybe<&2, Once.OnKey>}) -> {FO.ffi.scope(d) == SCon{'E', SCon{' ', "once: malformed key"}} : String}:
  match d:
    case Wr.Got{a, rest}:
      om.id(a, Wr.get_str(rest), no)
    case Wr.Bad{}:
      {==}

def Once.once_key_malformed_exact(i, no):
  om.scope(Wr.get_str(i), no)
