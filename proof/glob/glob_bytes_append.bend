# eukhe: the proof of LAW glob_bytes_append
#
# PROOF: by induction on a: a char's UTF-8 form goes before the rest
# untouched (GU.u8r.rest), and appending is associative.

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/utf8.bend as GU

def bya.go(a: String, +b: String) -> {GItems.bytes(String.append(a, b)) == List.append(&2, U32, GItems.bytes(a), GItems.bytes(b)) : List<&2, U32>}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x = GParse.code(c)
      +u = GItems.utf8(x, Nil{})
      %Equal.sym(List<&2, U32>, GItems.utf8(x, GItems.bytes(String.append(t, b))), List.append(&2, U32, u, GItems.bytes(String.append(t, b))), GU.u8r.rest(x, GItems.bytes(String.append(t, b)))) : {_ == List.append(&2, U32, GItems.utf8(x, GItems.bytes(t)), GItems.bytes(b)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, GItems.utf8(x, GItems.bytes(t)), List.append(&2, U32, u, GItems.bytes(t)), GU.u8r.rest(x, GItems.bytes(t))) : {List.append(&2, U32, u, GItems.bytes(String.append(t, b))) == List.append(&2, U32, _, GItems.bytes(b)) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, GItems.bytes(String.append(t, b)), List.append(&2, U32, GItems.bytes(t), GItems.bytes(b)), bya.go(t, b)) : {List.append(&2, U32, u, _) == List.append(&2, U32, List.append(&2, U32, u, GItems.bytes(t)), GItems.bytes(b)) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, GItems.bytes(t)), GItems.bytes(b)), List.append(&2, U32, u, List.append(&2, U32, GItems.bytes(t), GItems.bytes(b))), GL.gl.app_assoc(U32, u, GItems.bytes(t), GItems.bytes(b)))

def bya.one(c: Char) -> {GItems.bytes(SCon{c, SNil{}}) == GItems.utf8(Char.to_u32(c), Nil{}) : List<&2, U32>}:
  match c:
    case Chr{x}:
      {==}

def Glob.glob_bytes_append(a, b, c):
  +ab = List.append(&2, U32, GItems.bytes(a), GItems.bytes(b))
  +u = GItems.utf8(Char.to_u32(c), Nil{})
  %Equal.sym(List<&2, U32>, GItems.bytes(String.append(a, b)), ab, bya.go(a, b)) : {(_, GItems.bytes(SCon{c, SNil{}}), GItems.bytes("")) == (ab, u, Nil{}) : List<&2, U32> & List<&2, U32> & List<&2, U32>}
  %Equal.sym(List<&2, U32>, GItems.bytes(SCon{c, SNil{}}), u, bya.one(c)) : {(ab, _, GItems.bytes("")) == (ab, u, Nil{}) : List<&2, U32> & List<&2, U32> & List<&2, U32>}
  {==}
