# eukhe: the proof of LAW wire_list_spells_items

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base/dec.bend as LAWireDec

# the item loop answers the count of xs and the spec's items
def wp_go(~A: Data, ~put: A -> String -> String, xs: List<&2, A>, rest: String) ->
  {Wr.put_list.go(~A, ~put, xs, rest) == (List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Nat & String, Nat & String, p => Wr.put_list.step(~A, ~put, x, p),
        Wr.put_list.go(~A, ~put, t, rest), (List.length(&2, A, t), LawsBase.wire_put_items(~A, ~put, t, rest)),
        wp_go(~A, ~put, t, rest))

def Wire.wire_list_spells_items(A, put, xs, rest):
  +r = rest
  %Equal.sym(Nat & String, Wr.put_list.go(~A, ~put, xs, r), (List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, r)), wp_go(~A, ~put, xs, r)) : {Wr.put_list.fin(_) == LawsBase.wire_dec(List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, r)) : String}
  LAWireDec.wdec.nat(List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, r))
