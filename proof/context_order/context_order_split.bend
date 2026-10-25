# eukhe: the proof of LAW context_order_split

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_order_split: ordering a ++ b orders a, then b at offset |a| (co.order_app: no window reaches past the assistant b starts with), and an offset shifts every index (co.order_shift).

def ContextOrder.context_order_split(a, b, h):
  Equal.trans(List<&2, Co.Step>, Co.order.go(List.append(&2, Co.Msg, a, b), 0n), List.append(&2, Co.Step, Co.order.go(a, 0n), Co.order.go(b, Nat.add(List.length(&2, Co.Msg, a), 0n))), List.append(&2, Co.Step, Co.order.go(a, 0n), ContextOrder.shift(List.length(&2, Co.Msg, a), Co.order.go(b, 0n))), LACo.co.order_app(a, b, 0n, h), Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => List.append(&2, Co.Step, Co.order.go(a, 0n), z), Co.order.go(b, Nat.add(List.length(&2, Co.Msg, a), 0n)), ContextOrder.shift(List.length(&2, Co.Msg, a), Co.order.go(b, 0n)), LACo.co.order_shift(b, List.length(&2, Co.Msg, a), 0n)))
