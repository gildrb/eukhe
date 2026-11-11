# eukhe: the proof of LAW quirks_lookup_reads
#
# PROOF: the list a lookup's decoder reads is the spelling of that list,
# within the wire (Wire.wire_list_exact, WireFfi.wrb.nats_fit); a reply
# other than the error form comes only from a list read whole, nothing
# left, of exactly four Nats (qlr.ask), which is the lookup Rust writes.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/quirks.bend as Quirks
import ../wire/base/spell.bend as LAWireSpell
import ../wire_ffi/base.bend as WRB

def qlr.G(s: String) -> Type:
  &q: If.Query -> &d: Nat -> {s == Quirks.spell_lookup(q, d) : String} & {Quirks.lookup_fits(q, d) == True{} : Bool}

def qlr.ask(+rs: List<&2, If.Rule>, -s: String, xs: List<&2, Nat>,
  ex: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, "") : String},
  fx: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.ask(rs, FQ.ask(xs)))) == False{} : Bool}) -> qlr.G(s):
  match xs:
    case Nil{}:
      LAWireSpell.ws_absurd(qlr.G(s), ok)
    case f <> a:
      match a:
        case Nil{}:
          LAWireSpell.ws_absurd(qlr.G(s), ok)
        case m <> b:
          match b:
            case Nil{}:
              LAWireSpell.ws_absurd(qlr.G(s), ok)
            case h <> c:
              match c:
                case Nil{}:
                  LAWireSpell.ws_absurd(qlr.G(s), ok)
                case d <> e:
                  match e:
                    case Nil{}:
                      (If.Query{f, m, h}, (d, (ex, WRB.wrb.and_r(LawsBase.wire_fits(4n), LawsBase.wire_nats_fit([f, m, h, d]), fx))))
                    case y <> z:
                      LAWireSpell.ws_absurd(qlr.G(s), ok)

def qlr.end(+rs: List<&2, If.Rule>, -s: String, +xs: List<&2, Nat>, s1: String,
  ex: {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, s1) : String},
  fx: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.end(Wr.end(s1), rs, xs))) == False{} : Bool}) -> qlr.G(s):
  match s1:
    case SNil{}:
      qlr.ask(rs, s, xs, ex, fx, ok)
    case SCon{c, t}:
      LAWireSpell.ws_absurd(qlr.G(s), ok)

def qlr.book(+rs: List<&2, If.Rule>, +s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(Pair.snd(FQ.St, String, FQ.step.book(rs, d))) == False{} : Bool}) -> qlr.G(s):
  match d:
    case Wr.Got{+xs, +s1}:
      +e = ed
      qlr.end(rs, s, xs, s1, Wire.wire_list_exact(s, xs, s1, e), WRB.wrb.nats_fit(s, xs, s1, e), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(qlr.G(s), ok)

def Quirks.quirks_lookup_reads(rs, s, ok):
  qlr.book(rs, s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==}, ok)
