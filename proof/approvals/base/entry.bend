# eukhe: lemmas the proofs of the approvals entry share
# (laws/approvals.bend, section approvals entry)

import Base
import ../../../bend/approvals.bend as Am
import ../../../bend/ffi_approvals.bend as FAm
import ../../../bend/wire.bend as Wr
import ../../../laws/approvals.bend as Approvals
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def ap.next_parent(h: Am.Here, es: List<&2, Nat>, r: Wr.Dec<Bool>) -> {Approvals.read_next.parent(h, es, r) == FAm.get_next.parent(h, es, r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{p, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ap.next_effs(h: Am.Here, r: Wr.Dec<List<&2, Nat>>) -> {Approvals.read_next.effs(h, r) == FAm.get_next.effs(h, r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{es, s}:
      ap.next_parent(h, es, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ap.next_here(t: Nat, s: String) -> {Approvals.read_next.here(t, s) == FAm.get_next.here(t, s) : Wr.Dec<FAm.Req>}:
  match t:
    case 0n:
      ap.next_effs(Am.Nobody{}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 1n:
      ap.next_effs(Am.GatewayOnly{}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      ap.next_effs(Am.Clients{}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n+u:
      {==}

def ap.next(r: Wr.Dec<Nat>) -> {Approvals.read_next(r) == FAm.get_next(r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{t, s}:
      ap.next_here(t, s)
    case Wr.Bad{}:
      {==}

def ap.answered_yes(es: List<&2, Nat>, r: Wr.Dec<Bool>) -> {Approvals.read_answered.yes(es, r) == FAm.get_answered.yes(es, r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{y, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ap.answered(r: Wr.Dec<List<&2, Nat>>) -> {Approvals.read_answered(r) == FAm.get_answered(r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{es, s}:
      ap.answered_yes(es, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ap.tag(t: Nat, s: String) -> {Approvals.read_req.tag(t, s) == FAm.get_req.tag(t, s) : Wr.Dec<FAm.Req>}:
  match t:
    case 0n:
      ap.next(Wr.get_nat(s))
    case 1n:
      ap.answered(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      {==}
    case 3n+u:
      {==}

def ap.go(r: Wr.Dec<Nat>) -> {Approvals.read_req.go(r) == FAm.get_req.go(r) : Wr.Dec<FAm.Req>}:
  match r:
    case Wr.Got{t, s}:
      ap.tag(t, s)
    case Wr.Bad{}:
      {==}

def ap.req(s: String) -> {Approvals.read_req(s) == FAm.get_req(s) : Wr.Dec<FAm.Req>}:
  ap.go(Wr.get_nat(s))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def ap.fate(f: Am.Fate, rest: String) -> {FAm.put_fate(f, rest) == Approvals.spell_fate(f, rest) : String}:
  match f:
    case Am.Runs{}:
      {==}
    case Am.Denied{}:
      {==}
    case Am.Unheard{}:
      {==}
    case Am.GatewayRefused{}:
      {==}

def ap.reply_next(h: Am.Here, +es: List<&2, Nat>, p: Bool) -> {FAm.answer(FAm.QNext{h, es, p}) == Approvals.spell_answer(FAm.QNext{h, es, p}) : String}:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.GatewayOnly{}:
      %ap.fate(Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), "") : {Wr.put_nat(2n, FAm.put_fate(Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), "")) == Wr.put_nat(2n, _) : String}
      {==}
    case Am.Clients{}:
      {==}

def ap.reply(q: FAm.Req) -> {FAm.answer(q) == Approvals.spell_answer(q) : String}:
  match q:
    case FAm.QNext{h, es, p}:
      ap.reply_next(h, es, p)
    case FAm.QAnswered{es, y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}
    case FAm.QDefault{}:
      {==}

def ap.end(b: Bool, q: FAm.Req) -> {FAm.run.end(b, q) == Approvals.spec.end(b, q) : String}:
  match b:
    case True{}:
      ap.reply(q)
    case False{}:
      {==}

def ap.run(r: Wr.Dec<FAm.Req>) -> {FAm.run(r) == Approvals.spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      ap.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def ap.exact(+s: String) -> {FAm.ffi(s) == Approvals.spec(s) : String}:
  %ap.req(s) : {FAm.run(_) == Approvals.spec(s) : String}
  ap.run(Approvals.read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def ap.rt_next(p: Bool, h: Am.Here, +es: List<&2, Nat>, +rest: String, +fits: {Approvals.ns_fit(es) == True{} : Bool}) -> {Approvals.read_req(Approvals.spell_req(FAm.QNext{h, es, p}, rest)) == Wr.Got{FAm.QNext{h, es, p}, rest} : Wr.Dec<FAm.Req>}:
  match p:
    case True{}:
      match h:
        case Am.Nobody{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(True{}, rest))), Wr.Got{es, Wr.put_bool(True{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(True{}, rest), fits)) : {Approvals.read_next.effs(Am.Nobody{}, _) == Wr.Got{FAm.QNext{Am.Nobody{}, es, True{}}, rest} : Wr.Dec<FAm.Req>}
          {==}
        case Am.GatewayOnly{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(True{}, rest))), Wr.Got{es, Wr.put_bool(True{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(True{}, rest), fits)) : {Approvals.read_next.effs(Am.GatewayOnly{}, _) == Wr.Got{FAm.QNext{Am.GatewayOnly{}, es, True{}}, rest} : Wr.Dec<FAm.Req>}
          {==}
        case Am.Clients{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(True{}, rest))), Wr.Got{es, Wr.put_bool(True{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(True{}, rest), fits)) : {Approvals.read_next.effs(Am.Clients{}, _) == Wr.Got{FAm.QNext{Am.Clients{}, es, True{}}, rest} : Wr.Dec<FAm.Req>}
          {==}
    case False{}:
      match h:
        case Am.Nobody{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(False{}, rest))), Wr.Got{es, Wr.put_bool(False{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(False{}, rest), fits)) : {Approvals.read_next.effs(Am.Nobody{}, _) == Wr.Got{FAm.QNext{Am.Nobody{}, es, False{}}, rest} : Wr.Dec<FAm.Req>}
          {==}
        case Am.GatewayOnly{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(False{}, rest))), Wr.Got{es, Wr.put_bool(False{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(False{}, rest), fits)) : {Approvals.read_next.effs(Am.GatewayOnly{}, _) == Wr.Got{FAm.QNext{Am.GatewayOnly{}, es, False{}}, rest} : Wr.Dec<FAm.Req>}
          {==}
        case Am.Clients{}:
          %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(False{}, rest))), Wr.Got{es, Wr.put_bool(False{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(False{}, rest), fits)) : {Approvals.read_next.effs(Am.Clients{}, _) == Wr.Got{FAm.QNext{Am.Clients{}, es, False{}}, rest} : Wr.Dec<FAm.Req>}
          {==}

def ap.rt_answered(y: Bool, +es: List<&2, Nat>, +rest: String, +fits: {Approvals.ns_fit(es) == True{} : Bool}) -> {Approvals.read_req(Approvals.spell_req(FAm.QAnswered{es, y}, rest)) == Wr.Got{FAm.QAnswered{es, y}, rest} : Wr.Dec<FAm.Req>}:
  match y:
    case True{}:
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(True{}, rest))), Wr.Got{es, Wr.put_bool(True{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(True{}, rest), fits)) : {Approvals.read_answered(_) == Wr.Got{FAm.QAnswered{es, True{}}, rest} : Wr.Dec<FAm.Req>}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Approvals.spell_ns(es, Wr.put_bool(False{}, rest))), Wr.Got{es, Wr.put_bool(False{}, rest)}, Wire.wire_list_round_trip(es, Wr.put_bool(False{}, rest), fits)) : {Approvals.read_answered(_) == Wr.Got{FAm.QAnswered{es, False{}}, rest} : Wr.Dec<FAm.Req>}
      {==}

def ap.rt(q: FAm.Req, +rest: String, fits: {Approvals.req_fits(q) == True{} : Bool}) -> {Approvals.read_req(Approvals.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FAm.Req>}:
  match q:
    case FAm.QNext{h, es, p}:
      ap.rt_next(p, h, es, rest, fits)
    case FAm.QAnswered{es, y}:
      ap.rt_answered(y, es, rest, fits)
    case FAm.QDefault{}:
      {==}
