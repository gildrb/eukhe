# eukhe: lemmas the proofs of the runners entry share (laws/runners.bend,
# section runners entry)

import Base
import ../../../bend/ffi_runners.bend as FRu
import ../../../bend/runners.bend as Ru
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/runners.bend as Runners
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def rn.says(r: Wr.Dec<Bool>) -> {Runners.read_says(r) == FRu.get_says(r) : Wr.Dec<Ru.Asker>}:
  match r:
    case Wr.Got{y, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rn.asker_tag(t: Nat, s: String) -> {Runners.read_asker.tag(t, s) == FRu.get_asker.tag(t, s) : Wr.Dec<Ru.Asker>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      rn.says(Wr.get_bool(s))
    case 3n+u:
      {==}

def rn.asker(r: Wr.Dec<Nat>) -> {Runners.read_asker(r) == FRu.get_asker(r) : Wr.Dec<Ru.Asker>}:
  match r:
    case Wr.Got{t, s}:
      rn.asker_tag(t, s)
    case Wr.Bad{}:
      {==}

def rn.within_auto(c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {Runners.read_within.auto(c, r) == FRu.get_within.auto(c, r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rn.within(r: Wr.Dec<List<&2, Nat>>) -> {Runners.read_within(r) == FRu.get_within(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{c, s}:
      rn.within_auto(c, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def rn.cell_asker(c: List<&2, Nat>, a: List<&2, Nat>, r: Wr.Dec<Ru.Asker>) -> {Runners.read_cell.asker(c, a, r) == FRu.get_cell.asker(c, a, r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rn.cell_auto(+c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {Runners.read_cell.auto(c, r) == FRu.get_cell.auto(c, r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{+a, +s}:
      %rn.asker(Wr.get_nat(s)) : {Runners.read_cell.asker(c, a, Runners.read_asker(Wr.get_nat(s))) == FRu.get_cell.asker(c, a, _) : Wr.Dec<FRu.Req>}
      rn.cell_asker(c, a, Runners.read_asker(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def rn.cell(r: Wr.Dec<List<&2, Nat>>) -> {Runners.read_cell(r) == FRu.get_cell(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{c, s}:
      rn.cell_auto(c, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def rn.registry(r: Wr.Dec<Bool>) -> {Runners.read_registry(r) == FRu.get_registry(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rn.tag(t: Nat, s: String) -> {Runners.read_req.tag(t, s) == FRu.get_req.tag(t, s) : Wr.Dec<FRu.Req>}:
  match t:
    case 0n:
      rn.within(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 1n:
      rn.cell(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      rn.registry(Wr.get_bool(s))
    case 3n+u:
      {==}

def rn.go(r: Wr.Dec<Nat>) -> {Runners.read_req.go(r) == FRu.get_req.go(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{t, s}:
      rn.tag(t, s)
    case Wr.Bad{}:
      {==}

def rn.req(s: String) -> {Runners.read_req(s) == FRu.get_req(s) : Wr.Dec<FRu.Req>}:
  rn.go(Wr.get_nat(s))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def rn.out(o: Ru.Out) -> {FRu.put_out(o, "") == Runners.spell_out(o) : String}:
  match o:
    case Ru.Out{a, e}:
      match e:
        case Ru.Ran{h}:
          match h:
            case Ru.Auto{}:
              {==}
            case Ru.Approved{}:
              {==}
        case Ru.Refused{w}:
          match w:
            case Ru.Denied{}:
              {==}
            case Ru.Unanswered{}:
              {==}

def rn.reply(q: FRu.Req) -> {FRu.answer(q) == Runners.spell_answer(q) : String}:
  match q:
    case FRu.QWithin{c, a}:
      {==}
    case FRu.QCell{+c, +a, +k}:
      rn.out(Ru.cell(c, a, k))
    case FRu.QRegistry{h}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

def rn.end(b: Bool, q: FRu.Req) -> {FRu.run.end(b, q) == Runners.spec.end(b, q) : String}:
  match b:
    case True{}:
      rn.reply(q)
    case False{}:
      {==}

def rn.run(r: Wr.Dec<FRu.Req>) -> {FRu.run(r) == Runners.spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      rn.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def rn.exact(+s: String) -> {FRu.ffi(s) == Runners.spec(s) : String}:
  %rn.req(s) : {FRu.run(_) == Runners.spec(s) : String}
  rn.run(Runners.read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def rn.rt_asker(k: Ru.Asker, rest: String) -> {Runners.read_asker(Wr.get_nat(Runners.spell_asker(k, rest))) == Wr.Got{k, rest} : Wr.Dec<Ru.Asker>}:
  match k:
    case Ru.NoClient{}:
      {==}
    case Ru.Silent{}:
      {==}
    case Ru.Says{y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

def rn.rt_within(+c: List<&2, Nat>, +a: List<&2, Nat>, +rest: String, +fits: {Runners.req_fits(FRu.QWithin{c, a}) == True{} : Bool}) -> {Runners.read_req(Runners.spell_req(FRu.QWithin{c, a}, rest)) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}:
  +hc = LLogicBool.wr_and_l(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +ha = LLogicBool.wr_and_r(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(c, Runners.spell_ns(a, rest))), Wr.Got{c, Runners.spell_ns(a, rest)}, Wire.wire_list_round_trip(c, Runners.spell_ns(a, rest), hc)) : {Runners.read_within(_) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(a, rest)), Wr.Got{a, rest}, Wire.wire_list_round_trip(a, rest, ha)) : {Runners.read_within.auto(c, _) == Wr.Got{FRu.QWithin{c, a}, rest} : Wr.Dec<FRu.Req>}
  {==}

def rn.rt_cell(+c: List<&2, Nat>, +a: List<&2, Nat>, +k: Ru.Asker, +rest: String, +fits: {Runners.req_fits(FRu.QCell{c, a, k}) == True{} : Bool}) -> {Runners.read_req(Runners.spell_req(FRu.QCell{c, a, k}, rest)) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}:
  +hc = LLogicBool.wr_and_l(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +ha = LLogicBool.wr_and_r(Runners.ns_fit(c), Runners.ns_fit(a), fits)
  +r2 = Runners.spell_asker(k, rest)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(c, Runners.spell_ns(a, r2))), Wr.Got{c, Runners.spell_ns(a, r2)}, Wire.wire_list_round_trip(c, Runners.spell_ns(a, r2), hc)) : {Runners.read_cell(_) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Runners.spell_ns(a, r2)), Wr.Got{a, r2}, Wire.wire_list_round_trip(a, r2, ha)) : {Runners.read_cell.auto(c, _) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  %Equal.sym(Wr.Dec<Ru.Asker>, Runners.read_asker(Wr.get_nat(r2)), Wr.Got{k, rest}, rn.rt_asker(k, rest)) : {Runners.read_cell.asker(c, a, _) == Wr.Got{FRu.QCell{c, a, k}, rest} : Wr.Dec<FRu.Req>}
  {==}

def rn.rt_registry(h: Bool, rest: String) -> {Runners.read_req(Runners.spell_req(FRu.QRegistry{h}, rest)) == Wr.Got{FRu.QRegistry{h}, rest} : Wr.Dec<FRu.Req>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def rn.rt(q: FRu.Req, +rest: String, fits: {Runners.req_fits(q) == True{} : Bool}) -> {Runners.read_req(Runners.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRu.Req>}:
  match q:
    case FRu.QWithin{c, a}:
      rn.rt_within(c, a, rest, fits)
    case FRu.QCell{c, a, k}:
      rn.rt_cell(c, a, k, rest, fits)
    case FRu.QRegistry{h}:
      rn.rt_registry(h, rest)
