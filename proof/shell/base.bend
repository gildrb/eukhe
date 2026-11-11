# eukhe: lemmas the proofs of area shell share

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/shell.bend as Shell
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def sh.reply(q: FSh.Req) -> {FSh.answer(q) == Shell.spell_answer(q) : String}:
  match q:
    case FSh.QStep{a, ps}:
      {==}
    case FSh.QAllows{a, es}:
      {==}
    case FSh.QAnswer{i, y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

# The reader reads back what Rust writes
# --------------------------------------

def sh.parts_rt(ps: List<&2, Tl.Part>) -> {FSh.parts.of(Shell.spell_parts(ps)) == Some{ps} : Maybe<&2, List<&2, Tl.Part>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      match p:
        case Tl.Part{o, s}:
          match s:
            case True{}:
              %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, FSh.parts.of(Shell.spell_parts(t)), Some{t}, sh.parts_rt(t)) : {FSh.parts.cons(Some{Tl.Part{o, True{}}}, _) == Some{Tl.Part{o, True{}} <> t} : Maybe<&2, List<&2, Tl.Part>>}
              {==}
            case False{}:
              %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, FSh.parts.of(Shell.spell_parts(t)), Some{t}, sh.parts_rt(t)) : {FSh.parts.cons(Some{Tl.Part{o, False{}}}, _) == Some{Tl.Part{o, False{}} <> t} : Maybe<&2, List<&2, Tl.Part>>}
              {==}

def sh.rt_step(+a: List<&2, Nat>, +ps: List<&2, Tl.Part>, +rest: String, +fits: {Shell.req_fits(FSh.QStep{a, ps}) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(FSh.QStep{a, ps}, rest)) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}:
  +sp = Shell.spell_parts(ps)
  +f = Fl.flat(sp)
  +ha = LLogicBool.wr_and_l(Shell.ns_fit(a), Shell.ns_fit(f), fits)
  +hf = LLogicBool.wr_and_r(Shell.ns_fit(a), Shell.ns_fit(f), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(a, Shell.spell_ns(f, rest))), Wr.Got{a, Shell.spell_ns(f, rest)}, Wire.wire_list_round_trip(a, Shell.spell_ns(f, rest), ha)) : {FSh.get_step(_) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(f, rest)), Wr.Got{f, rest}, Wire.wire_list_round_trip(f, rest, hf)) : {FSh.get_step.flat(a, _) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(f), Some{sp}, LWire.fe.unflat_flat(sp)) : {FSh.get_step.parts(a, FSh.parts.flat(_), rest) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, FSh.parts.of(sp), Some{ps}, sh.parts_rt(ps)) : {FSh.get_step.parts(a, _, rest) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  {==}

def sh.rt_allows(+a: List<&2, Nat>, +es: List<&2, Nat>, +rest: String, +fits: {Shell.req_fits(FSh.QAllows{a, es}) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(FSh.QAllows{a, es}, rest)) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}:
  +ha = LLogicBool.wr_and_l(Shell.ns_fit(a), Shell.ns_fit(es), fits)
  +he = LLogicBool.wr_and_r(Shell.ns_fit(a), Shell.ns_fit(es), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(a, Shell.spell_ns(es, rest))), Wr.Got{a, Shell.spell_ns(es, rest)}, Wire.wire_list_round_trip(a, Shell.spell_ns(es, rest), ha)) : {FSh.get_allows(_) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(es, rest)), Wr.Got{es, rest}, Wire.wire_list_round_trip(es, rest, he)) : {FSh.get_allows.effs(a, _) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}
  {==}

def sh.rt_answer(+i: Nat, y: Bool, +rest: String, fits: {Shell.req_fits(FSh.QAnswer{i, y}) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(FSh.QAnswer{i, y}, rest)) == Wr.Got{FSh.QAnswer{i, y}, rest} : Wr.Dec<FSh.Req>}:
  match y:
    case True{}:
      %LWire.pw6.nat(i, Wr.put_bool(True{}, rest), fits) : {FSh.get_answer(_) == Wr.Got{FSh.QAnswer{i, True{}}, rest} : Wr.Dec<FSh.Req>}
      {==}
    case False{}:
      %LWire.pw6.nat(i, Wr.put_bool(False{}, rest), fits) : {FSh.get_answer(_) == Wr.Got{FSh.QAnswer{i, False{}}, rest} : Wr.Dec<FSh.Req>}
      {==}

def sh.rt(q: FSh.Req, +rest: String, fits: {Shell.req_fits(q) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSh.Req>}:
  match q:
    case FSh.QStep{a, ps}:
      sh.rt_step(a, ps, rest, fits)
    case FSh.QAllows{a, es}:
      sh.rt_allows(a, es, rest, fits)
    case FSh.QAnswer{i, y}:
      sh.rt_answer(i, y, rest, fits)

# Lists and Bools
# ---------------

def sh.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %sh.app_nil(A, t) : {x <> List.append(&2, A, t, Nil{}) == x <> _ : List<&2, A>}
      {==}

def sh.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %sh.app_assoc(A, t, ys, zs) : {x <> List.append(&2, A, List.append(&2, A, t, ys), zs) == x <> _ : List<&2, A>}
      {==}

def sh.and_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}
