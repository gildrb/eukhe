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

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def sh.part(xs: List<&2, Nat>) -> {Shell.read_part(xs) == FSh.part.of(xs) : Maybe<&2, Tl.Part>}:
  match xs:
    case Nil{}:
      {==}
    case f <> o:
      match f:
        case 0n:
          {==}
        case 1n+g:
          match g:
            case 0n:
              {==}
            case 1n+h:
              {==}

def sh.cons(m: Maybe<&2, Tl.Part>, ms: Maybe<&2, List<&2, Tl.Part>>) -> {Shell.read_parts.cons(m, ms) == FSh.parts.cons(m, ms) : Maybe<&2, List<&2, Tl.Part>>}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match ms:
        case None{}:
          {==}
        case Some{ps}:
          {==}

def sh.parts(xss: List<&2, List<&2, Nat>>) -> {Shell.read_parts(xss) == FSh.parts.of(xss) : Maybe<&2, List<&2, Tl.Part>>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      %sh.part(xs) : {Shell.read_parts.cons(Shell.read_part(xs), Shell.read_parts(rest)) == FSh.parts.cons(_, FSh.parts.of(rest)) : Maybe<&2, List<&2, Tl.Part>>}
      %sh.parts(rest) : {Shell.read_parts.cons(Shell.read_part(xs), Shell.read_parts(rest)) == FSh.parts.cons(Shell.read_part(xs), _) : Maybe<&2, List<&2, Tl.Part>>}
      sh.cons(Shell.read_part(xs), Shell.read_parts(rest))

def sh.flat(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> {Shell.read_parts.flat(m) == FSh.parts.flat(m) : Maybe<&2, List<&2, Tl.Part>>}:
  match m:
    case None{}:
      {==}
    case Some{xss}:
      sh.parts(xss)

def sh.step_parts(a: List<&2, Nat>, m: Maybe<&2, List<&2, Tl.Part>>, s: String) -> {Shell.read_step.parts(a, m, s) == FSh.get_step.parts(a, m, s) : Wr.Dec<FSh.Req>}:
  match m:
    case None{}:
      {==}
    case Some{ps}:
      {==}

def sh.step_flat(+a: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {Shell.read_step.flat(a, r) == FSh.get_step.flat(a, r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{+ns, +s}:
      %sh.flat(Fl.unflat(ns)) : {Shell.read_step.parts(a, Shell.read_parts.flat(Fl.unflat(ns)), s) == FSh.get_step.parts(a, _, s) : Wr.Dec<FSh.Req>}
      sh.step_parts(a, Shell.read_parts.flat(Fl.unflat(ns)), s)
    case Wr.Bad{}:
      {==}

def sh.step(r: Wr.Dec<List<&2, Nat>>) -> {Shell.read_step(r) == FSh.get_step(r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{a, s}:
      sh.step_flat(a, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def sh.allows_effs(a: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {Shell.read_allows.effs(a, r) == FSh.get_allows.effs(a, r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sh.allows(r: Wr.Dec<List<&2, Nat>>) -> {Shell.read_allows(r) == FSh.get_allows(r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{a, s}:
      sh.allows_effs(a, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def sh.answer_yes(i: Nat, r: Wr.Dec<Bool>) -> {Shell.read_answer.yes(i, r) == FSh.get_answer.yes(i, r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{y, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sh.answer(r: Wr.Dec<Nat>) -> {Shell.read_answer(r) == FSh.get_answer(r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{i, s}:
      sh.answer_yes(i, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def sh.tag(t: Nat, s: String) -> {Shell.read_req.tag(t, s) == FSh.get_req.tag(t, s) : Wr.Dec<FSh.Req>}:
  match t:
    case 0n:
      sh.step(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 1n:
      sh.allows(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      sh.answer(Wr.get_nat(s))
    case 3n+u:
      {==}

def sh.go(r: Wr.Dec<Nat>) -> {Shell.read_req.go(r) == FSh.get_req.go(r) : Wr.Dec<FSh.Req>}:
  match r:
    case Wr.Got{t, s}:
      sh.tag(t, s)
    case Wr.Bad{}:
      {==}

def sh.req(s: String) -> {Shell.read_req(s) == FSh.get_req(s) : Wr.Dec<FSh.Req>}:
  sh.go(Wr.get_nat(s))

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

def sh.end(b: Bool, q: FSh.Req) -> {FSh.run.end(b, q) == Shell.spec.end(b, q) : String}:
  match b:
    case True{}:
      sh.reply(q)
    case False{}:
      {==}

def sh.run(r: Wr.Dec<FSh.Req>) -> {FSh.run(r) == Shell.spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      sh.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def sh.exact(+s: String) -> {FSh.ffi(s) == Shell.spec(s) : String}:
  %sh.req(s) : {FSh.run(_) == Shell.spec(s) : String}
  sh.run(Shell.read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def sh.parts_rt(ps: List<&2, Tl.Part>) -> {Shell.read_parts(Shell.spell_parts(ps)) == Some{ps} : Maybe<&2, List<&2, Tl.Part>>}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      match p:
        case Tl.Part{o, s}:
          match s:
            case True{}:
              %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, Shell.read_parts(Shell.spell_parts(t)), Some{t}, sh.parts_rt(t)) : {Shell.read_parts.cons(Some{Tl.Part{o, True{}}}, _) == Some{Tl.Part{o, True{}} <> t} : Maybe<&2, List<&2, Tl.Part>>}
              {==}
            case False{}:
              %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, Shell.read_parts(Shell.spell_parts(t)), Some{t}, sh.parts_rt(t)) : {Shell.read_parts.cons(Some{Tl.Part{o, False{}}}, _) == Some{Tl.Part{o, False{}} <> t} : Maybe<&2, List<&2, Tl.Part>>}
              {==}

def sh.rt_step(+a: List<&2, Nat>, +ps: List<&2, Tl.Part>, +rest: String, +fits: {Shell.req_fits(FSh.QStep{a, ps}) == True{} : Bool}) -> {Shell.read_req(Shell.spell_req(FSh.QStep{a, ps}, rest)) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}:
  +sp = Shell.spell_parts(ps)
  +f = Fl.flat(sp)
  +ha = LLogicBool.wr_and_l(Shell.ns_fit(a), Shell.ns_fit(f), fits)
  +hf = LLogicBool.wr_and_r(Shell.ns_fit(a), Shell.ns_fit(f), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(a, Shell.spell_ns(f, rest))), Wr.Got{a, Shell.spell_ns(f, rest)}, Wire.wire_list_round_trip(a, Shell.spell_ns(f, rest), ha)) : {Shell.read_step(_) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(f, rest)), Wr.Got{f, rest}, Wire.wire_list_round_trip(f, rest, hf)) : {Shell.read_step.flat(a, _) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(f), Some{sp}, LWire.fe.unflat_flat(sp)) : {Shell.read_step.parts(a, Shell.read_parts.flat(_), rest) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, Tl.Part>>, Shell.read_parts(sp), Some{ps}, sh.parts_rt(ps)) : {Shell.read_step.parts(a, _, rest) == Wr.Got{FSh.QStep{a, ps}, rest} : Wr.Dec<FSh.Req>}
  {==}

def sh.rt_allows(+a: List<&2, Nat>, +es: List<&2, Nat>, +rest: String, +fits: {Shell.req_fits(FSh.QAllows{a, es}) == True{} : Bool}) -> {Shell.read_req(Shell.spell_req(FSh.QAllows{a, es}, rest)) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}:
  +ha = LLogicBool.wr_and_l(Shell.ns_fit(a), Shell.ns_fit(es), fits)
  +he = LLogicBool.wr_and_r(Shell.ns_fit(a), Shell.ns_fit(es), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(a, Shell.spell_ns(es, rest))), Wr.Got{a, Shell.spell_ns(es, rest)}, Wire.wire_list_round_trip(a, Shell.spell_ns(es, rest), ha)) : {Shell.read_allows(_) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(es, rest)), Wr.Got{es, rest}, Wire.wire_list_round_trip(es, rest, he)) : {Shell.read_allows.effs(a, _) == Wr.Got{FSh.QAllows{a, es}, rest} : Wr.Dec<FSh.Req>}
  {==}

def sh.rt_answer(+i: Nat, y: Bool, +rest: String, fits: {Shell.req_fits(FSh.QAnswer{i, y}) == True{} : Bool}) -> {Shell.read_req(Shell.spell_req(FSh.QAnswer{i, y}, rest)) == Wr.Got{FSh.QAnswer{i, y}, rest} : Wr.Dec<FSh.Req>}:
  match y:
    case True{}:
      %LWire.pw6.nat(i, Wr.put_bool(True{}, rest), fits) : {Shell.read_answer(_) == Wr.Got{FSh.QAnswer{i, True{}}, rest} : Wr.Dec<FSh.Req>}
      {==}
    case False{}:
      %LWire.pw6.nat(i, Wr.put_bool(False{}, rest), fits) : {Shell.read_answer(_) == Wr.Got{FSh.QAnswer{i, False{}}, rest} : Wr.Dec<FSh.Req>}
      {==}

def sh.rt(q: FSh.Req, +rest: String, fits: {Shell.req_fits(q) == True{} : Bool}) -> {Shell.read_req(Shell.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSh.Req>}:
  match q:
    case FSh.QStep{a, ps}:
      sh.rt_step(a, ps, rest, fits)
    case FSh.QAllows{a, es}:
      sh.rt_allows(a, es, rest, fits)
    case FSh.QAnswer{i, y}:
      sh.rt_answer(i, y, rest, fits)
