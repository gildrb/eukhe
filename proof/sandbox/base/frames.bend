# eukhe: lemmas the proofs of the frames gate share (laws/sandbox.bend,
# section frames entry)

import Base
import ../../../bend/ffi_frames.bend as FFr
import ../../../bend/sandbox.bend as Sb
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/sandbox.bend as Sandbox
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../base.bend as LA

# The gate
# --------

# b below a: a is not at most b
def fr.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {False{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      LA.px.absurdF({False{} == Nat.is_le(0n, 0n) : Bool}, h)
    case 0n 1n+q:
      LA.px.absurdF({False{} == Nat.is_le(0n, 1n+q) : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fr.lt_nle(p, q, h)

def fr.kind(k: Sb.Typed) -> {Sb.admit.kind(k) == Sandbox.kind_spec(k) : Sb.Verdict}:
  match k:
    case Sb.Unnamed{}:
      {==}
    case Sb.Named{s}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}

def fr.sa(a: Bool, b: Bool) -> {Sb.Verdict.serve(Sb.admit.size(a, Sb.Named{b})) == Bool.and(a, b) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def fr.named(r: Wr.Dec<Bool>) -> {Sandbox.fr_read_named(r) == FFr.get_named(r) : Wr.Dec<Sb.Typed>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fr.kind_tag(t: Nat, s: String) -> {Sandbox.fr_read_kind.tag(t, s) == FFr.get_kind.tag(t, s) : Wr.Dec<Sb.Typed>}:
  match t:
    case 0n:
      {==}
    case 1n:
      fr.named(Wr.get_bool(s))
    case 2n+u:
      {==}

def fr.read_kind(r: Wr.Dec<Nat>) -> {Sandbox.fr_read_kind(r) == FFr.get_kind(r) : Wr.Dec<Sb.Typed>}:
  match r:
    case Wr.Got{t, s}:
      fr.kind_tag(t, s)
    case Wr.Bad{}:
      {==}

def fr.req_kind(m: Nat, f: Bool, l: Nat, r: Wr.Dec<Sb.Typed>) -> {Sandbox.fr_read_req.kind(m, f, l, r) == FFr.get_req.kind(m, f, l, r) : Wr.Dec<FFr.Req>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fr.req_len(+m: Nat, +f: Bool, r: Wr.Dec<Nat>) -> {Sandbox.fr_read_req.len(m, f, r) == FFr.get_req.len(m, f, r) : Wr.Dec<FFr.Req>}:
  match r:
    case Wr.Got{+l, +s}:
      %fr.read_kind(Wr.get_nat(s)) : {Sandbox.fr_read_req.kind(m, f, l, Sandbox.fr_read_kind(Wr.get_nat(s))) == FFr.get_req.kind(m, f, l, _) : Wr.Dec<FFr.Req>}
      fr.req_kind(m, f, l, Sandbox.fr_read_kind(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def fr.req_fresh(m: Nat, r: Wr.Dec<Bool>) -> {Sandbox.fr_read_req.fresh(m, r) == FFr.get_req.fresh(m, r) : Wr.Dec<FFr.Req>}:
  match r:
    case Wr.Got{f, s}:
      fr.req_len(m, f, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fr.req_max(r: Wr.Dec<Nat>) -> {Sandbox.fr_read_req.max(r) == FFr.get_req.max(r) : Wr.Dec<FFr.Req>}:
  match r:
    case Wr.Got{m, s}:
      fr.req_fresh(m, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def fr.req(s: String) -> {Sandbox.fr_read_req(s) == FFr.get_req(s) : Wr.Dec<FFr.Req>}:
  fr.req_max(Wr.get_nat(s))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def fr.verdict(v: Sb.Verdict) -> {FFr.put_verdict(v, "") == Sandbox.fr_spell_verdict(v) : String}:
  match v:
    case Sb.Serve{}:
      {==}
    case Sb.Duplicate{}:
      {==}
    case Sb.Oversize{}:
      {==}
    case Sb.Kindless{}:
      {==}
    case Sb.NotServed{}:
      {==}

def fr.reply(q: FFr.Req) -> {FFr.answer(q) == Sandbox.fr_spell_answer(q) : String}:
  match q:
    case FFr.Req{+m, +f, +l, +k}:
      fr.verdict(Sb.admit(m, f, l, k))

def fr.end(b: Bool, q: FFr.Req) -> {FFr.run.end(b, q) == Sandbox.fr_spec.end(b, q) : String}:
  match b:
    case True{}:
      fr.reply(q)
    case False{}:
      {==}

def fr.run(r: Wr.Dec<FFr.Req>) -> {FFr.run(r) == Sandbox.fr_spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      fr.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def fr.exact(+s: String) -> {FFr.ffi(s) == Sandbox.fr_spec(s) : String}:
  %fr.req(s) : {FFr.run(_) == Sandbox.fr_spec(s) : String}
  fr.run(Sandbox.fr_read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def fr.rt_bool(f: Bool, rest: String) -> {Wr.get_bool(Wr.put_bool(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Bool>}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def fr.rt_kind(k: Sb.Typed, rest: String) -> {Sandbox.fr_read_kind(Wr.get_nat(Sandbox.fr_spell_kind(k, rest))) == Wr.Got{k, rest} : Wr.Dec<Sb.Typed>}:
  match k:
    case Sb.Unnamed{}:
      {==}
    case Sb.Named{s}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}

def fr.rt(q: FFr.Req, +rest: String, +fits: {Sandbox.fr_req_fits(q) == True{} : Bool}) -> {Sandbox.fr_read_req(Sandbox.fr_spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FFr.Req>}:
  match q:
    case FFr.Req{+m, +f, +l, +k}:
      +kr = Sandbox.fr_spell_kind(k, rest)
      +hm = LLogicBool.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(l), fits)
      +hl = LLogicBool.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(l), fits)
      %LWire.pw6.nat(m, Wr.put_bool(f, Wr.put_nat(l, kr)), hm) : {Sandbox.fr_read_req.max(_) == Wr.Got{FFr.Req{m, f, l, k}, rest} : Wr.Dec<FFr.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(f, Wr.put_nat(l, kr))), Wr.Got{f, Wr.put_nat(l, kr)}, fr.rt_bool(f, Wr.put_nat(l, kr))) : {Sandbox.fr_read_req.fresh(m, _) == Wr.Got{FFr.Req{m, f, l, k}, rest} : Wr.Dec<FFr.Req>}
      %LWire.pw6.nat(l, kr, hl) : {Sandbox.fr_read_req.len(m, f, _) == Wr.Got{FFr.Req{m, f, l, k}, rest} : Wr.Dec<FFr.Req>}
      %Equal.sym(Wr.Dec<Sb.Typed>, Sandbox.fr_read_kind(Wr.get_nat(kr)), Wr.Got{k, rest}, fr.rt_kind(k, rest)) : {Sandbox.fr_read_req.kind(m, f, l, _) == Wr.Got{FFr.Req{m, f, l, k}, rest} : Wr.Dec<FFr.Req>}
      {==}
