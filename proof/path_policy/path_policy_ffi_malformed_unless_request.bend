# eukhe: the proof of LAW path_policy_ffi_malformed_unless_request
#
# PROOF: what the decoder reads is the spelling of a request that fits,
# then the rest it leaves (mu.Q, stage by stage with the list, path and
# rule invariants of path_policy_ffi_reads_only_requests); when it reads
# none the entry answers the malformed error, which the premise excludes.

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./path_policy_ffi_reads_only_requests.bend as PRO

# a request read is the spelling of a request that fits, then the rest
def mu.Q(s: String, d: Wr.Dec<FPp.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == PathPolicy.pp_spell_req(q, r) : String} & {PathPolicy.pp_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the request read: its spelling (each equation used twice) and its fit
def mu.done(+s: String, -a: List<&2, Nat>, -b: List<&2, Nat>, -c: List<&2, Nat>, +at: List<&2, Nat>, +l: Bool, +s5: String, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, +ua: {a == PathPolicy.pp_flat(ro) : List<&2, Nat>}, +ub: {b == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}, +uc: {c == PathPolicy.pp_flat(se) : List<&2, Nat>}) -> mu.Q(s, Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s5}):
  (PRO.ro.pre(s, a, b, c, at, l, s5, ro, ru, se, pre, ua, ub, uc), PRO.ro.fits(a, b, c, at, l, ro, ru, se, fa, fb, fc, fat, ua, ub, uc))

def mu.build(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +at: List<&2, Nat>, +l: Bool, +s5: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, mro: Maybe<&2, List<&2, List<&2, Nat>>>, uro: PRO.ro.UI(a, mro), mru: Maybe<&2, List<&2, Pp.Rule>>, uru: PRO.ro.RI(b, mru), mse: Maybe<&2, List<&2, List<&2, Nat>>>, use: PRO.ro.UI(c, mse)) -> mu.Q(s, FPp.get_req.build(mro, mru, mse, at, l, s5)):
  match mro:
    case None{}:
      Unit{}
    case Some{+ro}:
      match mru:
        case None{}:
          Unit{}
        case Some{+ru}:
          match mse:
            case None{}:
              Unit{}
            case Some{+se}:
              mu.done(s, a, b, c, at, l, s5, ro, ru, se, pre, fa, fb, fc, fat, uro, uru, use)

def mu.looped(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +at: List<&2, Nat>, +s4: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, s4)))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> mu.Q(s, FPp.get_req.looped(a, b, c, at, d)):
  match d:
    case Wr.Got{+l, +s5}:
      mu.build(s, a, b, c, at, l, s5, PRO.ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, z)))), s, s4, Wr.put_bool(l, s5), pre, Wire.wire_bool_exact(s4, l, s5, ed)), fa, fb, fc, fat, Fl.unflat(a), PRO.ro.unflat_inv(a), FPp.get_req.rules(Fl.unflat(b)), PRO.ro.rules_at(b, Fl.unflat(b), PRO.ro.unflat_inv(b)), Fl.unflat(c), PRO.ro.unflat_inv(c))
    case Wr.Bad{}:
      Unit{}

def mu.at(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +s3: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, s3))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: PRO.ro.NL(s3, d)) -> mu.Q(s, FPp.get_req.at(a, b, c, d)):
  match d:
    case Wr.Got{+at, +s4}:
      (e4, fat) = xd
      mu.looped(s, a, b, c, at, s4, PRO.ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, z))), s, s3, LawsBase.wire_spell_nats(at, s4), pre, e4), fa, fb, fc, fat, Wr.get_bool(s4), {==})
    case Wr.Bad{}:
      Unit{}

def mu.secret(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +s2: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, s2)) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: PRO.ro.NL(s2, d)) -> mu.Q(s, FPp.get_req.secret(a, b, d)):
  match d:
    case Wr.Got{+c, +s3}:
      (e3, fc) = xd
      mu.at(s, a, b, c, s3, PRO.ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, z)), s, s2, LawsBase.wire_spell_nats(c, s3), pre, e3), fa, fb, fc, FPp.get_ns(s3), PRO.ro.nl(s3))
    case Wr.Bad{}:
      Unit{}

def mu.rules(+s: String, +a: List<&2, Nat>, +s1: String, pre: {s == LawsBase.wire_spell_nats(a, s1) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: PRO.ro.NL(s1, d)) -> mu.Q(s, FPp.get_req.rule_list(a, d)):
  match d:
    case Wr.Got{+b, +s2}:
      (e2, fb) = xd
      mu.secret(s, a, b, s2, PRO.ro.step(z => LawsBase.wire_spell_nats(a, z), s, s1, LawsBase.wire_spell_nats(b, s2), pre, e2), fa, fb, FPp.get_ns(s2), PRO.ro.nl(s2))
    case Wr.Bad{}:
      Unit{}

def mu.roots(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: PRO.ro.NL(s, d)) -> mu.Q(s, FPp.get_req.roots(d)):
  match d:
    case Wr.Got{+a, +s1}:
      (e1, fa) = xd
      mu.rules(s, a, s1, e1, fa, FPp.get_ns(s1), PRO.ro.nl(s1))
    case Wr.Bad{}:
      Unit{}

def mu.goal(+s: String) -> Type:
  &q: FPp.Req -> &rest: String -> {(s, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}

def mu.eq(+s: String, +q: FPp.Req, +rest: String, e1: {s == PathPolicy.pp_spell_req(q, rest) : String}, e2: {PathPolicy.pp_req_fits(q) == True{} : Bool}) -> {(s, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, PathPolicy.pp_spell_req(q, rest), e1) : {(_, PathPolicy.pp_req_fits(q)) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}
  %Equal.sym(Bool, PathPolicy.pp_req_fits(q), True{}, e2) : {(PathPolicy.pp_spell_req(q, rest), _) == (PathPolicy.pp_spell_req(q, rest), True{}) : String & Bool}
  {==}

def mu.main(+s: String, d: Wr.Dec<FPp.Req>, inv: mu.Q(s, d), other: {String.eq(FPp.answer(d), Wr.err("path_policy: malformed request")) == False{} : Bool}) -> mu.goal(s):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = inv
      (q, (rest, mu.eq(s, q, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mu.goal(s), other)

def PathPolicy.path_policy_ffi_malformed_unless_request(s, other):
  mu.main(s, FPp.get_req(s), mu.roots(s, FPp.get_ns(s), PRO.ro.nl(s)), other)
