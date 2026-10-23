# eukhe: the proof of LAW path_policy_ffi_request_round_trip

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../bend/ffi_path_policy.bend as FPp
import ../../LAWS.bend as Laws
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# path_policy
# -----------

def fe.rules_of(rs: List<&2, Pp.Rule>) -> {FPp.rules.of(FPp.rules(rs)) == Some{rs} : Maybe<&2, List<&2, Pp.Rule>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Pp.Tree{+p}:
          %Equal.sym(Maybe<&2, List<&2, Pp.Rule>>, FPp.rules.of(FPp.rules(rest)), Some{rest}, fe.rules_of(rest)) : {FPp.rules.cons(Some{Pp.Tree{p}}, _) == Some{Pp.Tree{p} <> rest} : Maybe<&2, List<&2, Pp.Rule>>}
          {==}
        case Pp.Dir{+p}:
          %Equal.sym(Maybe<&2, List<&2, Pp.Rule>>, FPp.rules.of(FPp.rules(rest)), Some{rest}, fe.rules_of(rest)) : {FPp.rules.cons(Some{Pp.Dir{p}}, _) == Some{Pp.Dir{p} <> rest} : Maybe<&2, List<&2, Pp.Rule>>}
          {==}
        case Pp.Named{+n}:
          %Equal.sym(Maybe<&2, List<&2, Pp.Rule>>, FPp.rules.of(FPp.rules(rest)), Some{rest}, fe.rules_of(rest)) : {FPp.rules.cons(Some{Pp.Named{n}}, _) == Some{Pp.Named{n} <> rest} : Maybe<&2, List<&2, Pp.Rule>>}
          {==}

def Laws.path_policy_ffi_request_round_trip(ro, ru, se, at, l, rest, h0):
  +h = h0
  +h3 = L.wr_and_l(Bool.and(Bool.and(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(se))), Laws.wire_nats_fit(Fl.flat(se)))), Bool.and(Laws.wire_fits(List.length(&2, Nat, at)), Laws.wire_nats_fit(at)), h)
  +hat = L.wr_and_r(Bool.and(Bool.and(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(se))), Laws.wire_nats_fit(Fl.flat(se)))), Bool.and(Laws.wire_fits(List.length(&2, Nat, at)), Laws.wire_nats_fit(at)), h)
  +h2 = L.wr_and_l(Bool.and(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(se))), Laws.wire_nats_fit(Fl.flat(se))), h3)
  +hse = L.wr_and_r(Bool.and(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(se))), Laws.wire_nats_fit(Fl.flat(se))), h3)
  +hro = L.wr_and_l(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru)))), h2)
  +hru = L.wr_and_r(Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(ro))), Laws.wire_nats_fit(Fl.flat(ro))), Bool.and(Laws.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), Laws.wire_nats_fit(Fl.flat(FPp.rules(ru)))), h2)
  +r4 = Wr.put_bool(l, rest)
  +r3 = FPp.put_ns(at, r4)
  +r2 = FPp.put_ns(Fl.flat(se), r3)
  +r1 = FPp.put_ns(Fl.flat(FPp.rules(ru)), r2)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, Fl.flat(ro), r1)), Wr.Got{Fl.flat(ro), r1}, Laws.wire_list_round_trip(Fl.flat(ro), r1, hro)) : {FPp.get_req.roots(_) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, Fl.flat(FPp.rules(ru)), r2)), Wr.Got{Fl.flat(FPp.rules(ru)), r2}, Laws.wire_list_round_trip(Fl.flat(FPp.rules(ru)), r2, hru)) : {FPp.get_req.rule_list(Fl.flat(ro), _) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, Fl.flat(se), r3)), Wr.Got{Fl.flat(se), r3}, Laws.wire_list_round_trip(Fl.flat(se), r3, hse)) : {FPp.get_req.secret(Fl.flat(ro), Fl.flat(FPp.rules(ru)), _) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, at, r4)), Wr.Got{at, r4}, Laws.wire_list_round_trip(at, r4, hat)) : {FPp.get_req.at(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), _) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(l, rest)), Wr.Got{l, rest}, Laws.wire_bool_round_trip(l, rest)) : {FPp.get_req.looped(Fl.flat(ro), Fl.flat(FPp.rules(ru)), Fl.flat(se), at, _) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(Fl.flat(ro)), Some{ro}, L.fe.unflat_flat(ro)) : {FPp.get_req.build(_, FPp.get_req.rules(Fl.unflat(Fl.flat(FPp.rules(ru)))), Fl.unflat(Fl.flat(se)), at, l, rest) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(Fl.flat(FPp.rules(ru))), Some{FPp.rules(ru)}, L.fe.unflat_flat(FPp.rules(ru))) : {FPp.get_req.build(Some{ro}, FPp.get_req.rules(_), Fl.unflat(Fl.flat(se)), at, l, rest) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Maybe<&2, List<&2, Pp.Rule>>, FPp.rules.of(FPp.rules(ru)), Some{ru}, fe.rules_of(ru)) : {FPp.get_req.build(Some{ro}, _, Fl.unflat(Fl.flat(se)), at, l, rest) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(Fl.flat(se)), Some{se}, L.fe.unflat_flat(se)) : {FPp.get_req.build(Some{ro}, Some{ru}, _, at, l, rest) == Wr.Got{FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest} : Wr.Dec<FPp.Req>}
  {==}
