# proof_approvals: the lemmas PROOF.bend proves the (G5) laws with
# (laws/approvals.bend), about the model in bend/approvals.bend.

import Base
import ./tools.bend as Tl
import ./approvals.bend as Am
import ./proof_shell.bend as Ps

# Logic
# -----

def pa.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pa.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pa.BD(_, A, Unit)
  Unit{}

def pa.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pa.BD(_, Unit, A)
  Unit{}

# Unanswered{} is A, an answer or a ruling is Unit
def pa.ED(e: Am.End, a: Type, u: Type) -> Type:
  match e:
    case Am.Answered{x, y}:
      u
    case Am.Unanswered{}:
      a
    case Am.Ruled{x}:
      u

def pa.absurdE(-A: Type, -x: Nat, -y: Bool, e: {Am.Answered{x, y} == Am.Unanswered{} : Am.End}) -> A:
  %e : pa.ED(_, A, Unit)
  Unit{}

def pa.absurdR(-A: Type, -x: Nat, e: {Am.Ruled{x} == Am.Unanswered{} : Am.End}) -> A:
  %e : pa.ED(_, A, Unit)
  Unit{}

# Outcomes
# --------

def pa.end_up(o: Am.Out) -> {Am.Out.end(Am.Out.up(o)) == Am.End.up(Am.Out.end(o)) : Am.End}:
  match o:
    case Am.Out{s, e}:
      {==}

def pa.end_first(o: Am.Out) -> {Am.Out.end(Am.Out.first(o)) == Am.Out.end(o) : Am.End}:
  match o:
    case Am.Out{s, e}:
      {==}

# the end of a parent's outcome seen from its child, by the parent's end
def pa.end_up_is(+o: Am.Out, -e: Am.End, h: {Am.Out.end(o) == e : Am.End}) -> {Am.Out.end(Am.Out.up(o)) == Am.End.up(e) : Am.End}:
  Equal.trans(Am.End, Am.Out.end(Am.Out.up(o)), Am.End.up(Am.Out.end(o)), Am.End.up(e), pa.end_up(o), Equal.cong(Am.End, Am.End, x => Am.End.up(x), Am.Out.end(o), e, h))

# so for a session that showed the question first
def pa.end_first_up_is(+o: Am.Out, -e: Am.End, h: {Am.Out.end(o) == e : Am.End}) -> {Am.Out.end(Am.Out.first(Am.Out.up(o))) == Am.End.up(e) : Am.End}:
  Equal.trans(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(o))), Am.Out.end(Am.Out.up(o)), Am.End.up(e), pa.end_first(Am.Out.up(o)), pa.end_up_is(o, e, h))

# a parent's end that is unanswered from its child is unanswered
def pa.up_unanswered(e: Am.End, h: {Am.End.up(e) == Am.Unanswered{} : Am.End}) -> {e == Am.Unanswered{} : Am.End}:
  match e:
    case Am.Answered{x, y}:
      pa.absurdE({Am.Answered{x, y} == Am.Unanswered{} : Am.End}, 1n+x, y, h)
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{x}:
      pa.absurdR({Am.Ruled{x} == Am.Unanswered{} : Am.End}, 1n+x, h)

# The laws
# --------

def pa.nearest(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +yes: Bool, +above: List<&2, Am.Desk>) -> {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}:
  match below:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.end_up_is(Am.route(List.append(&2, Am.Desk, rest, Am.Says{yes} <> above)), Am.Answered{List.length(&2, Am.Desk, rest), yes}, pa.nearest(rest, quiet, yes, above))
        case Am.Left{}:
          pa.end_first_up_is(Am.route(List.append(&2, Am.Desk, rest, Am.Says{yes} <> above)), Am.Answered{List.length(&2, Am.Desk, rest), yes}, pa.nearest(rest, quiet, yes, above))
        case Am.Says{z}:
          pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.Says{z} <> rest), yes} : Am.End}, quiet)
        case Am.Phone{}:
          pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.Phone{} <> rest), yes} : Am.End}, quiet)
        case Am.PhoneLeft{}:
          pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, Am.Says{yes} <> above))) == Am.Answered{List.length(&2, Am.Desk, Am.PhoneLeft{} <> rest), yes} : Am.End}, quiet)

def pa.root(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +yes: Bool) -> {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, [Am.Says{yes}]))) == Am.Answered{List.length(&2, Am.Desk, below), yes} : Am.End}:
  pa.nearest(below, quiet, yes, Nil{})

def pa.only_quiet(+ds: List<&2, Am.Desk>, none: {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}) -> {Am.quiet(ds) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.only_quiet(rest, pa.up_unanswered(Am.Out.end(Am.route(rest)), Equal.trans(Am.End, Am.End.up(Am.Out.end(Am.route(rest))), Am.Out.end(Am.Out.up(Am.route(rest))), Am.Unanswered{}, Equal.sym(Am.End, Am.Out.end(Am.Out.up(Am.route(rest))), Am.End.up(Am.Out.end(Am.route(rest))), pa.end_up(Am.route(rest))), none)))
        case Am.Left{}:
          pa.only_quiet(rest, pa.up_unanswered(Am.Out.end(Am.route(rest)), Equal.trans(Am.End, Am.End.up(Am.Out.end(Am.route(rest))), Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.Unanswered{}, Equal.sym(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.End.up(Am.Out.end(Am.route(rest))), Equal.trans(Am.End, Am.Out.end(Am.Out.first(Am.Out.up(Am.route(rest)))), Am.Out.end(Am.Out.up(Am.route(rest))), Am.End.up(Am.Out.end(Am.route(rest))), pa.end_first(Am.Out.up(Am.route(rest))), pa.end_up(Am.route(rest)))), none)))
        case Am.Says{y}:
          pa.absurdE({Am.quiet(Am.Says{y} <> rest) == True{} : Bool}, 0n, y, none)
        case Am.Phone{}:
          pa.absurdR({Am.quiet(Am.Phone{} <> rest) == True{} : Bool}, 0n, none)
        case Am.PhoneLeft{}:
          pa.absurdR({Am.quiet(Am.PhoneLeft{} <> rest) == True{} : Bool}, 0n, none)

def pa.quiet_none(+ds: List<&2, Am.Desk>, quiet: {Am.quiet(ds) == True{} : Bool}) -> {Am.Out.end(Am.route(ds)) == Am.Unanswered{} : Am.End}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.end_up_is(Am.route(rest), Am.Unanswered{}, pa.quiet_none(rest, quiet))
        case Am.Left{}:
          pa.end_first_up_is(Am.route(rest), Am.Unanswered{}, pa.quiet_none(rest, quiet))
        case Am.Says{y}:
          pa.absurdF({Am.Out.end(Am.route(Am.Says{y} <> rest)) == Am.Unanswered{} : Am.End}, quiet)
        case Am.Phone{}:
          pa.absurdF({Am.Out.end(Am.route(Am.Phone{} <> rest)) == Am.Unanswered{} : Am.End}, quiet)
        case Am.PhoneLeft{}:
          pa.absurdF({Am.Out.end(Am.route(Am.PhoneLeft{} <> rest)) == Am.Unanswered{} : Am.End}, quiet)

# The gateway rule
# ----------------

def pa.never_waits(+above: List<&2, Am.Desk>) -> {Am.route(Am.Phone{} <> above) == Am.Out{Nil{}, Am.Ruled{0n}} : Am.Out}:
  {==}

def pa.left_to_gateway(+above: List<&2, Am.Desk>) -> {Am.route(Am.PhoneLeft{} <> above) == Am.Out{[0n], Am.Ruled{0n}} : Am.Out}:
  {==}

# the guard refuses when its first part holds
def pa.guard_first(b1: Bool, b2: Bool, h: {b1 == True{} : Bool}) -> {Am.guard(Bool.or(b1, b2)) == Am.GatewayRefused{} : Am.Fate}:
  match b1:
    case True{}:
      {==}
    case False{}:
      pa.absurdF({Am.guard(Bool.or(False{}, b2)) == Am.GatewayRefused{} : Am.Fate}, h)

# and when its second part holds
def pa.guard_second(b1: Bool, b2: Bool, h: {b2 == True{} : Bool}) -> {Am.guard(Bool.or(b1, b2)) == Am.GatewayRefused{} : Am.Fate}:
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          pa.absurdF({Am.guard(Bool.or(False{}, False{})) == Am.GatewayRefused{} : Am.Fate}, h)

# it lets the step run when neither holds
def pa.guard_neither(b1: Bool, b2: Bool, h1: {b1 == False{} : Bool}, h2: {b2 == False{} : Bool}) -> {Am.guard(Bool.or(b1, b2)) == Am.Runs{} : Am.Fate}:
  match b1:
    case True{}:
      pa.absurdT({Am.guard(Bool.or(True{}, b2)) == Am.Runs{} : Am.Fate}, h1)
    case False{}:
      match b2:
        case True{}:
          pa.absurdT({Am.guard(Bool.or(False{}, True{})) == Am.Runs{} : Am.Fate}, h2)
        case False{}:
          {==}

def pa.refuses_protected(+es: List<&2, Nat>, protected: {Tl.elem(es, 5n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}:
  pa.guard_first(Tl.elem(es, 5n), Tl.elem(es, 6n), protected)

def pa.refuses_secret(+es: List<&2, Nat>, secret: {Tl.elem(es, 6n) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.GatewayRefused{} : Am.Fate}:
  pa.guard_second(Tl.elem(es, 5n), Tl.elem(es, 6n), secret)

def pa.runs_the_rest(+es: List<&2, Nat>, not_protected: {Tl.elem(es, 5n) == False{} : Bool}, not_secret: {Tl.elem(es, 6n) == False{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(Am.Phone{} <> above))) == Am.Runs{} : Am.Fate}:
  pa.guard_neither(Tl.elem(es, 5n), Tl.elem(es, 6n), not_protected, not_secret)

# a step fares the same whichever session's end it is seen from
def pa.fate_up(+es: List<&2, Nat>, e: Am.End) -> {Am.fate(es, Am.End.up(e)) == Am.fate(es, e) : Am.Fate}:
  match e:
    case Am.Answered{a, y}:
      {==}
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{a}:
      {==}

# so for a session that hands the question up
def pa.fate_up_is(+es: List<&2, Nat>, +o: Am.Out, -t: Am.Fate, h: {Am.fate(es, Am.Out.end(o)) == t : Am.Fate}) -> {Am.fate(es, Am.Out.end(Am.Out.up(o))) == t : Am.Fate}:
  match o:
    case Am.Out{s, e}:
      Equal.trans(Am.Fate, Am.fate(es, Am.End.up(e)), Am.fate(es, e), t, pa.fate_up(es, e), h)

# and for one that showed it first
def pa.fate_first_up_is(+es: List<&2, Nat>, +o: Am.Out, -t: Am.Fate, h: {Am.fate(es, Am.Out.end(o)) == t : Am.Fate}) -> {Am.fate(es, Am.Out.end(Am.Out.first(Am.Out.up(o)))) == t : Am.Fate}:
  match o:
    case Am.Out{s, e}:
      Equal.trans(Am.Fate, Am.fate(es, Am.End.up(e)), Am.fate(es, e), t, pa.fate_up(es, e), h)

def pa.subagent(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +es: List<&2, Nat>, +above: List<&2, Am.Desk>) -> {Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, below, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}:
  match below:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Am.Away{}:
          pa.fate_up_is(es, Am.route(List.append(&2, Am.Desk, rest, Am.Phone{} <> above)), Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), pa.subagent(rest, quiet, es, above))
        case Am.Left{}:
          pa.fate_first_up_is(es, Am.route(List.append(&2, Am.Desk, rest, Am.Phone{} <> above)), Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))), pa.subagent(rest, quiet, es, above))
        case Am.Says{z}:
          pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)
        case Am.Phone{}:
          pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)
        case Am.PhoneLeft{}:
          pa.absurdF({Am.fate(es, Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, Am.Phone{} <> above)))) == Am.fate(es, Am.Out.end(Am.route([Am.Phone{}]))) : Am.Fate}, quiet)

# The auto set
# ------------

def pa.default_auto(+c: Nat) -> {Tl.elem(Am.default_auto(), c) == Tl.grantable(c) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+d:
              match d:
                case 0n:
                  {==}
                case 1n+e:
                  {==}

# a step not within the auto set goes its route
def pa.gate_routed(w: Bool, +es: List<&2, Nat>, +ds: List<&2, Am.Desk>, h: {w == False{} : Bool}) -> {Am.gate.by(w, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}:
  match w:
    case True{}:
      pa.absurdT({Am.gate.by(True{}, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}, h)
    case False{}:
      {==}

def pa.never_auto(+auto: List<&2, Nat>, +es: List<&2, Nat>, +c: Nat, has: {Tl.elem(es, c) == True{} : Bool}, held: {Nat.is_le(4n, c) == True{} : Bool}, +ds: List<&2, Am.Desk>) -> {Am.gate(auto, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}:
  pa.gate_routed(Tl.within(es, auto), es, ds, Ps.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, c, has, held))

def pa.never_auto_asks(+auto: List<&2, Nat>, +es: List<&2, Nat>, +c: Nat, has: {Tl.elem(es, c) == True{} : Bool}, held: {Nat.is_le(4n, c) == True{} : Bool}, +yes: Bool, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Says{yes} <> above) == Am.Routed{Am.Out{[0n], Am.Answered{0n, yes}}, Am.yes.fate(yes)} : Am.Gated}:
  pa.never_auto(auto, es, c, has, held, Am.Says{yes} <> above)

# the gateway's outcome as the gate gives it
def pa.phone_gate(+auto: List<&2, Nat>, +es: List<&2, Nat>, +above: List<&2, Am.Desk>, -f: Am.Fate, w: {Tl.within(es, auto) == False{} : Bool}, r: {Am.rule(es) == f : Am.Fate}) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, f} : Am.Gated}:
  Equal.trans(Am.Gated, Am.gate(auto, es, Am.Phone{} <> above), Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.rule(es)}, Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, f}, pa.gate_routed(Tl.within(es, auto), es, Am.Phone{} <> above, w), Equal.cong(Am.Fate, Am.Gated, x => Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, x}, Am.rule(es), f, r))

def pa.outside_by_gateway(+auto: List<&2, Nat>, +es: List<&2, Nat>, outside: {Tl.elem(es, 4n) == True{} : Bool}, not_protected: {Tl.elem(es, 5n) == False{} : Bool}, not_secret: {Tl.elem(es, 6n) == False{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.Runs{}} : Am.Gated}:
  pa.phone_gate(auto, es, above, Am.Runs{}, Ps.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 4n, outside, {==}), pa.guard_neither(Tl.elem(es, 5n), Tl.elem(es, 6n), not_protected, not_secret))

# a guarded step is never within the auto set
def pa.guarded_not_within(+auto: List<&2, Nat>, +es: List<&2, Nat>, b1: Bool, e1: {Tl.elem(es, 5n) == b1 : Bool}, b2: Bool, e2: {Tl.elem(es, 6n) == b2 : Bool}, g: {Bool.or(b1, b2) == True{} : Bool}) -> {Tl.within(es, auto) == False{} : Bool}:
  match b1:
    case True{}:
      Ps.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 5n, e1, {==})
    case False{}:
      match b2:
        case True{}:
          Ps.ps.auto_never_sensitive(Tl.Step{0n, es}, auto, 6n, e2, {==})
        case False{}:
          pa.absurdF({Tl.within(es, auto) == False{} : Bool}, g)

def pa.guard_true(b: Bool, h: {b == True{} : Bool}) -> {Am.guard(b) == Am.GatewayRefused{} : Am.Fate}:
  match b:
    case True{}:
      {==}
    case False{}:
      pa.absurdF({Am.guard(False{}) == Am.GatewayRefused{} : Am.Fate}, h)

def pa.guarded_from_phone(+auto: List<&2, Nat>, +es: List<&2, Nat>, +guarded: {Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.GatewayRefused{}} : Am.Gated}:
  pa.phone_gate(auto, es, above, Am.GatewayRefused{}, pa.guarded_not_within(auto, es, Tl.elem(es, 5n), {==}, Tl.elem(es, 6n), {==}, guarded), pa.guard_true(Bool.or(Tl.elem(es, 5n), Tl.elem(es, 6n)), guarded))
