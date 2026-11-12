# eukhe: the proof of LAW left_to_the_gateway_stays
# PROOF: by induction on the quiet sessions below: each is away or left,
# so its outcome is its parent's, one session further (Out.up, and
# Out.first for a left session), the same function of the rest on both
# chains; the session the clients left ends it (Out{[0], Ruled{0}})
# whatever is above. The shown sessions: one session further is every
# shown index plus one (ups), which spreads over the append (pl.ups_app).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/route.bend as Approvals
import ../base/logic/logic.bend as LLogicLogic

def pl.same(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +above: List<&2, Am.Desk>) -> {Am.route(List.append(&2, Am.Desk, below, Am.PhoneLeft{} <> above)) == Am.route(List.append(&2, Am.Desk, below, [Am.PhoneLeft{}])) : Am.Out}:
  match below:
    case Nil{}:
      {==}
    case d <> +rest:
      match d:
        case Am.Away{}:
          Equal.cong(Am.Out, Am.Out, o => Am.Out.up(o), Am.route(List.append(&2, Am.Desk, rest, Am.PhoneLeft{} <> above)), Am.route(List.append(&2, Am.Desk, rest, [Am.PhoneLeft{}])), pl.same(rest, quiet, above))
        case Am.Left{}:
          Equal.cong(Am.Out, Am.Out, o => Am.Out.first(Am.Out.up(o)), Am.route(List.append(&2, Am.Desk, rest, Am.PhoneLeft{} <> above)), Am.route(List.append(&2, Am.Desk, rest, [Am.PhoneLeft{}])), pl.same(rest, quiet, above))
        case Am.Says{z}:
          LLogicLogic.approvals.pa.absurdF({Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, Am.PhoneLeft{} <> above)) == Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, [Am.PhoneLeft{}])) : Am.Out}, quiet)
        case Am.Phone{}:
          LLogicLogic.approvals.pa.absurdF({Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, Am.PhoneLeft{} <> above)) == Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, [Am.PhoneLeft{}])) : Am.Out}, quiet)
        case Am.PhoneLeft{}:
          LLogicLogic.approvals.pa.absurdF({Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, Am.PhoneLeft{} <> above)) == Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, [Am.PhoneLeft{}])) : Am.Out}, quiet)

# one session further: every shown index plus one
def pl.shown_up(o: Am.Out) -> {Am.Out.shown(Am.Out.up(o)) == Am.ups(Am.Out.shown(o)) : List<&2, Nat>}:
  match o:
    case Am.Out{s, e}:
      {==}

# and with this session first
def pl.shown_first_up(o: Am.Out) -> {Am.Out.shown(Am.Out.first(Am.Out.up(o))) == 0n <> Am.ups(Am.Out.shown(o)) : List<&2, Nat>}:
  match o:
    case Am.Out{s, e}:
      {==}

def pl.ups_app(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Am.ups(List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Am.ups(xs), Am.ups(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => (1n+x) <> z, Am.ups(List.append(&2, Nat, t, ys)), List.append(&2, Nat, Am.ups(t), Am.ups(ys)), pl.ups_app(t, ys))

def pl.shown(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}) -> {Am.Out.shown(Am.route(List.append(&2, Am.Desk, below, [Am.PhoneLeft{}]))) == List.append(&2, Nat, Am.Out.shown(Am.route(below)), [List.length(&2, Am.Desk, below)]) : List<&2, Nat>}:
  match below:
    case Nil{}:
      {==}
    case d <> +rest:
      match d:
        case Am.Away{}:
          +O1 = Am.route(List.append(&2, Am.Desk, rest, [Am.PhoneLeft{}]))
          +O0 = Am.route(rest)
          +L = {[List.length(&2, Am.Desk, rest)] : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(Am.Out.up(O1)), Am.ups(Am.Out.shown(O1)), pl.shown_up(O1)) : {_ == List.append(&2, Nat, Am.Out.shown(Am.Out.up(O0)), Am.ups(L)) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(Am.Out.up(O0)), Am.ups(Am.Out.shown(O0)), pl.shown_up(O0)) : {Am.ups(Am.Out.shown(O1)) == List.append(&2, Nat, _, Am.ups(L)) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(O1), List.append(&2, Nat, Am.Out.shown(O0), L), pl.shown(rest, quiet)) : {Am.ups(_) == List.append(&2, Nat, Am.ups(Am.Out.shown(O0)), Am.ups(L)) : List<&2, Nat>}
          pl.ups_app(Am.Out.shown(O0), L)
        case Am.Left{}:
          +O1 = Am.route(List.append(&2, Am.Desk, rest, [Am.PhoneLeft{}]))
          +O0 = Am.route(rest)
          +L = {[List.length(&2, Am.Desk, rest)] : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(Am.Out.first(Am.Out.up(O1))), 0n <> Am.ups(Am.Out.shown(O1)), pl.shown_first_up(O1)) : {_ == List.append(&2, Nat, Am.Out.shown(Am.Out.first(Am.Out.up(O0))), Am.ups(L)) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(Am.Out.first(Am.Out.up(O0))), 0n <> Am.ups(Am.Out.shown(O0)), pl.shown_first_up(O0)) : {0n <> Am.ups(Am.Out.shown(O1)) == List.append(&2, Nat, _, Am.ups(L)) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, Am.Out.shown(O1), List.append(&2, Nat, Am.Out.shown(O0), L), pl.shown(rest, quiet)) : {0n <> Am.ups(_) == 0n <> List.append(&2, Nat, Am.ups(Am.Out.shown(O0)), Am.ups(L)) : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, Am.ups(List.append(&2, Nat, Am.Out.shown(O0), L)), List.append(&2, Nat, Am.ups(Am.Out.shown(O0)), Am.ups(L)), pl.ups_app(Am.Out.shown(O0), L))
        case Am.Says{z}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.shown(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, [Am.PhoneLeft{}]))) == List.append(&2, Nat, Am.Out.shown(Am.route(Am.Says{z} <> rest)), [List.length(&2, Am.Desk, Am.Says{z} <> rest)]) : List<&2, Nat>}, quiet)
        case Am.Phone{}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.shown(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, [Am.PhoneLeft{}]))) == List.append(&2, Nat, Am.Out.shown(Am.route(Am.Phone{} <> rest)), [List.length(&2, Am.Desk, Am.Phone{} <> rest)]) : List<&2, Nat>}, quiet)
        case Am.PhoneLeft{}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.shown(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, [Am.PhoneLeft{}]))) == List.append(&2, Nat, Am.Out.shown(Am.route(Am.PhoneLeft{} <> rest)), [List.length(&2, Am.Desk, Am.PhoneLeft{} <> rest)]) : List<&2, Nat>}, quiet)

def Approvals.left_to_the_gateway_stays(below, quiet, above):
  +q = quiet
  (pl.same(below, q, above), pl.shown(below, q))
