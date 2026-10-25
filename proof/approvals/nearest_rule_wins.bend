# eukhe: the proof of LAW nearest_rule_wins
# PROOF: by induction on the quiet sessions below: each is away or left,
# so its outcome is its parent's, one session further (pa.end_up_is,
# pa.end_first_up_is); the gateway's session rules itself (Ruled{0}).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/route.bend as Approvals
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pr.near(+below: List<&2, Am.Desk>, quiet: {Am.quiet(below) == True{} : Bool}, +w: Am.Desk, +above: List<&2, Am.Desk>, base: {Am.Out.end(Am.route(w <> above)) == Am.Ruled{0n} : Am.End}) -> {Am.Out.end(Am.route(List.append(&2, Am.Desk, below, w <> above))) == Am.Ruled{List.length(&2, Am.Desk, below)} : Am.End}:
  match below:
    case Nil{}:
      base
    case d <> +rest:
      match d:
        case Am.Away{}:
          LA.pa.end_up_is(Am.route(List.append(&2, Am.Desk, rest, w <> above)), Am.Ruled{List.length(&2, Am.Desk, rest)}, pr.near(rest, quiet, w, above, base))
        case Am.Left{}:
          LA.pa.end_first_up_is(Am.route(List.append(&2, Am.Desk, rest, w <> above)), Am.Ruled{List.length(&2, Am.Desk, rest)}, pr.near(rest, quiet, w, above, base))
        case Am.Says{z}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Says{z} <> rest, w <> above))) == Am.Ruled{List.length(&2, Am.Desk, Am.Says{z} <> rest)} : Am.End}, quiet)
        case Am.Phone{}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.Phone{} <> rest, w <> above))) == Am.Ruled{List.length(&2, Am.Desk, Am.Phone{} <> rest)} : Am.End}, quiet)
        case Am.PhoneLeft{}:
          LLogicLogic.approvals.pa.absurdF({Am.Out.end(Am.route(List.append(&2, Am.Desk, Am.PhoneLeft{} <> rest, w <> above))) == Am.Ruled{List.length(&2, Am.Desk, Am.PhoneLeft{} <> rest)} : Am.End}, quiet)

def Approvals.nearest_rule_wins(below, quiet, above):
  +q = quiet
  (pr.near(below, q, Am.Phone{}, above, {==}), pr.near(below, q, Am.PhoneLeft{}, above, {==}))
