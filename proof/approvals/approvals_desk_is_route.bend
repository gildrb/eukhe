# eukhe: the proof of LAW approvals_desk_is_route
#
# PROOF: by induction on the chain, a case per Desk of its first session.
# Away with a parent: the desk relays (the parent's chain, by induction)
# and the parent's fate wakes the question: the parent's sessions one
# further up, its fate (ir.up: `route` moves every session one up and
# keeps the fate). Left: shown, then the clients leave: relayed the same
# way, with this session first (ir.first). At a root both end unanswered.
# Says: shown, then the answer is taken: the answer's fate. Phone: the
# gateway rule at once. PhoneLeft: shown, then the gateway rule.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk

def ir.ups(xs: List<&2, Nat>) -> {ApprovalsDesk.ch_up(xs) == Am.ups(xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %ir.ups(t) : {(1n+x) <> ApprovalsDesk.ch_up(t) == (1n+x) <> _ : List<&2, Nat>}
      {==}

def ir.fu(+es: List<&2, Nat>, +s: List<&2, Nat>, e: Am.End) -> {(ApprovalsDesk.ch_up(s), Am.fate(es, e)) == (ApprovalsDesk.ch_up(s), Am.fate(es, Am.End.up(e))) : List<&2, Nat> & Am.Fate}:
  match e:
    case Am.Answered{a, y}:
      {==}
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{a}:
      {==}

# `route` one session up: every shown session one further, the same fate
def ir.up(+es: List<&2, Nat>, o: Am.Out) -> {(ApprovalsDesk.ch_up(Am.Out.shown(o)), Am.fate(es, Am.Out.end(o))) == (Am.Out.shown(Am.Out.up(o)), Am.fate(es, Am.Out.end(Am.Out.up(o)))) : List<&2, Nat> & Am.Fate}:
  match o:
    case Am.Out{+s, +e}:
      %ir.ups(s) : {(ApprovalsDesk.ch_up(s), Am.fate(es, e)) == (_, Am.fate(es, Am.End.up(e))) : List<&2, Nat> & Am.Fate}
      ir.fu(es, s, e)

def ir.fu0(+es: List<&2, Nat>, +s: List<&2, Nat>, e: Am.End) -> {(0n <> ApprovalsDesk.ch_up(s), Am.fate(es, e)) == (0n <> ApprovalsDesk.ch_up(s), Am.fate(es, Am.End.up(e))) : List<&2, Nat> & Am.Fate}:
  match e:
    case Am.Answered{a, y}:
      {==}
    case Am.Unanswered{}:
      {==}
    case Am.Ruled{a}:
      {==}

# and with this session first
def ir.first(+es: List<&2, Nat>, o: Am.Out) -> {(0n <> ApprovalsDesk.ch_up(Am.Out.shown(o)), Am.fate(es, Am.Out.end(o))) == (Am.Out.shown(Am.Out.first(Am.Out.up(o))), Am.fate(es, Am.Out.end(Am.Out.first(Am.Out.up(o))))) : List<&2, Nat> & Am.Fate}:
  match o:
    case Am.Out{+s, +e}:
      %ir.ups(s) : {(0n <> ApprovalsDesk.ch_up(s), Am.fate(es, e)) == (0n <> _, Am.fate(es, Am.End.up(e))) : List<&2, Nat> & Am.Fate}
      ir.fu0(es, s, e)

def ApprovalsDesk.approvals_desk_is_route(ds, es):
  match ds:
    case Nil{}:
      {==}
    case d <> +rest:
      match d:
        case Am.Away{}:
          match rest:
            case Nil{}:
              {==}
            case +r <> +rs:
              %Equal.sym(List<&2, Nat> & Am.Fate, ApprovalsDesk.ch_run(r <> rs, es), (Am.Out.shown(Am.route(r <> rs)), Am.fate(es, Am.Out.end(Am.route(r <> rs)))), ApprovalsDesk.approvals_desk_is_route(r <> rs, es)) : {ApprovalsDesk.ch_relayed(Nil{}, _, Am.D{1n, [Am.Q{0n, "q", es, Am.OnParent{}}]}) == (Am.Out.shown(Am.Out.up(Am.route(r <> rs))), Am.fate(es, Am.Out.end(Am.Out.up(Am.route(r <> rs))))) : List<&2, Nat> & Am.Fate}
              ir.up(es, Am.route(r <> rs))
        case Am.Left{}:
          match rest:
            case Nil{}:
              {==}
            case +r <> +rs:
              %Equal.sym(List<&2, Nat> & Am.Fate, ApprovalsDesk.ch_run(r <> rs, es), (Am.Out.shown(Am.route(r <> rs)), Am.fate(es, Am.Out.end(Am.route(r <> rs)))), ApprovalsDesk.approvals_desk_is_route(r <> rs, es)) : {ApprovalsDesk.ch_relayed([0n], _, Am.D{1n, [Am.Q{0n, "q", es, Am.OnParent{}}]}) == (Am.Out.shown(Am.Out.first(Am.Out.up(Am.route(r <> rs)))), Am.fate(es, Am.Out.end(Am.Out.first(Am.Out.up(Am.route(r <> rs)))))) : List<&2, Nat> & Am.Fate}
              ir.first(es, Am.route(r <> rs))
        case Am.Says{y}:
          match y:
            case True{}:
              {==}
            case False{}:
              {==}
        case Am.Phone{}:
          {==}
        case Am.PhoneLeft{}:
          {==}
