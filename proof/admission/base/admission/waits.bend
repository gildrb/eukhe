# eukhe: lemmas the proofs of area admission share: admission/waits

import Base
import ../../../../bend/admission.bend as Ad
import ./le.bend as LAAdmissionLe
import ./misc.bend as LAAdmissionMisc
import ./pot.bend as LAAdmissionPot
import ../bool.bend as LABool

def aw.wait_pre1(t: Ad.Tk) -> {Ad.waits.ia(Some{Ad.Tk.preempt(t)}) == Ad.waits.ia(Some{t}) : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Granted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Held{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Preempted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Ended{}}:
      {==}

def aw.wait_pre(t: List<&2, Ad.Tk>, w: Nat) -> {Ad.waits.ia(Ad.get(Ad.preempt(t), w)) == Ad.waits.ia(Ad.get(t, w)) : Bool}:
  match t w:
    case Nil{} _:
      {==}
    case +h <> +r 0n:
      aw.wait_pre1(h)
    case +h <> +r 1n+p:
      aw.wait_pre(r, p)

# a grant never makes a ticket wait
def aw.wait_mark(t: List<&2, Ad.Tk>, +c: Ad.Cls, +w: Nat, e: {Ad.waits.ia(Ad.get(Ad.mark(c, t), w)) == True{} : Bool}) -> {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+hc, +hs} <> +r:
      match hc hs:
        case Ad.Ia{} Ad.Queued{}:
          match c w:
            case Ad.Ia{} 0n:
              LABool.ad.absurd({Ad.waits.ia(Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}) == True{} : Bool}, e)
            case Ad.Ia{} 1n+p:
              e
            case Ad.Bg{} 0n:
              {==}
            case Ad.Bg{} 1n+p:
              aw.wait_mark(r, Ad.Bg{}, p, e)
        case Ad.Bg{} Ad.Queued{}:
          match c w:
            case Ad.Bg{} 0n:
              LABool.ad.absurd({Ad.waits.ia(Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}) == True{} : Bool}, e)
            case Ad.Bg{} 1n+p:
              e
            case Ad.Ia{} 0n:
              e
            case Ad.Ia{} 1n+p:
              aw.wait_mark(r, Ad.Ia{}, p, e)
        case _ Ad.Granted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Held{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Preempted{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)
        case _ Ad.Ended{}:
          match w:
            case 0n:
              e
            case 1n+p:
              aw.wait_mark(r, c, p, e)

def aw.wait_grant(+n: Nat, +d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +w: Nat, e: {Ad.waits.ia(Ad.get(Ad.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}:
  match n d:
    case 0n _:
      e
    case 1n+f None{}:
      e
    case 1n+f Some{+c}:
      aw.wait_mark(t, c, w, aw.wait_grant(f, Ad.pick(l, Ad.mark(c, t)), l, Ad.mark(c, t), w, e))

def aw.pot_grant(+n: Nat, +d: Maybe<&2, Ad.Cls>, +l: Ad.Lim, +t: List<&2, Ad.Tk>, +w: Nat, +e: {Ad.waits.ia(Ad.get(Ad.grant.go(n, d, l, t), w)) == True{} : Bool}) -> {Ad.pot(Ad.grant.go(n, d, l, t), w) == Ad.pot(t, w) : Nat}:
  match n d:
    case 0n _:
      {==}
    case 1n+f None{}:
      {==}
    case 1n+f Some{Ad.Ia{}}:
      +t2 = Ad.mark(Ad.Ia{}, t)
      Equal.trans(Nat, Ad.pot(Ad.grant.go(f, Ad.pick(l, t2), l, t2), w), Ad.pot(t2, w), Ad.pot(t, w), aw.pot_grant(f, Ad.pick(l, t2), l, t2, w, e), LAAdmissionPot.aw.pot_mark_ia(t, w, aw.wait_grant(f, Ad.pick(l, t2), l, t2, w, e)))
    case 1n+f Some{Ad.Bg{}}:
      +t2 = Ad.mark(Ad.Bg{}, t)
      Equal.trans(Nat, Ad.pot(Ad.grant.go(f, Ad.pick(l, t2), l, t2), w), Ad.pot(t2, w), Ad.pot(t, w), aw.pot_grant(f, Ad.pick(l, t2), l, t2, w, e), LAAdmissionPot.aw.pot_mark_bg(t, w))

# a new interactive request waits behind w
def aw.st_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +w: Nat, +ws: {Ad.waits.ia(Ad.get(ts, w)) == True{} : Bool}) -> {Ad.le(Ad.pot(Ad.admit.ia(l, q, ts), w), Ad.pot(ts, w)) == True{} : Bool}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))
  +x = {Ad.Tk{Ad.Ia{}, st} : Ad.Tk}
  +t1 = Ad.preempt(ts)
  +p = Ad.pot(ts, w)
  +ws1 = Equal.trans(Bool, Ad.waits.ia(Ad.get(t1, w)), Ad.waits.ia(Ad.get(ts, w)), True{}, aw.wait_pre(ts, w), ws)
  %Equal.sym(Nat, Ad.pot(List.append(&2, Ad.Tk, t1, [x]), w), Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), Ad.pot(t1, w)), LAAdmissionPot.aw.pot_app(t1, x, w, ws1)) : {Ad.le(_, p) == True{} : Bool}
  %Equal.sym(Nat, Ad.pot(t1, w), p, LAAdmissionPot.aw.pot_pre(ts, w)) : {Ad.le(Ad.bit(Ad.hit(Ad.Holding{}, Ad.Ia{}, x), _), p) == True{} : Bool}
  %Equal.sym(Bool, Ad.isz(wi), False{}, LAAdmissionMisc.aw.wait_cnt(ts, w, ws)) : {Ad.le(Ad.bit(Bool.and(Ad.Mode.of(Ad.Holding{}, Ad.admit.ia.st(Bool.and(_, Ad.room(l, hi)), Ad.le(q, wi))), True{}), p), p) == True{} : Bool}
  LAAdmissionLe.aw.ia_new(Ad.room(l, hi), Ad.le(q, wi), p)

def aw.rel(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, wf: {Ad.waits.ia(Ad.get(Ad.St.ts(Ad.release.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees.at(mb, True{}), Ad.pot(Ad.St.ts(Ad.release.at(mb, l, q, ts, k)), w)), Ad.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}, True{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}:
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Ended{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}, True{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}:
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Ended{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))

def aw.lea(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +w: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, wf: {Ad.waits.ia(Ad.get(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k)), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees.at(mb, False{}), Ad.pot(Ad.St.ts(Ad.leave.at(mb, l, q, ts, k)), w)), Ad.pot(ts, w)) == True{} : Bool}:
  match mb:
    case None{}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Queued{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Ia{}, Ad.Granted{}}}, ej)
    case Some{Ad.Tk{Ad.Ia{}, Ad.Held{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Preempted{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Ia{}, Ad.Ended{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Queued{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Nat, Ad.pot(Ad.grant(l, t2), w), Ad.pot(t2, w), aw.pot_grant(Ad.waits(t2), Ad.pick(l, t2), l, t2, w, wf)) : {Ad.le(Nat.add(Ad.frees.at(Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}, False{}), _), Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionPot.aw.end_at(ts, k, w, Some{Ad.Tk{Ad.Bg{}, Ad.Granted{}}}, ej)
    case Some{Ad.Tk{Ad.Bg{}, Ad.Held{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Preempted{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
    case Some{Ad.Tk{Ad.Bg{}, Ad.Ended{}}}:
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))

def aw.step(s: Ad.St, o: Ad.Op, +w: Nat, +ws: {Ad.waits.ia(Ad.status(s, w)) == True{} : Bool}, wf: {Ad.waits.ia(Ad.status(Ad.step(s, o), w)) == True{} : Bool}) -> {Ad.le(Nat.add(Ad.frees(s, o), Ad.ahead(Ad.step(s, o), w)), Ad.ahead(s, w)) == True{} : Bool}:
  match s o:
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Ia{}}:
      aw.st_ia(l, q, ts, w, ws)
    case Ad.St{+l, +q, +ts} Ad.Admit{Ad.Bg{}}:
      LAAdmissionPot.aw.st_bg(l, ts, w, ws)
    case Ad.St{+l, +q, +ts} Ad.Collect{+k}:
      LAAdmissionPot.aw.col(Ad.get(ts, k), l, q, ts, k, w, {==})
    case Ad.St{+l, +q, +ts} Ad.Release{+k}:
      aw.rel(Ad.get(ts, k), l, q, ts, k, w, {==}, wf)
    case Ad.St{+l, +q, +ts} Ad.Leave{+k}:
      aw.lea(Ad.get(ts, k), l, q, ts, k, w, {==}, wf)
    case Ad.St{+l, +q, +ts} Ad.Limit{+l2, q2}:
      %Equal.sym(Nat, Ad.pot(Ad.grant(l2, ts), w), Ad.pot(ts, w), aw.pot_grant(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, w, wf)) : {Ad.le(_, Ad.pot(ts, w)) == True{} : Bool}
      LAAdmissionLe.ad.le_refl(Ad.pot(ts, w))
