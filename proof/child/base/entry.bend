# eukhe: lemmas the proofs of the child entry share (laws/child.bend,
# section the child entry: spelled requests)

import Base
import ../../../bend/child.bend as Ch
import ../../../bend/ffi_child.bend as FCh
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/child.bend as Child
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../base.bend as LA

# The watch's verdict (K1)
# ------------------------

def cl.moved(tok: Maybe<&2, Nat>, t: Maybe<&2, Nat>) -> {Ch.moved(tok, t) == Child.ch_news(tok, t) : Bool}:
  match tok:
    case None{}:
      match t:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case Some{y}:
      match t:
        case None{}:
          {==}
        case Some{x}:
          {==}

def cl.spend(rest: Nat, tok: Maybe<&2, Nat>, tries: Nat) -> {Ch.spend(rest, tok, tries) == Child.ch_quiet(rest, tok, tries) : Ch.Next}:
  match rest:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cl.busy(news: Bool, cfg: Ch.Cfg, tok: Maybe<&2, Nat>, +left: Nat, tries: Nat, t: Maybe<&2, Nat>, +e: Nat) -> {Ch.busy(news, cfg, Ch.W{tok, left, tries}, t, e) == Child.ch_busy(news, cfg, t, tok, left, e) : Ch.Next}:
  match news:
    case True{}:
      match cfg:
        case Ch.Cfg{s, f}:
          {==}
    case False{}:
      match cfg:
        case Ch.Cfg{s, f}:
          cl.spend(Nat.sub(left, e), tok, f)

def cl.lost(tries: Nat, tok: Maybe<&2, Nat>, +left: Nat, +e: Nat) -> {Ch.lost(Ch.W{tok, left, tries}, e) == Child.ch_lost(tries, tok, left, e) : Ch.Next}:
  match tries:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+q:
      cl.spend(Nat.sub(left, e), tok, 1n+q)

def cl.settled(r: Bool) -> {Ch.settled(r) == Child.ch_settled(r) : Ch.Next}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def cl.look(+cfg: Ch.Cfg, w: Ch.W, +e: Nat, o: Ch.Obs) -> {Ch.look(cfg, w, e, o) == Child.ch_look_spec(cfg, w, e, o) : Ch.Next}:
  match w:
    case Ch.W{+tok, +left, +tries}:
      match o:
        case Ch.Busy{+t}:
          %cl.moved(tok, t) : {Ch.busy(Ch.moved(tok, t), cfg, Ch.W{tok, left, tries}, t, e) == Child.ch_busy(_, cfg, t, tok, left, e) : Ch.Next}
          cl.busy(Ch.moved(tok, t), cfg, tok, left, tries, t, e)
        case Ch.Lost{}:
          cl.lost(tries, tok, left, e)
        case Ch.Answered{r}:
          cl.settled(r)
        case Ch.Broke{}:
          {==}
        case Ch.Gone{}:
          {==}

# The laws' reader is the entry's decoder
# ---------------------------------------

def cr.mnat_some(r: Wr.Dec<Nat>) -> {Child.ch_read_mnat.some(r) == FCh.get_maybe_nat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.mnat_tag(t: Nat, s: String) -> {Child.ch_read_mnat.tag(t, s) == FCh.get_maybe_nat.tag(FCh.tag.of(t), s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cr.mnat_some(Wr.get_nat(s))
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.mnat(r: Wr.Dec<Nat>) -> {Child.ch_read_mnat(r) == FCh.get_maybe_nat.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      cr.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.cfg_f(+st: Nat, r: Wr.Dec<Nat>) -> {Child.ch_read_cfg.f(st, r) == FCh.get_cfg.f(st, r) : Wr.Dec<Ch.Cfg>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.cfg(r: Wr.Dec<Nat>) -> {Child.ch_read_cfg(r) == FCh.get_cfg.s(r) : Wr.Dec<Ch.Cfg>}:
  match r:
    case Wr.Got{+st, s}:
      cr.cfg_f(st, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cr.w_n(t: Maybe<&2, Nat>, +l: Nat, r: Wr.Dec<Nat>) -> {Child.ch_read_w.n(t, l, r) == FCh.get_w.n(t, l, r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.w_l(t: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Child.ch_read_w.l(t, r) == FCh.get_w.l(t, r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{+l, s}:
      cr.w_n(t, l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cr.w(r: Wr.Dec<Maybe<&2, Nat>>) -> {Child.ch_read_w(r) == FCh.get_w.t(r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{t, s}:
      cr.w_l(t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cr.w_full(+s: String) -> {Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s))) == FCh.get_w(s) : Wr.Dec<Ch.W>}:
  %cr.mnat(Wr.get_nat(s)) : {Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s))) == FCh.get_w.t(_) : Wr.Dec<Ch.W>}
  cr.w(Child.ch_read_mnat(Wr.get_nat(s)))

def cr.busy(r: Wr.Dec<Maybe<&2, Nat>>) -> {Child.ch_read_obs.busy(r) == FCh.get_obs.busy(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.answered(r: Wr.Dec<Bool>) -> {Child.ch_read_obs.answered(r) == FCh.get_obs.answered(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.obs_tag(t: Nat, +s: String) -> {Child.ch_read_obs.tag(t, s) == FCh.get_obs.tag(FCh.tag.of(t), s) : Wr.Dec<Ch.Obs>}:
  match t:
    case 0n:
      %cr.mnat(Wr.get_nat(s)) : {Child.ch_read_obs.busy(Child.ch_read_mnat(Wr.get_nat(s))) == FCh.get_obs.busy(_) : Wr.Dec<Ch.Obs>}
      cr.busy(Child.ch_read_mnat(Wr.get_nat(s)))
    case 1n:
      {==}
    case 2n:
      cr.answered(Wr.get_bool(s))
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.obs(r: Wr.Dec<Nat>) -> {Child.ch_read_obs(r) == FCh.get_obs.go(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{t, s}:
      cr.obs_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.mode_tag(t: Nat, s: String) -> {Child.ch_read_mode.tag(t, s) == FCh.get_mode.tag(FCh.tag.of(t), s) : Wr.Dec<Ch.Mode>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.mode(r: Wr.Dec<Nat>) -> {Child.ch_read_mode(r) == FCh.get_mode.go(r) : Wr.Dec<Ch.Mode>}:
  match r:
    case Wr.Got{t, s}:
      cr.mode_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.report_tag(t: Nat, s: String) -> {Child.ch_read_report.tag(t, s) == FCh.get_report.tag(FCh.tag.of(t), s) : Wr.Dec<Ch.Report>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.report(r: Wr.Dec<Nat>) -> {Child.ch_read_report(r) == FCh.get_report.go(r) : Wr.Dec<Ch.Report>}:
  match r:
    case Wr.Got{t, s}:
      cr.report_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.fate_tag(t: Nat, s: String) -> {Child.ch_read_fate.tag(t, s) == FCh.get_mfate.some(FCh.get_fate.tag(FCh.tag.of(t), s)) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.fate(r: Wr.Dec<Nat>) -> {Child.ch_read_fate(r) == FCh.get_mfate.some(FCh.get_fate.go(r)) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match r:
    case Wr.Got{t, s}:
      cr.fate_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.mfate_tag(t: Nat, s: String) -> {Child.ch_read_mfate.tag(t, s) == FCh.get_mfate.tag(FCh.tag.of(t), s) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cr.fate(Wr.get_nat(s))
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.mfate(r: Wr.Dec<Nat>) -> {Child.ch_read_mfate(r) == FCh.get_mfate.go(r) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match r:
    case Wr.Got{t, s}:
      cr.mfate_tag(t, s)
    case Wr.Bad{}:
      {==}

def cr.watching(r: Wr.Dec<Ch.W>) -> {Child.ch_read_ph.watching(r) == FCh.get_ph.watching(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.ph_n(k: Ch.Report, r: Wr.Dec<Nat>) -> {Child.ch_read_ph.n(k, r) == FCh.get_ph.n(k, r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cr.owing(r: Wr.Dec<Ch.Report>) -> {Child.ch_read_ph.owing(r) == FCh.get_ph.owing(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{k, s}:
      cr.ph_n(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cr.ph_tag(t: Nat, +s: String) -> {Child.ch_read_ph.tag(t, s) == FCh.get_ph.tag(FCh.tag.of(t), s) : Wr.Dec<Ch.Ph>}:
  match t:
    case 0n:
      %cr.w_full(s) : {Child.ch_read_ph.watching(Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s)))) == FCh.get_ph.watching(_) : Wr.Dec<Ch.Ph>}
      cr.watching(Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s))))
    case 1n:
      %cr.report(Wr.get_nat(s)) : {Child.ch_read_ph.owing(Child.ch_read_report(Wr.get_nat(s))) == FCh.get_ph.owing(_) : Wr.Dec<Ch.Ph>}
      cr.owing(Child.ch_read_report(Wr.get_nat(s)))
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def cr.ph(r: Wr.Dec<Nat>) -> {Child.ch_read_ph(r) == FCh.get_ph.go(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{t, s}:
      cr.ph_tag(t, s)
    case Wr.Bad{}:
      {==}

# The entry's replies are the laws' spellings
# -------------------------------------------

def cc.mnat(t: Maybe<&2, Nat>, rest: String) -> {FCh.put_maybe_nat(t, rest) == Child.ch_spell_mnat(t, rest) : String}:
  match t:
    case None{}:
      {==}
    case Some{x}:
      {==}

def cc.w(w: Ch.W, rest: String) -> {FCh.put_w(w, rest) == Child.ch_spell_w(w, rest) : String}:
  match w:
    case Ch.W{t, l, n}:
      cc.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)))

def cc.report(k: Ch.Report, rest: String) -> {FCh.put_report(k, rest) == Child.ch_spell_report(k, rest) : String}:
  match k:
    case Ch.Completed{}:
      {==}
    case Ch.Failed{}:
      {==}
    case Ch.Cancelled{}:
      {==}
    case Ch.Stalled{}:
      {==}
    case Ch.Unreachable{}:
      {==}

def cc.call(x: Ch.Next, m: Ch.Mode) -> {FCh.put_call(Ch.call.of(x, m), "") == Child.ch_spell_call(Child.ChildActed(x, m)) : String}:
  match x:
    case Ch.Watch{+w}:
      %cc.w(w, "") : {Wr.put_nat(0n, FCh.put_w(w, "")) == Wr.put_nat(0n, _) : String}
      {==}
    case Ch.Owe{+k}:
      match m:
        case Ch.Inbox{}:
          %cc.report(k, "") : {Wr.put_nat(1n, FCh.put_report(k, "")) == Wr.put_nat(1n, _) : String}
          {==}
        case Ch.Silent{}:
          %cc.report(k, "") : {Wr.put_nat(2n, Wr.put_nat(1n, FCh.put_report(k, ""))) == Wr.put_nat(2n, Wr.put_nat(1n, _)) : String}
          {==}
    case Ch.Quiet{}:
      {==}

def cc.move(f: Maybe<&2, Ch.Fate>, +n: Nat) -> {FCh.put_move(Ch.owe.next(f, n), "") == Child.ch_spell_move(Child.ChildMove(f, n)) : String}:
  match f:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          {==}
        case Ch.Placed{}:
          {==}

def cc.ph(p: Ch.Ph, d: Bool) -> {FCh.put_ph(Ch.cut.ph(p, d), "") == Child.ch_spell_ph(Child.ChildAbort(p, d), "") : String}:
  match p:
    case Ch.Watching{w}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ch.Owing{+k, +n}:
      %cc.report(k, Wr.put_nat(n, "")) : {Wr.put_nat(1n, FCh.put_report(k, Wr.put_nat(n, ""))) == Wr.put_nat(1n, _) : String}
      {==}
    case Ch.Ended{}:
      {==}

# The entry answers as the laws' reply, part by part
# --------------------------------------------------

def cv.fin(whole: Bool, +c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, +m: Ch.Mode) -> {FCh.verdict.fin(whole, c, w, e, o, m) == Child.ch_spec.verdict.fin(whole, c, w, e, o, m) : String}:
  match whole:
    case True{}:
      %cl.look(c, w, e, o) : {FCh.put_call(Ch.call.of(Ch.look(c, w, e, o), m), "") == Child.ch_spell_call(Child.ChildActed(_, m)) : String}
      cc.call(Ch.look(c, w, e, o), m)
    case False{}:
      {==}

def cv.m(+c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, r: Wr.Dec<Ch.Mode>) -> {FCh.verdict.m(c, w, e, o, r) == Child.ch_spec.verdict.m(c, w, e, o, r) : String}:
  match r:
    case Wr.Got{m, s}:
      cv.fin(Wr.end(s), c, w, e, o, m)
    case Wr.Bad{}:
      {==}

def cv.o(+c: Ch.Cfg, +w: Ch.W, +e: Nat, r: Wr.Dec<Ch.Obs>) -> {FCh.verdict.o(c, w, e, r) == Child.ch_spec.verdict.o(c, w, e, r) : String}:
  match r:
    case Wr.Got{+o, +s}:
      %cr.mode(Wr.get_nat(s)) : {FCh.verdict.m(c, w, e, o, _) == Child.ch_spec.verdict.m(c, w, e, o, Child.ch_read_mode(Wr.get_nat(s))) : String}
      cv.m(c, w, e, o, Child.ch_read_mode(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cv.e(+c: Ch.Cfg, +w: Ch.W, r: Wr.Dec<Nat>) -> {FCh.verdict.e(c, w, r) == Child.ch_spec.verdict.e(c, w, r) : String}:
  match r:
    case Wr.Got{+e, +s}:
      %cr.obs(Wr.get_nat(s)) : {FCh.verdict.o(c, w, e, _) == Child.ch_spec.verdict.o(c, w, e, Child.ch_read_obs(Wr.get_nat(s))) : String}
      cv.o(c, w, e, Child.ch_read_obs(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cv.w(+c: Ch.Cfg, r: Wr.Dec<Ch.W>) -> {FCh.verdict.w(c, r) == Child.ch_spec.verdict.w(c, r) : String}:
  match r:
    case Wr.Got{+w, s}:
      cv.e(c, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cv.c(r: Wr.Dec<Ch.Cfg>) -> {FCh.verdict.c(r) == Child.ch_spec.verdict.c(r) : String}:
  match r:
    case Wr.Got{+c, +s}:
      %cr.w_full(s) : {FCh.verdict.w(c, _) == Child.ch_spec.verdict.w(c, Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s)))) : String}
      cv.w(c, Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(s))))
    case Wr.Bad{}:
      {==}

def cm.fin(whole: Bool, +f: Maybe<&2, Ch.Fate>, +n: Nat) -> {FCh.move.fin(whole, f, n) == Child.ch_spec.move.fin(whole, f, n) : String}:
  match whole:
    case True{}:
      cc.move(f, n)
    case False{}:
      {==}

def cm.n(+f: Maybe<&2, Ch.Fate>, r: Wr.Dec<Nat>) -> {FCh.move.n(f, r) == Child.ch_spec.move.n(f, r) : String}:
  match r:
    case Wr.Got{+n, s}:
      cm.fin(Wr.end(s), f, n)
    case Wr.Bad{}:
      {==}

def cm.f(r: Wr.Dec<Maybe<&2, Ch.Fate>>) -> {FCh.move.f(r) == Child.ch_spec.move.f(r) : String}:
  match r:
    case Wr.Got{+f, s}:
      cm.n(f, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ca.fin(whole: Bool, +p: Ch.Ph, +d: Bool) -> {FCh.abort.fin(whole, p, d) == Child.ch_spec.abort.fin(whole, p, d) : String}:
  match whole:
    case True{}:
      cc.ph(p, d)
    case False{}:
      {==}

def ca.d(+p: Ch.Ph, r: Wr.Dec<Bool>) -> {FCh.abort.d(p, r) == Child.ch_spec.abort.d(p, r) : String}:
  match r:
    case Wr.Got{+d, s}:
      ca.fin(Wr.end(s), p, d)
    case Wr.Bad{}:
      {==}

def ca.p(r: Wr.Dec<Ch.Ph>) -> {FCh.abort.ph(r) == Child.ch_spec.abort.p(r) : String}:
  match r:
    case Wr.Got{+p, s}:
      ca.d(p, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ct.tag(t: Nat, +s: String) -> {FCh.run.tag(FCh.tag.of(t), s) == Child.ch_spec.tag(t, s) : String}:
  match t:
    case 0n:
      %cr.cfg(Wr.get_nat(s)) : {FCh.verdict.c(_) == Child.ch_spec.verdict.c(Child.ch_read_cfg(Wr.get_nat(s))) : String}
      cv.c(Child.ch_read_cfg(Wr.get_nat(s)))
    case 1n:
      %cr.mfate(Wr.get_nat(s)) : {FCh.move.f(_) == Child.ch_spec.move.f(Child.ch_read_mfate(Wr.get_nat(s))) : String}
      cm.f(Child.ch_read_mfate(Wr.get_nat(s)))
    case 2n:
      %cr.ph(Wr.get_nat(s)) : {FCh.abort.ph(_) == Child.ch_spec.abort.p(Child.ch_read_ph(Wr.get_nat(s))) : String}
      ca.p(Child.ch_read_ph(Wr.get_nat(s)))
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n+q:
      {==}

def ct.go(r: Wr.Dec<Nat>) -> {FCh.run(r) == Child.ch_spec.go(r) : String}:
  match r:
    case Wr.Got{t, s}:
      ct.tag(t, s)
    case Wr.Bad{}:
      {==}

def ct.exact(+s: String) -> {FCh.ffi(s) == Child.ch_spec(s) : String}:
  ct.go(Wr.get_nat(s))

# The laws' reader reads back what the laws spell
# -----------------------------------------------

def rt.mnat(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == Child.ch_read_mnat(Wr.get_nat(Child.ch_spell_mnat(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == Child.ch_read_mnat(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == Child.ch_read_mnat(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == Child.ch_read_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def rt.cfg(c: Ch.Cfg, +rest: String, +h: {Child.wire_cfg_fits(c) == True{} : Bool}) -> {Wr.Got{c, rest} == Child.ch_read_cfg(Wr.get_nat(Child.ch_spell_cfg(c, rest))) : Wr.Dec<Ch.Cfg>}:
  match c:
    case Ch.Cfg{+s, +f}:
      %LWire.pw6.nat(s, Wr.put_nat(f, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == Child.ch_read_cfg(_) : Wr.Dec<Ch.Cfg>}
      %LWire.pw6.nat(f, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == Child.ch_read_cfg.f(s, _) : Wr.Dec<Ch.Cfg>}
      {==}

def rt.w(w: Ch.W, +rest: String, +h: {Child.wire_w_fits(w) == True{} : Bool}) -> {Wr.Got{w, rest} == Child.ch_read_w(Child.ch_read_mnat(Wr.get_nat(Child.ch_spell_w(w, rest)))) : Wr.Dec<Ch.W>}:
  match w:
    case Ch.W{+t, +l, +n}:
      +ln = LLogicBool.wr_and_r(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)
      %rt.mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)), LLogicBool.wr_and_l(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)), h)) : {Wr.Got{Ch.W{t, l, n}, rest} == Child.ch_read_w(_) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(l, Wr.put_nat(n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == Child.ch_read_w.l(t, _) : Wr.Dec<Ch.W>}
      %LWire.pw6.nat(n, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(l), LawsBase.wire_fits(n), ln)) : {Wr.Got{Ch.W{t, l, n}, rest} == Child.ch_read_w.n(t, l, _) : Wr.Dec<Ch.W>}
      {==}

def rt.obs(o: Ch.Obs, +rest: String, +h: {Child.wire_obs_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == Child.ch_read_obs(Wr.get_nat(Child.ch_spell_obs(o, rest))) : Wr.Dec<Ch.Obs>}:
  match o:
    case Ch.Busy{+t}:
      %LWire.pw6.nat(0n, Child.ch_spell_mnat(t, rest), {==}) : {Wr.Got{Ch.Busy{t}, rest} == Child.ch_read_obs(_) : Wr.Dec<Ch.Obs>}
      %rt.mnat(t, rest, h) : {Wr.Got{Ch.Busy{t}, rest} == Child.ch_read_obs.busy(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Lost{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Lost{}, rest} == Child.ch_read_obs(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Answered{+r}:
      %LWire.pw6.nat(2n, Wr.put_bool(r, rest), {==}) : {Wr.Got{Ch.Answered{r}, rest} == Child.ch_read_obs(_) : Wr.Dec<Ch.Obs>}
      %LA.pw6.bool(r, rest) : {Wr.Got{Ch.Answered{r}, rest} == Child.ch_read_obs.answered(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Broke{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Broke{}, rest} == Child.ch_read_obs(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Gone{}:
      %LWire.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Gone{}, rest} == Child.ch_read_obs(_) : Wr.Dec<Ch.Obs>}
      {==}

def rt.mode(m: Ch.Mode, +rest: String) -> {Wr.Got{m, rest} == Child.ch_read_mode(Wr.get_nat(Child.ch_spell_mode(m, rest))) : Wr.Dec<Ch.Mode>}:
  match m:
    case Ch.Inbox{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Inbox{}, rest} == Child.ch_read_mode(_) : Wr.Dec<Ch.Mode>}
      {==}
    case Ch.Silent{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Silent{}, rest} == Child.ch_read_mode(_) : Wr.Dec<Ch.Mode>}
      {==}

def rt.report(k: Ch.Report, +rest: String) -> {Wr.Got{k, rest} == Child.ch_read_report(Wr.get_nat(Child.ch_spell_report(k, rest))) : Wr.Dec<Ch.Report>}:
  match k:
    case Ch.Completed{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Completed{}, rest} == Child.ch_read_report(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Failed{}:
      %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Failed{}, rest} == Child.ch_read_report(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Cancelled{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Cancelled{}, rest} == Child.ch_read_report(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Stalled{}:
      %LWire.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Stalled{}, rest} == Child.ch_read_report(_) : Wr.Dec<Ch.Report>}
      {==}
    case Ch.Unreachable{}:
      %LWire.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Unreachable{}, rest} == Child.ch_read_report(_) : Wr.Dec<Ch.Report>}
      {==}

def rt.mfate(f: Maybe<&2, Ch.Fate>, +rest: String) -> {Wr.Got{f, rest} == Child.ch_read_mfate(Wr.get_nat(Child.ch_spell_mfate(f, rest))) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match f:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == Child.ch_read_mfate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
      {==}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          %LWire.pw6.nat(1n, Wr.put_nat(0n, rest), {==}) : {Wr.Got{Some{Ch.Queued{}}, rest} == Child.ch_read_mfate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Some{Ch.Queued{}}, rest} == Child.ch_read_fate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          {==}
        case Ch.Withdrawn{}:
          %LWire.pw6.nat(1n, Wr.put_nat(1n, rest), {==}) : {Wr.Got{Some{Ch.Withdrawn{}}, rest} == Child.ch_read_mfate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Some{Ch.Withdrawn{}}, rest} == Child.ch_read_fate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          {==}
        case Ch.Placed{}:
          %LWire.pw6.nat(1n, Wr.put_nat(2n, rest), {==}) : {Wr.Got{Some{Ch.Placed{}}, rest} == Child.ch_read_mfate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Some{Ch.Placed{}}, rest} == Child.ch_read_fate(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          {==}

def rt.ph(p: Ch.Ph, +rest: String, +h: {Child.wire_ph_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == Child.ch_read_ph(Wr.get_nat(Child.ch_spell_ph(p, rest))) : Wr.Dec<Ch.Ph>}:
  match p:
    case Ch.Watching{+w}:
      %LWire.pw6.nat(0n, Child.ch_spell_w(w, rest), {==}) : {Wr.Got{Ch.Watching{w}, rest} == Child.ch_read_ph(_) : Wr.Dec<Ch.Ph>}
      %rt.w(w, rest, h) : {Wr.Got{Ch.Watching{w}, rest} == Child.ch_read_ph.watching(_) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Owing{+k, +n}:
      %LWire.pw6.nat(1n, Child.ch_spell_report(k, Wr.put_nat(n, rest)), {==}) : {Wr.Got{Ch.Owing{k, n}, rest} == Child.ch_read_ph(_) : Wr.Dec<Ch.Ph>}
      %rt.report(k, Wr.put_nat(n, rest)) : {Wr.Got{Ch.Owing{k, n}, rest} == Child.ch_read_ph.owing(_) : Wr.Dec<Ch.Ph>}
      %LWire.pw6.nat(n, rest, h) : {Wr.Got{Ch.Owing{k, n}, rest} == Child.ch_read_ph.n(k, _) : Wr.Dec<Ch.Ph>}
      {==}
    case Ch.Ended{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Ch.Ended{}, rest} == Child.ch_read_ph(_) : Wr.Dec<Ch.Ph>}
      {==}

# a request the laws spell is answered as the laws decide
def rt.answers(q: FCh.Req, +fits: {Child.ch_req_fits(q) == True{} : Bool}) -> {Child.ch_spec(Child.ch_spell_req(q, "")) == Child.ch_answer(q) : String}:
  match q:
    case FCh.AskVerdict{+c, +w, +e, +o, +m}:
      +A = Child.ch_answer(FCh.AskVerdict{c, w, e, o, m})
      +h1 = LLogicBool.wr_and_r(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o))), fits)
      +h2 = LLogicBool.wr_and_r(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)), h1)
      +hc = LLogicBool.wr_and_l(Child.wire_cfg_fits(c), Bool.and(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o))), fits)
      +hw = LLogicBool.wr_and_l(Child.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), Child.wire_obs_fits(o)), h1)
      +he = LLogicBool.wr_and_l(LawsBase.wire_fits(e), Child.wire_obs_fits(o), h2)
      +ho = LLogicBool.wr_and_r(LawsBase.wire_fits(e), Child.wire_obs_fits(o), h2)
      +U = Child.ch_spell_mode(m, "")
      +V = Child.ch_spell_obs(o, U)
      +Z = Wr.put_nat(e, V)
      +Y = Child.ch_spell_w(w, Z)
      %LWire.pw6.nat(0n, Child.ch_spell_cfg(c, Y), {==}) : {Child.ch_spec.go(_) == A : String}
      %rt.cfg(c, Y, hc) : {Child.ch_spec.verdict.c(_) == A : String}
      %rt.w(w, Z, hw) : {Child.ch_spec.verdict.w(c, _) == A : String}
      %LWire.pw6.nat(e, V, he) : {Child.ch_spec.verdict.e(c, w, _) == A : String}
      %rt.obs(o, U, ho) : {Child.ch_spec.verdict.o(c, w, e, _) == A : String}
      %rt.mode(m, "") : {Child.ch_spec.verdict.m(c, w, e, o, _) == A : String}
      {==}
    case FCh.AskMove{+f, +n}:
      +A = Child.ch_answer(FCh.AskMove{f, n})
      %LWire.pw6.nat(1n, Child.ch_spell_mfate(f, Wr.put_nat(n, "")), {==}) : {Child.ch_spec.go(_) == A : String}
      %rt.mfate(f, Wr.put_nat(n, "")) : {Child.ch_spec.move.f(_) == A : String}
      %LWire.pw6.nat(n, "", fits) : {Child.ch_spec.move.n(f, _) == A : String}
      {==}
    case FCh.AskAbort{+p, +d}:
      +A = Child.ch_answer(FCh.AskAbort{p, d})
      %LWire.pw6.nat(2n, Child.ch_spell_ph(p, Wr.put_bool(d, "")), {==}) : {Child.ch_spec.go(_) == A : String}
      %rt.ph(p, Wr.put_bool(d, ""), fits) : {Child.ch_spec.abort.p(_) == A : String}
      %LA.pw6.bool(d, "") : {Child.ch_spec.abort.d(p, _) == A : String}
      {==}
