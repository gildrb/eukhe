# eukhe: the proof of LAW child_entry_errors_named
#
# PROOF: every stage of the entry either hands its decoded field to the next
# stage or answers a named error; the last stage answers a reply (which
# opens with a tag's digit, never 'E': the premise is absurd) or the
# left-over error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ../../laws/base.bend as LawsBase
import ../base/logic/logic.bend as LLogicLogic

def en.call(x: Ch.Call, err: {LawsBase.wire_opens_err(FCh.put_call(x, "")) == True{} : Bool}) -> {Child.ch_named_error(FCh.put_call(x, "")) == True{} : Bool}:
  match x:
    case Ch.Watches{w}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_call(Ch.Watches{w}, "")) == True{} : Bool}, err)
    case Ch.Reports{k}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_call(Ch.Reports{k}, "")) == True{} : Bool}, err)
    case Ch.Settles{why}:
      match why:
        case None{}:
          LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_call(Ch.Settles{None{}}, "")) == True{} : Bool}, err)
        case Some{k}:
          LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_call(Ch.Settles{Some{k}}, "")) == True{} : Bool}, err)

def en.move(x: Ch.Move, err: {LawsBase.wire_opens_err(FCh.put_move(x, "")) == True{} : Bool}) -> {Child.ch_named_error(FCh.put_move(x, "")) == True{} : Bool}:
  match x:
    case Ch.Submit{n}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_move(Ch.Submit{n}, "")) == True{} : Bool}, err)
    case Ch.Await{}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_move(Ch.Await{}, "")) == True{} : Bool}, err)
    case Ch.Resubmit{n}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_move(Ch.Resubmit{n}, "")) == True{} : Bool}, err)
    case Ch.Delivered{}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_move(Ch.Delivered{}, "")) == True{} : Bool}, err)

def en.ph(x: Ch.Ph, err: {LawsBase.wire_opens_err(FCh.put_ph(x, "")) == True{} : Bool}) -> {Child.ch_named_error(FCh.put_ph(x, "")) == True{} : Bool}:
  match x:
    case Ch.Watching{w}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_ph(Ch.Watching{w}, "")) == True{} : Bool}, err)
    case Ch.Owing{k, n}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_ph(Ch.Owing{k, n}, "")) == True{} : Bool}, err)
    case Ch.Ended{}:
      LLogicLogic.child.pc.absurd({Child.ch_named_error(FCh.put_ph(Ch.Ended{}, "")) == True{} : Bool}, err)

def en.vfin(left: Bool, +c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, +m: Ch.Mode, err: {LawsBase.wire_opens_err(FCh.verdict.fin(left, c, w, e, o, m)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.fin(left, c, w, e, o, m)) == True{} : Bool}:
  match left:
    case True{}:
      en.call(Ch.verdict(c, w, e, o, m), err)
    case False{}:
      {==}

def en.mfin(left: Bool, +f: Maybe<&2, Ch.Fate>, +n: Nat, err: {LawsBase.wire_opens_err(FCh.move.fin(left, f, n)) == True{} : Bool}) -> {Child.ch_named_error(FCh.move.fin(left, f, n)) == True{} : Bool}:
  match left:
    case True{}:
      en.move(Ch.owe.next(f, n), err)
    case False{}:
      {==}

def en.afin(left: Bool, +p: Ch.Ph, +b: Bool, err: {LawsBase.wire_opens_err(FCh.abort.fin(left, p, b)) == True{} : Bool}) -> {Child.ch_named_error(FCh.abort.fin(left, p, b)) == True{} : Bool}:
  match left:
    case True{}:
      en.ph(Ch.cut.ph(p, b), err)
    case False{}:
      {==}

def en.vm(+c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, r: Wr.Dec<Ch.Mode>, err: {LawsBase.wire_opens_err(FCh.verdict.m(c, w, e, o, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.m(c, w, e, o, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+m, +s}:
      en.vfin(Wr.end(s), c, w, e, o, m, err)
    case Wr.Bad{}:
      {==}

def en.vo(+c: Ch.Cfg, +w: Ch.W, +e: Nat, r: Wr.Dec<Ch.Obs>, err: {LawsBase.wire_opens_err(FCh.verdict.o(c, w, e, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.o(c, w, e, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+o, +s}:
      en.vm(c, w, e, o, FCh.get_mode(s), err)
    case Wr.Bad{}:
      {==}

def en.ve(+c: Ch.Cfg, +w: Ch.W, r: Wr.Dec<Nat>, err: {LawsBase.wire_opens_err(FCh.verdict.e(c, w, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.e(c, w, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+e, +s}:
      en.vo(c, w, e, FCh.get_obs(s), err)
    case Wr.Bad{}:
      {==}

def en.vw(+c: Ch.Cfg, r: Wr.Dec<Ch.W>, err: {LawsBase.wire_opens_err(FCh.verdict.w(c, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.w(c, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+w, +s}:
      en.ve(c, w, Wr.get_nat(s), err)
    case Wr.Bad{}:
      {==}

def en.vc(r: Wr.Dec<Ch.Cfg>, err: {LawsBase.wire_opens_err(FCh.verdict.c(r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.verdict.c(r)) == True{} : Bool}:
  match r:
    case Wr.Got{+c, +s}:
      en.vw(c, FCh.get_w(s), err)
    case Wr.Bad{}:
      {==}

def en.mn(+f: Maybe<&2, Ch.Fate>, r: Wr.Dec<Nat>, err: {LawsBase.wire_opens_err(FCh.move.n(f, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.move.n(f, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+n, +s}:
      en.mfin(Wr.end(s), f, n, err)
    case Wr.Bad{}:
      {==}

def en.mf(r: Wr.Dec<Maybe<&2, Ch.Fate>>, err: {LawsBase.wire_opens_err(FCh.move.f(r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.move.f(r)) == True{} : Bool}:
  match r:
    case Wr.Got{+f, +s}:
      en.mn(f, Wr.get_nat(s), err)
    case Wr.Bad{}:
      {==}

def en.ad(+p: Ch.Ph, r: Wr.Dec<Bool>, err: {LawsBase.wire_opens_err(FCh.abort.d(p, r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.abort.d(p, r)) == True{} : Bool}:
  match r:
    case Wr.Got{+b, +s}:
      en.afin(Wr.end(s), p, b, err)
    case Wr.Bad{}:
      {==}

def en.ap(r: Wr.Dec<Ch.Ph>, err: {LawsBase.wire_opens_err(FCh.abort.ph(r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.abort.ph(r)) == True{} : Bool}:
  match r:
    case Wr.Got{+p, +s}:
      en.ad(p, Wr.get_bool(s), err)
    case Wr.Bad{}:
      {==}

def en.tag(t: FCh.Tag, +s: String, err: {LawsBase.wire_opens_err(FCh.run.tag(t, s)) == True{} : Bool}) -> {Child.ch_named_error(FCh.run.tag(t, s)) == True{} : Bool}:
  match t:
    case FCh.T0{}:
      en.vc(FCh.get_cfg(s), err)
    case FCh.T1{}:
      en.mf(FCh.get_mfate(s), err)
    case FCh.T2{}:
      en.ap(FCh.get_ph(s), err)
    case FCh.T3{}:
      {==}
    case FCh.T4{}:
      {==}
    case FCh.TBad{}:
      {==}

def en.run(r: Wr.Dec<Nat>, err: {LawsBase.wire_opens_err(FCh.run(r)) == True{} : Bool}) -> {Child.ch_named_error(FCh.run(r)) == True{} : Bool}:
  match r:
    case Wr.Got{+t, +s}:
      en.tag(FCh.tag.of(t), s, err)
    case Wr.Bad{}:
      {==}

def Child.child_entry_errors_named(s, err):
  en.run(Wr.get_nat(s), err)
