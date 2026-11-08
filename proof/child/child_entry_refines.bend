# eukhe: the proof of LAW child_entry_refines
#
# PROOF: field by field, each of the entry's decoders answers what the
# spec's decoder of that field answers (a tag through FCh.tag.of against
# the grammar's tag numbers, split until both sides compute); each stage
# of a request then hands the same decoded field to the next stage or
# answers the same error, and the last stage answers the spelled decision
# (lo.answer) or the left-over error.

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../../laws/child.bend as Child
import ./base.bend as LA

# Fields
# ------

def rf.mnat_some(r: Wr.Dec<Nat>) -> {FCh.get_maybe_nat.some(r) == Child.ch_spec_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.mnat_tag(t: Nat, +s: String) -> {FCh.get_maybe_nat.tag(FCh.tag.of(t), s) == Child.ch_spec_mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          rf.mnat_some(Wr.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.mnat_go(r: Wr.Dec<Nat>) -> {FCh.get_maybe_nat.go(r) == Child.ch_spec_mnat.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, +s}:
      rf.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.mnat(s: String) -> {FCh.get_maybe_nat(s) == Child.ch_spec_mnat(s) : Wr.Dec<Maybe<&2, Nat>>}:
  rf.mnat_go(Wr.get_nat(s))

def rf.w_n(t: Maybe<&2, Nat>, +l: Nat, r: Wr.Dec<Nat>) -> {FCh.get_w.n(t, l, r) == Child.ch_spec_w.n(t, l, r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.w_l(t: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {FCh.get_w.l(t, r) == Child.ch_spec_w.l(t, r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{+l, +s}:
      rf.w_n(t, l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.w_t(r: Wr.Dec<Maybe<&2, Nat>>) -> {FCh.get_w.t(r) == Child.ch_spec_w.t(r) : Wr.Dec<Ch.W>}:
  match r:
    case Wr.Got{+t, +s}:
      rf.w_l(t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.w(+s: String) -> {FCh.get_w(s) == Child.ch_spec_w(s) : Wr.Dec<Ch.W>}:
  %rf.mnat(s) : {FCh.get_w.t(FCh.get_maybe_nat(s)) == Child.ch_spec_w.t(_) : Wr.Dec<Ch.W>}
  rf.w_t(FCh.get_maybe_nat(s))

def rf.cfg_f(+st: Nat, r: Wr.Dec<Nat>) -> {FCh.get_cfg.f(st, r) == Child.ch_spec_cfg.f(st, r) : Wr.Dec<Ch.Cfg>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.cfg_s(r: Wr.Dec<Nat>) -> {FCh.get_cfg.s(r) == Child.ch_spec_cfg.s(r) : Wr.Dec<Ch.Cfg>}:
  match r:
    case Wr.Got{+st, +s}:
      rf.cfg_f(st, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.cfg(s: String) -> {FCh.get_cfg(s) == Child.ch_spec_cfg(s) : Wr.Dec<Ch.Cfg>}:
  rf.cfg_s(Wr.get_nat(s))

def rf.obs_busy(r: Wr.Dec<Maybe<&2, Nat>>) -> {FCh.get_obs.busy(r) == Child.ch_spec_obs.busy(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.obs_answered(r: Wr.Dec<Bool>) -> {FCh.get_obs.answered(r) == Child.ch_spec_obs.answered(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.obs_tag(t: Nat, +s: String) -> {FCh.get_obs.tag(FCh.tag.of(t), s) == Child.ch_spec_obs.tag(t, s) : Wr.Dec<Ch.Obs>}:
  match t:
    case 0n:
      %rf.mnat(s) : {FCh.get_obs.busy(FCh.get_maybe_nat(s)) == Child.ch_spec_obs.busy(_) : Wr.Dec<Ch.Obs>}
      rf.obs_busy(FCh.get_maybe_nat(s))
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              rf.obs_answered(Wr.get_bool(s))
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.obs_go(r: Wr.Dec<Nat>) -> {FCh.get_obs.go(r) == Child.ch_spec_obs.go(r) : Wr.Dec<Ch.Obs>}:
  match r:
    case Wr.Got{t, +s}:
      rf.obs_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.obs(s: String) -> {FCh.get_obs(s) == Child.ch_spec_obs(s) : Wr.Dec<Ch.Obs>}:
  rf.obs_go(Wr.get_nat(s))

def rf.mode_tag(t: Nat, s: String) -> {FCh.get_mode.tag(FCh.tag.of(t), s) == Child.ch_spec_mode.tag(t, s) : Wr.Dec<Ch.Mode>}:
  match t:
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
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.mode_go(r: Wr.Dec<Nat>) -> {FCh.get_mode.go(r) == Child.ch_spec_mode.go(r) : Wr.Dec<Ch.Mode>}:
  match r:
    case Wr.Got{t, s}:
      rf.mode_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.mode(s: String) -> {FCh.get_mode(s) == Child.ch_spec_mode(s) : Wr.Dec<Ch.Mode>}:
  rf.mode_go(Wr.get_nat(s))

def rf.report_tag(t: Nat, s: String) -> {FCh.get_report.tag(FCh.tag.of(t), s) == Child.ch_spec_report.tag(t, s) : Wr.Dec<Ch.Report>}:
  match t:
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
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.report_go(r: Wr.Dec<Nat>) -> {FCh.get_report.go(r) == Child.ch_spec_report.go(r) : Wr.Dec<Ch.Report>}:
  match r:
    case Wr.Got{t, s}:
      rf.report_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.report(s: String) -> {FCh.get_report(s) == Child.ch_spec_report(s) : Wr.Dec<Ch.Report>}:
  rf.report_go(Wr.get_nat(s))

def rf.fate_tag(t: Nat, s: String) -> {FCh.get_fate.tag(FCh.tag.of(t), s) == Child.ch_spec_fate.tag(t, s) : Wr.Dec<Ch.Fate>}:
  match t:
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
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.fate_go(r: Wr.Dec<Nat>) -> {FCh.get_fate.go(r) == Child.ch_spec_fate.go(r) : Wr.Dec<Ch.Fate>}:
  match r:
    case Wr.Got{t, s}:
      rf.fate_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.fate(s: String) -> {FCh.get_fate(s) == Child.ch_spec_fate(s) : Wr.Dec<Ch.Fate>}:
  rf.fate_go(Wr.get_nat(s))

def rf.mfate_some(r: Wr.Dec<Ch.Fate>) -> {FCh.get_mfate.some(r) == Child.ch_spec_mfate.some(r) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.mfate_tag(t: Nat, +s: String) -> {FCh.get_mfate.tag(FCh.tag.of(t), s) == Child.ch_spec_mfate.tag(t, s) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match t:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          %rf.fate(s) : {FCh.get_mfate.some(FCh.get_fate(s)) == Child.ch_spec_mfate.some(_) : Wr.Dec<Maybe<&2, Ch.Fate>>}
          rf.mfate_some(FCh.get_fate(s))
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.mfate_go(r: Wr.Dec<Nat>) -> {FCh.get_mfate.go(r) == Child.ch_spec_mfate.go(r) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  match r:
    case Wr.Got{t, +s}:
      rf.mfate_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.mfate(s: String) -> {FCh.get_mfate(s) == Child.ch_spec_mfate(s) : Wr.Dec<Maybe<&2, Ch.Fate>>}:
  rf.mfate_go(Wr.get_nat(s))

def rf.ph_watching(r: Wr.Dec<Ch.W>) -> {FCh.get_ph.watching(r) == Child.ch_spec_ph.watching(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.ph_n(k: Ch.Report, r: Wr.Dec<Nat>) -> {FCh.get_ph.n(k, r) == Child.ch_spec_ph.n(k, r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rf.ph_owing(r: Wr.Dec<Ch.Report>) -> {FCh.get_ph.owing(r) == Child.ch_spec_ph.owing(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{+k, +s}:
      rf.ph_n(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.ph_tag(t: Nat, +s: String) -> {FCh.get_ph.tag(FCh.tag.of(t), s) == Child.ch_spec_ph.tag(t, s) : Wr.Dec<Ch.Ph>}:
  match t:
    case 0n:
      %rf.w(s) : {FCh.get_ph.watching(FCh.get_w(s)) == Child.ch_spec_ph.watching(_) : Wr.Dec<Ch.Ph>}
      rf.ph_watching(FCh.get_w(s))
    case 1n+a:
      match a:
        case 0n:
          %rf.report(s) : {FCh.get_ph.owing(FCh.get_report(s)) == Child.ch_spec_ph.owing(_) : Wr.Dec<Ch.Ph>}
          rf.ph_owing(FCh.get_report(s))
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.ph_go(r: Wr.Dec<Nat>) -> {FCh.get_ph.go(r) == Child.ch_spec_ph.go(r) : Wr.Dec<Ch.Ph>}:
  match r:
    case Wr.Got{t, +s}:
      rf.ph_tag(t, s)
    case Wr.Bad{}:
      {==}

def rf.ph(s: String) -> {FCh.get_ph(s) == Child.ch_spec_ph(s) : Wr.Dec<Ch.Ph>}:
  rf.ph_go(Wr.get_nat(s))

# Requests
# --------

def rf.fin(r: FCh.Req, left: Bool) -> {LA.lo.fin(r, left) == Child.ch_spec_fin(r, left) : String}:
  match left:
    case True{}:
      LA.lo.answer(r)
    case False{}:
      LA.lo.left(r)

def rf.vm(+c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, r: Wr.Dec<Ch.Mode>) -> {FCh.verdict.m(c, w, e, o, r) == Child.ch_spec_vm(c, w, e, o, r) : String}:
  match r:
    case Wr.Got{+m, +s}:
      rf.fin(FCh.AskVerdict{c, w, e, o, m}, Wr.end(s))
    case Wr.Bad{}:
      {==}

def rf.vo(+c: Ch.Cfg, +w: Ch.W, +e: Nat, r: Wr.Dec<Ch.Obs>) -> {FCh.verdict.o(c, w, e, r) == Child.ch_spec_vo(c, w, e, r) : String}:
  match r:
    case Wr.Got{+o, +s}:
      %rf.mode(s) : {FCh.verdict.m(c, w, e, o, FCh.get_mode(s)) == Child.ch_spec_vm(c, w, e, o, _) : String}
      rf.vm(c, w, e, o, FCh.get_mode(s))
    case Wr.Bad{}:
      {==}

def rf.ve(+c: Ch.Cfg, +w: Ch.W, r: Wr.Dec<Nat>) -> {FCh.verdict.e(c, w, r) == Child.ch_spec_ve(c, w, r) : String}:
  match r:
    case Wr.Got{+e, +s}:
      %rf.obs(s) : {FCh.verdict.o(c, w, e, FCh.get_obs(s)) == Child.ch_spec_vo(c, w, e, _) : String}
      rf.vo(c, w, e, FCh.get_obs(s))
    case Wr.Bad{}:
      {==}

def rf.vw(+c: Ch.Cfg, r: Wr.Dec<Ch.W>) -> {FCh.verdict.w(c, r) == Child.ch_spec_vw(c, r) : String}:
  match r:
    case Wr.Got{+w, +s}:
      rf.ve(c, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.vc(r: Wr.Dec<Ch.Cfg>) -> {FCh.verdict.c(r) == Child.ch_spec_vc(r) : String}:
  match r:
    case Wr.Got{+c, +s}:
      %rf.w(s) : {FCh.verdict.w(c, FCh.get_w(s)) == Child.ch_spec_vw(c, _) : String}
      rf.vw(c, FCh.get_w(s))
    case Wr.Bad{}:
      {==}

def rf.mn(+f: Maybe<&2, Ch.Fate>, r: Wr.Dec<Nat>) -> {FCh.move.n(f, r) == Child.ch_spec_mn(f, r) : String}:
  match r:
    case Wr.Got{+n, +s}:
      rf.fin(FCh.AskMove{f, n}, Wr.end(s))
    case Wr.Bad{}:
      {==}

def rf.mf(r: Wr.Dec<Maybe<&2, Ch.Fate>>) -> {FCh.move.f(r) == Child.ch_spec_mf(r) : String}:
  match r:
    case Wr.Got{+f, +s}:
      rf.mn(f, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def rf.ad(+p: Ch.Ph, r: Wr.Dec<Bool>) -> {FCh.abort.d(p, r) == Child.ch_spec_ad(p, r) : String}:
  match r:
    case Wr.Got{+d, +s}:
      rf.fin(FCh.AskAbort{p, d}, Wr.end(s))
    case Wr.Bad{}:
      {==}

def rf.ap(r: Wr.Dec<Ch.Ph>) -> {FCh.abort.ph(r) == Child.ch_spec_ap(r) : String}:
  match r:
    case Wr.Got{+p, +s}:
      rf.ad(p, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def rf.tag(t: Nat, +s: String) -> {FCh.run.tag(FCh.tag.of(t), s) == Child.ch_spec_req.tag(t, s) : String}:
  match t:
    case 0n:
      %rf.cfg(s) : {FCh.verdict.c(FCh.get_cfg(s)) == Child.ch_spec_vc(_) : String}
      rf.vc(FCh.get_cfg(s))
    case 1n+a:
      match a:
        case 0n:
          %rf.mfate(s) : {FCh.move.f(FCh.get_mfate(s)) == Child.ch_spec_mf(_) : String}
          rf.mf(FCh.get_mfate(s))
        case 1n+b:
          match b:
            case 0n:
              %rf.ph(s) : {FCh.abort.ph(FCh.get_ph(s)) == Child.ch_spec_ap(_) : String}
              rf.ap(FCh.get_ph(s))
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      {==}

def rf.run(r: Wr.Dec<Nat>) -> {FCh.run(r) == Child.ch_spec_req(r) : String}:
  match r:
    case Wr.Got{t, +s}:
      rf.tag(t, s)
    case Wr.Bad{}:
      {==}

def Child.child_entry_refines(s):
  rf.run(Wr.get_nat(s))
