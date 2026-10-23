# eukhe: the proof of LAW child_entry_verdict

import Base
import ../../bend/child.bend as Ch
import ../../bend/wire.bend as Wr
import ../../bend/ffi_child.bend as FCh
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pw6.cfg(c: Ch.Cfg, +rest: String, +h: {Laws.wire_cfg_fits(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FCh.get_cfg(FCh.put_cfg(c, rest)) : Wr.Dec<Ch.Cfg>}:
  match c:
    case Ch.Cfg{+s, +f}:
      %L.pw6.nat(s, Wr.put_nat(f, rest), L.wr_and_l(Laws.wire_fits(s), Laws.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == FCh.get_cfg.s(_) : Wr.Dec<Ch.Cfg>}
      %L.pw6.nat(f, rest, L.wr_and_r(Laws.wire_fits(s), Laws.wire_fits(f), h)) : {Wr.Got{Ch.Cfg{s, f}, rest} == FCh.get_cfg.f(s, _) : Wr.Dec<Ch.Cfg>}
      {==}

def pw6.obs(o: Ch.Obs, +rest: String, +h: {Laws.wire_obs_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FCh.get_obs(FCh.put_obs(o, rest)) : Wr.Dec<Ch.Obs>}:
  match o:
    case Ch.Busy{+t}:
      %L.pw6.nat(0n, FCh.put_maybe_nat(t, rest), {==}) : {Wr.Got{Ch.Busy{t}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %LA.pw6.mnat(t, rest, h) : {Wr.Got{Ch.Busy{t}, rest} == FCh.get_obs.busy(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Lost{}:
      %L.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Lost{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Answered{+r}:
      %L.pw6.nat(2n, Wr.put_bool(r, rest), {==}) : {Wr.Got{Ch.Answered{r}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      %LA.pw6.bool(r, rest) : {Wr.Got{Ch.Answered{r}, rest} == FCh.get_obs.answered(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Broke{}:
      %L.pw6.nat(3n, rest, {==}) : {Wr.Got{Ch.Broke{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}
    case Ch.Gone{}:
      %L.pw6.nat(4n, rest, {==}) : {Wr.Got{Ch.Gone{}, rest} == FCh.get_obs.go(_) : Wr.Dec<Ch.Obs>}
      {==}

def pw6.mode(m: Ch.Mode, +rest: String) -> {Wr.Got{m, rest} == FCh.get_mode(FCh.put_mode(m, rest)) : Wr.Dec<Ch.Mode>}:
  match m:
    case Ch.Inbox{}:
      %L.pw6.nat(0n, rest, {==}) : {Wr.Got{Ch.Inbox{}, rest} == FCh.get_mode.go(_) : Wr.Dec<Ch.Mode>}
      {==}
    case Ch.Silent{}:
      %L.pw6.nat(1n, rest, {==}) : {Wr.Got{Ch.Silent{}, rest} == FCh.get_mode.go(_) : Wr.Dec<Ch.Mode>}
      {==}

def Laws.child_entry_verdict(c, w, e, o, m, hc, hw, he, ho):
  +R = FCh.put_call(Ch.verdict(c, w, e, o, m), "")
  %L.pw6.nat(0n, FCh.put_cfg(c, FCh.put_w(w, Wr.put_nat(e, FCh.put_obs(o, FCh.put_mode(m, ""))))), {==}) : {FCh.run(_) == R : String}
  %pw6.cfg(c, FCh.put_w(w, Wr.put_nat(e, FCh.put_obs(o, FCh.put_mode(m, "")))), hc) : {FCh.verdict.c(_) == R : String}
  %LA.pw6.w(w, Wr.put_nat(e, FCh.put_obs(o, FCh.put_mode(m, ""))), hw) : {FCh.verdict.w(c, _) == R : String}
  %L.pw6.nat(e, FCh.put_obs(o, FCh.put_mode(m, "")), he) : {FCh.verdict.e(c, w, _) == R : String}
  %pw6.obs(o, FCh.put_mode(m, ""), ho) : {FCh.verdict.o(c, w, e, _) == R : String}
  %pw6.mode(m, "") : {FCh.verdict.m(c, w, e, o, _) == R : String}
  {==}
