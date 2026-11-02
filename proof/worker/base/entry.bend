# eukhe: lemmas the entry proofs of area worker share: the entry's own
# encoders write what the spec spellers of laws/worker.bend spell (we_*),
# its readers read every spelled value back (wr_*: the decoder of a request,
# and the reply readers), and its answer to a request is the spelled reply
# of the model (we_run).

import Base
import ../../../bend/worker.bend as Wk
import ../../../bend/ffi_worker.bend as FWk
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/worker.bend as Worker
import ../../base/wire.bend as LWire
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base.bend as LAWorker

# ---- the encoders spell the spec ----

def we_mp(m: Wk.Mode, p: Maybe<&2, Nat>, -y: String) -> {FWk.put_mode(m, FWk.put_parked(p, y)) == Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, y)) : String}:
  match m p:
    case Wk.Run{} None{}:
      {==}
    case Wk.Run{} Some{x}:
      {==}
    case Wk.Paused{} None{}:
      {==}
    case Wk.Paused{} Some{x}:
      {==}

# a state: mode, parked, kept, in flight
def we_st(x: Wk.St, +rest: String) -> {FWk.put_st(x, rest) == Worker.wk_spell_st(x, rest) : String}:
  match x:
    case Wk.St{+m, +p, +k, +n}:
      +y = Wr.put_nat(n, rest)
      %Wire.wire_nats_spells(k, y) : {FWk.put_mode(m, FWk.put_parked(p, FWk.put_nats(k, y))) == Worker.wk_spell_mode(m, Worker.wk_spell_parked(p, _)) : String}
      we_mp(m, p, Wr.put_list(~Nat, ~Wr.put_nat, k, y))

# a verdict
def we_verdict(v: Wk.Verdict, +rest: String) -> {FWk.put_verdict(v, rest) == Worker.wk_spell_verdict(v, rest) : String}:
  match v:
    case Wk.Go{}:
      {==}
    case Wk.Hold{}:
      {==}
    case Wk.Release{+xs}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FWk.put_nats(xs, rest), LawsBase.wire_spell_nats(xs, rest), Wire.wire_nats_spells(xs, rest))
    case Wk.Kept{}:
      {==}
    case Wk.Pass{}:
      {==}
    case Wk.Ack{}:
      {==}

# a pick: cursor, seqs, text
def we_pick(x: Wk.Pick, +rest: String) -> {FWk.put_pick(x, rest) == Worker.wk_spell_pick(x, rest) : String}:
  match x:
    case Wk.Pick{+c, +ps, +b}:
      Equal.cong(String, String, z => Wr.put_nat(c, z), FWk.put_nats(ps, Wr.put_str(b, rest)), LawsBase.wire_spell_nats(ps, Wr.put_str(b, rest)), Wire.wire_nats_spells(ps, Wr.put_str(b, rest)))

# a step's reply: the state, then the verdict
def we_stepped(r: Wk.St & Wk.Verdict) -> {FWk.ffi.stepped(r) == Worker.wk_spell_stepped(r) : String}:
  (+x, +v) = r
  Equal.trans(String, FWk.put_st(x, FWk.put_verdict(v, "")), FWk.put_st(x, Worker.wk_spell_verdict(v, "")), Worker.wk_spell_st(x, Worker.wk_spell_verdict(v, "")),
    Equal.cong(String, String, z => FWk.put_st(x, z), FWk.put_verdict(v, ""), Worker.wk_spell_verdict(v, ""), we_verdict(v, "")),
    we_st(x, Worker.wk_spell_verdict(v, "")))

# the entry's answer to a request is the spelled reply of the model
def we_run(r: FWk.Req) -> {FWk.ffi.run(r) == Worker.wk_spell_reply(r) : String}:
  match r:
    case FWk.Step{x, e}:
      we_stepped(Wk.step(x, e))
    case FWk.Forward{c, ms, n}:
      we_pick(Wk.pick(c, ms, n), "")

# ---- the readers read the spelling ----

def wr_nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def wr_str(+t: String, +rest: String, h: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}) -> {Wr.Got{t, rest} == Wr.get_str(Wr.put_str(t, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, h))

# a list of Nats that fits
def wr_nats(+k: List<&2, Nat>, +rest: String, h: {Worker.wk_nats_fit(k) == True{} : Bool}) -> {FWk.get_nats(LawsBase.wire_spell_nats(k, rest)) == Wr.Got{k, rest} : Wr.Dec<List<&2, Nat>>}:
  %Wire.wire_nats_spells(k, rest) : {FWk.get_nats(_) == Wr.Got{k, rest} : Wr.Dec<List<&2, Nat>>}
  Wire.wire_list_round_trip(k, rest, h)

def wr_mode(m: Wk.Mode, -rest: String) -> {FWk.get_mode(Worker.wk_spell_mode(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Wk.Mode>}:
  match m:
    case Wk.Run{}:
      {==}
    case Wk.Paused{}:
      {==}

def wr_parked(p: Maybe<&2, Nat>, +rest: String, h: {LawsBase.wire_mfits(p) == True{} : Bool}) -> {FWk.get_parked(Worker.wk_spell_parked(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match p:
    case None{}:
      {==}
    case Some{+x}:
      %wr_nat(x, rest, h) : {FWk.get_parked.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a state that fits
def wr_st(x: Wk.St, +rest: String, h: {Worker.wk_st_fits(x) == True{} : Bool}) -> {FWk.get_st(Worker.wk_spell_st(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.St>}:
  match x:
    case Wk.St{+m, +p, +k, +n}:
      +hh = h
      +h2 = LAWorker.wb_and_r(LawsBase.wire_mfits(p), Bool.and(Worker.wk_nats_fit(k), LawsBase.wire_fits(n)), hh)
      +s3 = Wr.put_nat(n, rest)
      +s2 = LawsBase.wire_spell_nats(k, s3)
      +s1 = Worker.wk_spell_parked(p, s2)
      %Equal.sym(Wr.Dec<Wk.Mode>, FWk.get_mode(Worker.wk_spell_mode(m, s1)), Wr.Got{m, s1}, wr_mode(m, s1)) : {FWk.get_st.mode(_) == Wr.Got{Wk.St{m, p, k, n}, rest} : Wr.Dec<Wk.St>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FWk.get_parked(s1), Wr.Got{p, s2}, wr_parked(p, s2, LAWorker.wb_and_l(LawsBase.wire_mfits(p), Bool.and(Worker.wk_nats_fit(k), LawsBase.wire_fits(n)), hh))) : {FWk.get_st.parked(m, _) == Wr.Got{Wk.St{m, p, k, n}, rest} : Wr.Dec<Wk.St>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, FWk.get_nats(s2), Wr.Got{k, s3}, wr_nats(k, s3, LAWorker.wb_and_l(Worker.wk_nats_fit(k), LawsBase.wire_fits(n), h2))) : {FWk.get_st.kept(m, p, _) == Wr.Got{Wk.St{m, p, k, n}, rest} : Wr.Dec<Wk.St>}
      %wr_nat(n, rest, LAWorker.wb_and_r(Worker.wk_nats_fit(k), LawsBase.wire_fits(n), h2)) : {FWk.get_st.n(m, p, k, _) == Wr.Got{Wk.St{m, p, k, n}, rest} : Wr.Dec<Wk.St>}
      {==}

# an event that fits
def wr_ev(e: Wk.Ev, +rest: String, h: {Worker.wk_ev_fits(e) == True{} : Bool}) -> {FWk.get_ev(Worker.wk_spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Wk.Ev>}:
  match e:
    case Wk.Pause{}:
      {==}
    case Wk.Resume{}:
      {==}
    case Wk.Gate{+g, +i}:
      +hh = h
      %wr_nat(g, Wr.put_nat(i, rest), LAWorker.wb_and_l(LawsBase.wire_fits(g), LawsBase.wire_fits(i), hh)) : {FWk.get_ev.gate(_) == Wr.Got{Wk.Gate{g, i}, rest} : Wr.Dec<Wk.Ev>}
      %wr_nat(i, rest, LAWorker.wb_and_r(LawsBase.wire_fits(g), LawsBase.wire_fits(i), hh)) : {FWk.get_ev.gate.id(g, _) == Wr.Got{Wk.Gate{g, i}, rest} : Wr.Dec<Wk.Ev>}
      {==}
    case Wk.ToolDone{}:
      {==}
    case Wk.Msg{+i, w}:
      match w:
        case True{}:
          %wr_nat(i, SCon{'T', rest}, h) : {FWk.get_ev.msg(_) == Wr.Got{Wk.Msg{i, True{}}, rest} : Wr.Dec<Wk.Ev>}
          {==}
        case False{}:
          %wr_nat(i, SCon{'F', rest}, h) : {FWk.get_ev.msg(_) == Wr.Got{Wk.Msg{i, False{}}, rest} : Wr.Dec<Wk.Ev>}
          {==}
    case Wk.End{}:
      {==}

# a message that fits
def wr_umsg(m: Wk.UMsg, +rest: String, h: {Worker.wk_umsg_fits(m) == True{} : Bool}) -> {FWk.get_umsg(Worker.wk_spell_umsg(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Wk.UMsg>}:
  match m:
    case Wk.UMsg{+q, +t}:
      +hh = h
      %wr_nat(q, Wr.put_str(t, rest), LAWorker.wb_and_l(LawsBase.wire_fits(q), LawsBase.wire_fits(String.length(t)), hh)) : {FWk.get_umsg.seq(_) == Wr.Got{Wk.UMsg{q, t}, rest} : Wr.Dec<Wk.UMsg>}
      %wr_str(t, rest, LAWorker.wb_and_r(LawsBase.wire_fits(q), LawsBase.wire_fits(String.length(t)), hh)) : {FWk.get_umsg.text(q, _) == Wr.Got{Wk.UMsg{q, t}, rest} : Wr.Dec<Wk.UMsg>}
      {==}

# the item loop reads back x then t
def wr_umsgs_go(+t: List<&2, Wk.UMsg>, +x: Wk.UMsg, +rest: String, +hf: {Worker.wk_umsgs_all(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, List.length(&2, Wk.UMsg, t), FWk.get_umsg(Worker.wk_spell_umsg(x, Worker.wk_spell_umsgs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Wk.UMsg>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Wk.UMsg>, FWk.get_umsg(Worker.wk_spell_umsg(x, rest)), Wr.Got{x, rest}, wr_umsg(x, rest, LAWorker.wb_and_l(Worker.wk_umsg_fits(x), True{}, hf))) : {Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Wk.UMsg>>}
      {==}
    case Con{+y, +u}:
      +s1 = Worker.wk_spell_umsg(y, Worker.wk_spell_umsgs.items(u, rest))
      %Equal.sym(Wr.Dec<Wk.UMsg>, FWk.get_umsg(Worker.wk_spell_umsg(x, s1)), Wr.Got{x, s1}, wr_umsg(x, s1, LAWorker.wb_and_l(Worker.wk_umsg_fits(x), Worker.wk_umsgs_all(y <> u), hf))) : {Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, 1n+List.length(&2, Wk.UMsg, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Wk.UMsg>>}
      %Equal.sym(Wr.Dec<List<&2, Wk.UMsg>>, Wr.get_list.go(~Wk.UMsg, ~FWk.get_umsg, List.length(&2, Wk.UMsg, u), FWk.get_umsg(s1)), Wr.Got{y <> u, rest}, wr_umsgs_go(u, y, rest, LAWorker.wb_and_r(Worker.wk_umsg_fits(x), Worker.wk_umsgs_all(y <> u), hf))) : {Wr.get_list.cons(Wk.UMsg, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Wk.UMsg>>}
      {==}

# messages that fit
def wr_umsgs(ms: List<&2, Wk.UMsg>, +rest: String, h: {Worker.wk_umsgs_fit(ms) == True{} : Bool}) -> {FWk.get_umsgs(Worker.wk_spell_umsgs(ms, rest)) == Wr.Got{ms, rest} : Wr.Dec<List<&2, Wk.UMsg>>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hh = h
      +l = List.length(&2, Wk.UMsg, x <> t)
      +s1 = Worker.wk_spell_umsgs.items(x <> t, rest)
      %wr_nat(l, s1, LAWorker.wb_and_l(LawsBase.wire_fits(l), Worker.wk_umsgs_all(x <> t), hh)) : {Wr.get_list.start(~Wk.UMsg, ~FWk.get_umsg, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Wk.UMsg>>}
      wr_umsgs_go(t, x, rest, LAWorker.wb_and_r(LawsBase.wire_fits(l), Worker.wk_umsgs_all(x <> t), hh))

def wr_note(n: Maybe<&2, String>, +rest: String, h: {Worker.wk_note_fits(n) == True{} : Bool}) -> {FWk.get_note(Worker.wk_spell_note(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Maybe<&2, String>>}:
  match n:
    case None{}:
      {==}
    case Some{+t}:
      %wr_str(t, rest, h) : {FWk.get_note.some(_) == Wr.Got{Some{t}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

# a request that fits
def wr_req(r: FWk.Req, +rest: String, h: {Worker.wk_req_fits(r) == True{} : Bool}) -> {FWk.get_req(Worker.wk_spell_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FWk.Req>}:
  match r:
    case FWk.Step{+x, +e}:
      +hh = h
      +s1 = Worker.wk_spell_ev(e, rest)
      %Equal.sym(Wr.Dec<Wk.St>, FWk.get_st(Worker.wk_spell_st(x, s1)), Wr.Got{x, s1}, wr_st(x, s1, LAWorker.wb_and_l(Worker.wk_st_fits(x), Worker.wk_ev_fits(e), hh))) : {FWk.get_req.st(_) == Wr.Got{FWk.Step{x, e}, rest} : Wr.Dec<FWk.Req>}
      %Equal.sym(Wr.Dec<Wk.Ev>, FWk.get_ev(s1), Wr.Got{e, rest}, wr_ev(e, rest, LAWorker.wb_and_r(Worker.wk_st_fits(x), Worker.wk_ev_fits(e), hh))) : {FWk.get_req.ev(x, _) == Wr.Got{FWk.Step{x, e}, rest} : Wr.Dec<FWk.Req>}
      {==}
    case FWk.Forward{+c, +ms, +n}:
      +hh = h
      +h2 = LAWorker.wb_and_r(LawsBase.wire_fits(c), Bool.and(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n)), hh)
      +s2 = Worker.wk_spell_note(n, rest)
      +s1 = Worker.wk_spell_umsgs(ms, s2)
      %wr_nat(c, s1, LAWorker.wb_and_l(LawsBase.wire_fits(c), Bool.and(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n)), hh)) : {FWk.get_req.cursor(_) == Wr.Got{FWk.Forward{c, ms, n}, rest} : Wr.Dec<FWk.Req>}
      %Equal.sym(Wr.Dec<List<&2, Wk.UMsg>>, FWk.get_umsgs(s1), Wr.Got{ms, s2}, wr_umsgs(ms, s2, LAWorker.wb_and_l(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n), h2))) : {FWk.get_req.msgs(c, _) == Wr.Got{FWk.Forward{c, ms, n}, rest} : Wr.Dec<FWk.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FWk.get_note(s2), Wr.Got{n, rest}, wr_note(n, rest, LAWorker.wb_and_r(Worker.wk_umsgs_fit(ms), Worker.wk_note_fits(n), h2))) : {FWk.get_req.note(c, ms, _) == Wr.Got{FWk.Forward{c, ms, n}, rest} : Wr.Dec<FWk.Req>}
      {==}

# a verdict that fits
def wr_verdict(v: Wk.Verdict, +rest: String, h: {Worker.wk_verdict_fits(v) == True{} : Bool}) -> {FWk.get_verdict(Worker.wk_spell_verdict(v, rest)) == Wr.Got{v, rest} : Wr.Dec<Wk.Verdict>}:
  match v:
    case Wk.Go{}:
      {==}
    case Wk.Hold{}:
      {==}
    case Wk.Release{+xs}:
      %Equal.sym(Wr.Dec<List<&2, Nat>>, FWk.get_nats(LawsBase.wire_spell_nats(xs, rest)), Wr.Got{xs, rest}, wr_nats(xs, rest, h)) : {FWk.get_verdict.release(_) == Wr.Got{Wk.Release{xs}, rest} : Wr.Dec<Wk.Verdict>}
      {==}
    case Wk.Kept{}:
      {==}
    case Wk.Pass{}:
      {==}
    case Wk.Ack{}:
      {==}

# a pick that fits
def wr_pick(x: Wk.Pick, +rest: String, h: {Worker.wk_pick_fits(x) == True{} : Bool}) -> {FWk.get_pick(Worker.wk_spell_pick(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Wk.Pick>}:
  match x:
    case Wk.Pick{+c, +ps, +b}:
      +hh = h
      +h2 = LAWorker.wb_and_r(LawsBase.wire_fits(c), Bool.and(Worker.wk_nats_fit(ps), LawsBase.wire_fits(String.length(b))), hh)
      +s2 = Wr.put_str(b, rest)
      +s1 = LawsBase.wire_spell_nats(ps, s2)
      %wr_nat(c, s1, LAWorker.wb_and_l(LawsBase.wire_fits(c), Bool.and(Worker.wk_nats_fit(ps), LawsBase.wire_fits(String.length(b))), hh)) : {FWk.get_pick.cursor(_) == Wr.Got{Wk.Pick{c, ps, b}, rest} : Wr.Dec<Wk.Pick>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, FWk.get_nats(s1), Wr.Got{ps, s2}, wr_nats(ps, s2, LAWorker.wb_and_l(Worker.wk_nats_fit(ps), LawsBase.wire_fits(String.length(b)), h2))) : {FWk.get_pick.picked(c, _) == Wr.Got{Wk.Pick{c, ps, b}, rest} : Wr.Dec<Wk.Pick>}
      %wr_str(b, rest, LAWorker.wb_and_r(Worker.wk_nats_fit(ps), LawsBase.wire_fits(String.length(b)), h2)) : {FWk.get_pick.body(c, ps, _) == Wr.Got{Wk.Pick{c, ps, b}, rest} : Wr.Dec<Wk.Pick>}
      {==}

# the entry on a spelled request that fits, then rest: the request is read
# whole, then the rest decides
def we_spelled(+r: FWk.Req, +rest: String, h: {Worker.wk_req_fits(r) == True{} : Bool}) -> {FWk.ffi(Worker.wk_spell_req(r, rest)) == FWk.ffi.whole(r, Wr.end(rest)) : String}:
  Equal.cong(Wr.Dec<FWk.Req>, String, d => FWk.ffi.go(d), FWk.get_req(Worker.wk_spell_req(r, rest)), Wr.Got{r, rest}, wr_req(r, rest, h))
