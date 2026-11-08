# eukhe: lemmas of the screen entry's spelled laws (laws/screen.bend
# `screen_spell_*`): the laws' spellings are the entry's encoders
# (scsp.req), a request that fits reads back with any rest after it
# (scsp.rt), and the entry's answer is the spelled reply of the model's
# decision (scsp.answer).

import Base
import ../../../bend/ffi_screen.bend as FSc
import ../../../bend/screen.bend as Sc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/screen.bend as Screen
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../../wire/base/spell.bend as LAWireSpell
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../screen_ffi_run.bend as PScreenFfiRun

# Spellings are the encoders
# --------------------------

def scsp.blk(b: Sc.Blk, -rest: String) -> {Screen.screen_spell_blk(b, rest) == FSc.put_blk(b, rest) : String}:
  match b:
    case Sc.Blk{i, s, l}:
      match s:
        case Sc.Active{}:
          {==}
        case Sc.Final{}:
          {==}
        case Sc.Comm{}:
          {==}

def scsp.blks.items(bs: List<&2, Sc.Blk>, -rest: String) -> {Screen.screen_spell_blks.items(bs, rest) == PScreenFfiRun.fs.blks.items(bs, rest) : String}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %scsp.blks.items(t, rest) : {Screen.screen_spell_blk(b, Screen.screen_spell_blks.items(t, rest)) == FSc.put_blk(b, _) : String}
      scsp.blk(b, Screen.screen_spell_blks.items(t, rest))

def scsp.blks(+bs: List<&2, Sc.Blk>, -rest: String) -> {Screen.screen_spell_blks(bs, rest) == Wr.put_list(~Sc.Blk, ~FSc.put_blk, bs, rest) : String}:
  %Equal.sym(String, Wr.put_list(~Sc.Blk, ~FSc.put_blk, bs, rest), Wr.put_nat(List.length(&2, Sc.Blk, bs), PScreenFfiRun.fs.blks.items(bs, rest)), PScreenFfiRun.fs.blks.put(bs, rest)) : {Screen.screen_spell_blks(bs, rest) == _ : String}
  %scsp.blks.items(bs, rest) : {Screen.screen_spell_blks(bs, rest) == Wr.put_nat(List.length(&2, Sc.Blk, bs), _) : String}
  {==}

def scsp.tx(t: Sc.Tx, -rest: String) -> {Screen.screen_spell_tx(t, rest) == FSc.put_tx(t, rest) : String}:
  match t:
    case Sc.Tx{+bs, n, w}:
      scsp.blks(bs, Wr.put_nat(n, Wr.put_nat(w, rest)))

def scsp.ev(e: Sc.Ev, -rest: String) -> {Screen.screen_spell_ev(e, rest) == FSc.put_ev(e, rest) : String}:
  match e:
    case Sc.Open{}:
      {==}
    case Sc.Grow{x, n}:
      {==}
    case Sc.Fin{x}:
      {==}
    case Sc.Flush{}:
      {==}
    case Sc.Resize{w}:
      {==}

def scsp.evs.items(es: List<&2, Sc.Ev>, -rest: String) -> {Screen.screen_spell_evs.items(es, rest) == PScreenFfiRun.fs.evs.items(es, rest) : String}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %scsp.evs.items(t, rest) : {Screen.screen_spell_ev(e, Screen.screen_spell_evs.items(t, rest)) == FSc.put_ev(e, _) : String}
      scsp.ev(e, Screen.screen_spell_evs.items(t, rest))

def scsp.evs(+es: List<&2, Sc.Ev>, -rest: String) -> {Screen.screen_spell_evs(es, rest) == Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, rest) : String}:
  %Equal.sym(String, Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, rest), Wr.put_nat(List.length(&2, Sc.Ev, es), PScreenFfiRun.fs.evs.items(es, rest)), PScreenFfiRun.fs.evs.put(es, rest)) : {Screen.screen_spell_evs(es, rest) == _ : String}
  %scsp.evs.items(es, rest) : {Screen.screen_spell_evs(es, rest) == Wr.put_nat(List.length(&2, Sc.Ev, es), _) : String}
  {==}

def scsp.bools.go(ks: List<&2, Bool>, -rest: String) -> {Wr.put_list.go(~Bool, ~Wr.put_bool, ks, rest) == (List.length(&2, Bool, ks), Screen.screen_spell_bools.items(ks, rest)) : Nat & String}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, t, rest), (List.length(&2, Bool, t), Screen.screen_spell_bools.items(t, rest)), scsp.bools.go(t, rest)) : {Wr.put_list.step(~Bool, ~Wr.put_bool, k, _) == (1n+List.length(&2, Bool, t), Wr.put_bool(k, Screen.screen_spell_bools.items(t, rest))) : Nat & String}
      {==}

def scsp.bools(+ks: List<&2, Bool>, -rest: String) -> {Screen.screen_spell_bools(ks, rest) == Wr.put_list(~Bool, ~Wr.put_bool, ks, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, ks, rest), (List.length(&2, Bool, ks), Screen.screen_spell_bools.items(ks, rest)), scsp.bools.go(ks, rest)) : {Screen.screen_spell_bools(ks, rest) == Wr.put_list.fin(_) : String}
  {==}

def scsp.rects.go(rs: List<&2, Sc.Rect>, -rest: String) -> {Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, rs, rest) == (List.length(&2, Sc.Rect, rs), Screen.screen_spell_rects.items(rs, rest)) : Nat & String}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case Sc.Rect{y, h}:
          %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, t, rest), (List.length(&2, Sc.Rect, t), Screen.screen_spell_rects.items(t, rest)), scsp.rects.go(t, rest)) : {Wr.put_list.step(~Sc.Rect, ~FSc.put_rect, Sc.Rect{y, h}, _) == (1n+List.length(&2, Sc.Rect, t), Screen.screen_spell_rect(Sc.Rect{y, h}, Screen.screen_spell_rects.items(t, rest))) : Nat & String}
          {==}

def scsp.rects(+rs: List<&2, Sc.Rect>, -rest: String) -> {Wr.put_list(~Sc.Rect, ~FSc.put_rect, rs, rest) == Screen.screen_spell_rects(rs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, rs, rest), (List.length(&2, Sc.Rect, rs), Screen.screen_spell_rects.items(rs, rest)), scsp.rects.go(rs, rest)) : {Wr.put_list.fin(_) == Screen.screen_spell_rects(rs, rest) : String}
  {==}

def scsp.pace(p: Sc.Pace, -rest: String) -> {FSc.put_pace(p, rest) == Screen.screen_spell_pace(p, rest) : String}:
  match p:
    case Sc.Pace{r, s}:
      {==}

# the laws' spelling of a request is the entry's encoder
def scsp.req(q: FSc.Req, rest: String) -> {Screen.screen_spell_req(q, rest) == FSc.put_req(q, rest) : String}:
  match q:
    case FSc.ReqRun{+t, +es}:
      %scsp.evs(es, rest) : {Wr.put_nat(0n, Screen.screen_spell_tx(t, Screen.screen_spell_evs(es, rest))) == Wr.put_nat(0n, FSc.put_tx(t, _)) : String}
      %scsp.tx(t, Screen.screen_spell_evs(es, rest)) : {Wr.put_nat(0n, Screen.screen_spell_tx(t, Screen.screen_spell_evs(es, rest))) == Wr.put_nat(0n, _) : String}
      {==}
    case FSc.ReqPace{min, k, p, n}:
      match p:
        case Sc.Pace{r, s}:
          {==}
    case FSc.ReqStack{+hs, +y, +rows}:
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, hs, Wr.put_nat(y, Wr.put_nat(rows, rest))), LawsBase.wire_spell_nats(hs, Wr.put_nat(y, Wr.put_nat(rows, rest))), Wire.wire_nats_spells(hs, Wr.put_nat(y, Wr.put_nat(rows, rest)))) : {Wr.put_nat(2n, LawsBase.wire_spell_nats(hs, Wr.put_nat(y, Wr.put_nat(rows, rest)))) == Wr.put_nat(2n, _) : String}
      {==}
    case FSc.ReqPaint{+ks}:
      %scsp.bools(ks, rest) : {Wr.put_nat(3n, Screen.screen_spell_bools(ks, rest)) == Wr.put_nat(3n, _) : String}
      {==}

# Round trips
# -----------

# the item loop reads back x, then t
def scsp.bools.go_rt(+t: List<&2, Bool>, x: Bool, +rest: String) -> {Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, t), Wr.get_bool(Wr.put_bool(x, Screen.screen_spell_bools.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}:
  match t:
    case Nil{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}
    case +y <> +u:
      match x:
        case True{}:
          +g = Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, u), Wr.get_bool(Wr.put_bool(y, Screen.screen_spell_bools.items(u, rest))))
          %Equal.sym(Wr.Dec<List<&2, Bool>>, g, Wr.Got{y <> u, rest}, scsp.bools.go_rt(u, y, rest)) : {Wr.get_list.cons(Bool, True{}, _) == Wr.Got{True{} <> y <> u, rest} : Wr.Dec<List<&2, Bool>>}
          {==}
        case False{}:
          +g = Wr.get_list.go(~Bool, ~Wr.get_bool, List.length(&2, Bool, u), Wr.get_bool(Wr.put_bool(y, Screen.screen_spell_bools.items(u, rest))))
          %Equal.sym(Wr.Dec<List<&2, Bool>>, g, Wr.Got{y <> u, rest}, scsp.bools.go_rt(u, y, rest)) : {Wr.get_list.cons(Bool, False{}, _) == Wr.Got{False{} <> y <> u, rest} : Wr.Dec<List<&2, Bool>>}
          {==}

# a list of check results whose count fits reads back
def scsp.bools.rt(ks: List<&2, Bool>, +rest: String, h: {LawsBase.wire_fits(List.length(&2, Bool, ks)) == True{} : Bool}) -> {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ks, rest)) == Wr.Got{ks, rest} : Wr.Dec<List<&2, Bool>>}:
  match ks:
    case Nil{}:
      {==}
    case +x <> +t:
      %scsp.bools(x <> t, rest) : {Wr.get_list(~Bool, ~Wr.get_bool, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}
      %LWire.pc.nat(1n+List.length(&2, Bool, t), Screen.screen_spell_bools.items(x <> t, rest), h) : {Wr.get_list.start(~Bool, ~Wr.get_bool, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Bool>>}
      scsp.bools.go_rt(t, x, rest)

# a request that fits reads back, and the rest after it is untouched
def scsp.rt(q: FSc.Req, +rest: String, fits: {Screen.screen_req_fits(q) == True{} : Bool}) -> {FSc.get_req(FSc.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSc.Req>}:
  match q:
    case FSc.ReqRun{+t, +es}:
      +f = fits
      +a = Screen.tx_fits(t)
      +b = Bool.and(LawsBase.wire_fits(List.length(&2, Sc.Ev, es)), Screen.evs_fit(es))
      +y = Wr.put_list(~Sc.Ev, ~FSc.put_ev, es, rest)
      %LWire.pc.nat(0n, FSc.put_tx(t, y), {==}) : {FSc.get_req.of(_) == Wr.Got{FSc.ReqRun{t, es}, rest} : Wr.Dec<FSc.Req>}
      %Equal.sym(Wr.Dec<Sc.Tx>, FSc.get_tx(FSc.put_tx(t, y)), Wr.Got{t, y}, PScreenFfiRun.fs.tx_rt(t, y, LLogicBool.pq.and_l(a, b, f))) : {FSc.get_run(_) == Wr.Got{FSc.ReqRun{t, es}, rest} : Wr.Dec<FSc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Sc.Ev>>, Wr.get_list(~Sc.Ev, ~FSc.get_ev, y), Wr.Got{es, rest}, PScreenFfiRun.fs.evs.rt(es, rest, LLogicBool.pq.and_r(a, b, f))) : {FSc.get_run.es(t, _) == Wr.Got{FSc.ReqRun{t, es}, rest} : Wr.Dec<FSc.Req>}
      {==}
    case FSc.ReqPace{+min, +k, p, +n}:
      match p:
        case Sc.Pace{+r, +s}:
          +f = fits
          +a = Bool.and(LawsBase.wire_fits(min), LawsBase.wire_fits(k))
          +b = Bool.and(Screen.screen_pace_fits(Sc.Pace{r, s}), LawsBase.wire_fits(n))
          +fa = LLogicBool.pq.and_l(a, b, f)
          +fb = LLogicBool.pq.and_r(a, b, f)
          +c = Bool.and(LawsBase.wire_fits(r), LawsBase.wire_fits(s))
          +fc = LLogicBool.pq.and_l(c, LawsBase.wire_fits(n), fb)
          +g = {Wr.Got{FSc.ReqPace{min, k, Sc.Pace{r, s}, n}, rest} : Wr.Dec<FSc.Req>}
          +x4 = Wr.put_nat(n, rest)
          +x3 = Wr.put_nat(s, x4)
          +x2 = Wr.put_nat(r, x3)
          +x1 = Wr.put_nat(k, x2)
          %LWire.pc.nat(1n, Wr.put_nat(min, x1), {==}) : {FSc.get_req.of(_) == g : Wr.Dec<FSc.Req>}
          %LWire.pc.nat(min, x1, LLogicBool.pq.and_l(LawsBase.wire_fits(min), LawsBase.wire_fits(k), fa)) : {FSc.get_pacereq(_) == g : Wr.Dec<FSc.Req>}
          %LWire.pc.nat(k, x2, LLogicBool.pq.and_r(LawsBase.wire_fits(min), LawsBase.wire_fits(k), fa)) : {FSc.get_pacereq.k(min, _) == g : Wr.Dec<FSc.Req>}
          %LWire.pc.nat(r, x3, LLogicBool.pq.and_l(LawsBase.wire_fits(r), LawsBase.wire_fits(s), fc)) : {FSc.get_pacereq.p(min, k, FSc.get_pace.r(_)) == g : Wr.Dec<FSc.Req>}
          %LWire.pc.nat(s, x4, LLogicBool.pq.and_r(LawsBase.wire_fits(r), LawsBase.wire_fits(s), fc)) : {FSc.get_pacereq.p(min, k, FSc.get_pace.s(r, _)) == g : Wr.Dec<FSc.Req>}
          %LWire.pc.nat(n, rest, LLogicBool.pq.and_r(c, LawsBase.wire_fits(n), fb)) : {FSc.get_pacereq.n(min, k, Sc.Pace{r, s}, _) == g : Wr.Dec<FSc.Req>}
          {==}
    case FSc.ReqStack{+hs, +y, +rows}:
      +f = fits
      +a = Bool.and(LawsBase.wire_fits(List.length(&2, Nat, hs)), LawsBase.wire_nats_fit(hs))
      +b = Bool.and(LawsBase.wire_fits(y), LawsBase.wire_fits(rows))
      +fb = LLogicBool.pq.and_r(a, b, f)
      +g = {Wr.Got{FSc.ReqStack{hs, y, rows}, rest} : Wr.Dec<FSc.Req>}
      +x1 = Wr.put_nat(y, Wr.put_nat(rows, rest))
      %LWire.pc.nat(2n, Wr.put_list(~Nat, ~Wr.put_nat, hs, x1), {==}) : {FSc.get_req.of(_) == g : Wr.Dec<FSc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, hs, x1)), Wr.Got{hs, x1}, Wire.wire_list_round_trip(hs, x1, LLogicBool.pq.and_l(a, b, f))) : {FSc.get_stack(_) == g : Wr.Dec<FSc.Req>}
      %LWire.pc.nat(y, Wr.put_nat(rows, rest), LLogicBool.pq.and_l(LawsBase.wire_fits(y), LawsBase.wire_fits(rows), fb)) : {FSc.get_stack.y(hs, _) == g : Wr.Dec<FSc.Req>}
      %LWire.pc.nat(rows, rest, LLogicBool.pq.and_r(LawsBase.wire_fits(y), LawsBase.wire_fits(rows), fb)) : {FSc.get_stack.rows(hs, y, _) == g : Wr.Dec<FSc.Req>}
      {==}
    case FSc.ReqPaint{+ks}:
      %LWire.pc.nat(3n, Wr.put_list(~Bool, ~Wr.put_bool, ks, rest), {==}) : {FSc.get_req.of(_) == Wr.Got{FSc.ReqPaint{ks}, rest} : Wr.Dec<FSc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ks, rest)), Wr.Got{ks, rest}, scsp.bools.rt(ks, rest, fits)) : {FSc.get_paint(_) == Wr.Got{FSc.ReqPaint{ks}, rest} : Wr.Dec<FSc.Req>}
      {==}

# The answer
# ----------

def scsp.step(m: Maybe<&2, Sc.Paint>, -rest: String) -> {FSc.put_step(m, rest) == Screen.screen_spell_step(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          {==}
        case Sc.Fresh{f}:
          {==}
        case Sc.Kept{f}:
          {==}

# one, two and three checks: the reply is the spec's, case by case
def scsp.paint.c1(x1: Bool) -> {FSc.paint.reply.fit(True{}, [x1]) == Screen.screen_paint_reply.fit(True{}, [x1]) : String}:
  match x1:
    case True{}:
      {==}
    case False{}:
      {==}

def scsp.paint.c2(x1: Bool, x2: Bool) -> {FSc.paint.reply.fit(True{}, [x1, x2]) == Screen.screen_paint_reply.fit(True{}, [x1, x2]) : String}:
  match x1 x2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def scsp.paint.c3(x1: Bool, x2: Bool, x3: Bool) -> {FSc.paint.reply.fit(True{}, [x1, x2, x3]) == Screen.screen_paint_reply.fit(True{}, [x1, x2, x3]) : String}:
  match x1 x2 x3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the paint reply on at most three checks (b: whether at most three ran)
# is the spec's; more than three is the error on both sides
def scsp.paint.fit(b: Bool, +ks: List<&2, Bool>, e: {Nat.is_le(List.length(&2, Bool, ks), 3n) == b : Bool}) -> {FSc.paint.reply.fit(b, ks) == Screen.screen_paint_reply.fit(b, ks) : String}:
  match b:
    case True{}:
      match ks:
        case Nil{}:
          {==}
        case Con{x1, r1}:
          match r1:
            case Nil{}:
              scsp.paint.c1(x1)
            case Con{x2, r2}:
              match r2:
                case Nil{}:
                  scsp.paint.c2(x1, x2)
                case Con{x3, r3}:
                  match r3:
                    case Nil{}:
                      scsp.paint.c3(x1, x2, x3)
                    case Con{x4, r4}:
                      LAWireSpell.ws_absurd({FSc.paint.reply.fit(True{}, x1 <> x2 <> x3 <> x4 <> r4) == Screen.screen_paint_reply.fit(True{}, x1 <> x2 <> x3 <> x4 <> r4) : String}, Equal.sym(Bool, Nat.is_le(List.length(&2, Bool, x1 <> x2 <> x3 <> x4 <> r4), 3n), True{}, e))
    case False{}:
      {==}

def scsp.paint(+ks: List<&2, Bool>) -> {FSc.paint.reply(ks) == Screen.screen_paint_reply(ks) : String}:
  scsp.paint.fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks, {==})

# the entry's answer is the spelled reply of the model's decision
def scsp.answer(q: FSc.Req) -> {FSc.answer(q) == Screen.screen_spell_answer(q) : String}:
  match q:
    case FSc.ReqRun{+t, +es}:
      Equal.sym(String, Screen.screen_spell_tx(Sc.run(es, t), ""), FSc.put_tx(Sc.run(es, t), ""), scsp.tx(Sc.run(es, t), ""))
    case FSc.ReqPace{+min, +k, +p, +n}:
      scsp.pace(Sc.pace.run([Sc.Chunk{n}, Sc.Frame{}], min, k, p), "")
    case FSc.ReqStack{+hs, +y, +rows}:
      scsp.rects(Sc.vstack(hs, y, rows), "")
    case FSc.ReqPaint{+ks}:
      scsp.paint(ks)
