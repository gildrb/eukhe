# eukhe: the proof of LAW idle_stalls_once
# A reply `1,0,` comes only from a live deadline's fire whose decision is
# the stall (so.st: a shut stepper, garbage, an ended deadline, a life, a
# hold and a sleep all answer otherwise), and leaves the deadline ended.
# An ended deadline stays ended whatever input comes (so.over_any), and
# answers every spelled event `0,`.

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ./base.bend as LA

# a reply String.eq tells apart from a stall is not a stall
def so.ne(+x: String, -G: Type, h: {x == "1,0," : String}, ne: {String.eq(x, "1,0,") == False{} : Bool}) -> G:
  LA.ri.absurd(G, Equal.trans(Bool, False{}, String.eq(x, "1,0,"), True{}, Equal.sym(Bool, String.eq(x, "1,0,"), False{}, ne), Equal.cong(String, Bool, y => String.eq(y, "1,0,"), x, "1,0,", h)))

def so.end(+d: Nat, +l: Nat, +h: Nat, b: Bool, e: R.IdleEv) -> {Fi.Live{R.IdleSt{d, l, h, True{}}} == RetryIdle.ri_state(Fi.step.end(b, R.IdleSt{d, l, h, True{}}, e)) : Fi.St}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def so.ev(+d: Nat, +l: Nat, +h: Nat, r: Wr.Dec<R.IdleEv>) -> {Fi.Live{R.IdleSt{d, l, h, True{}}} == RetryIdle.ri_state(Fi.step.ev(R.IdleSt{d, l, h, True{}}, r)) : Fi.St}:
  match r:
    case Wr.Got{e, rest}:
      so.end(d, l, h, Wr.end(rest), e)
    case Wr.Bad{}:
      {==}

# an ended deadline stays ended, whatever input comes
def so.over_any(+d: Nat, +l: Nat, +h: Nat, i: String) -> {Fi.Live{R.IdleSt{d, l, h, True{}}} == RetryIdle.ri_state(Fi.step(Fi.Live{R.IdleSt{d, l, h, True{}}}, i)) : Fi.St}:
  so.ev(d, l, h, Fi.get_ev(i))

def so.feed_over(mid: List<&2, R.IdleEv>, +d: Nat, +l: Nat, +h: Nat) -> {Fi.Live{R.IdleSt{d, l, h, True{}}} == RetryIdle.ri_feed(mid, Fi.Live{R.IdleSt{d, l, h, True{}}}) : Fi.St}:
  match mid:
    case Nil{}:
      {==}
    case +x <> +rest:
      %so.over_any(d, l, h, RetryIdle.spell_ev(x)) : {Fi.Live{R.IdleSt{d, l, h, True{}}} == RetryIdle.ri_feed(rest, _) : Fi.St}
      so.feed_over(rest, d, l, h)

# an ended deadline answers every spelled event nothing
def so.last(+d: Nat, +l: Nat, +h: Nat, mid: List<&2, R.IdleEv>, +e2: R.IdleEv, fits: {RetryIdle.ev_fits(e2) == True{} : Bool}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, Fi.Live{R.IdleSt{d, l, h, True{}}}), RetryIdle.spell_ev(e2))) == "0," : String}:
  %so.feed_over(mid, d, l, h) : {RetryIdle.ri_reply(Fi.step(_, RetryIdle.spell_ev(e2))) == "0," : String}
  %Equal.sym(Fi.St & String, Fi.step(Fi.Live{R.IdleSt{d, l, h, True{}}}, RetryIdle.spell_ev(e2)), Fi.reply(R.idle.step(R.IdleSt{d, l, h, True{}}, e2)), LA.ri.ev(R.IdleSt{d, l, h, True{}}, e2, fits)) : {RetryIdle.ri_reply(_) == "0," : String}
  {==}

def so.w(w: R.Wake, +d: Nat, +l: Nat, +h: Nat, mid: List<&2, R.IdleEv>, +e2: R.IdleEv, fits: {RetryIdle.ev_fits(e2) == True{} : Bool}, hs: {RetryIdle.ri_reply(Fi.reply(R.idle.fired(d, l, h, w))) == "1,0," : String}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.reply(R.idle.fired(d, l, h, w)))), RetryIdle.spell_ev(e2))) == "0," : String}:
  match w:
    case R.WakeStall{}:
      so.last(d, l, h, mid, e2, fits)
    case R.WakeSleep{us}:
      so.ne(RetryIdle.ri_reply(Fi.reply(R.idle.fired(d, l, h, R.WakeSleep{us}))), {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, Fi.Live{R.IdleSt{d, l, h, False{}}}), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})

def so.b(b: Bool, s: R.IdleSt, e: R.IdleEv, mid: List<&2, R.IdleEv>, +e2: R.IdleEv, fits: {RetryIdle.ev_fits(e2) == True{} : Bool}, hs: {RetryIdle.ri_reply(Fi.step.end(b, s, e)) == "1,0," : String}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(b, s, e))), RetryIdle.spell_ev(e2))) == "0," : String}:
  match b:
    case False{}:
      so.ne(RetryIdle.ri_reply(Fi.step.end(False{}, s, e)), {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(False{}, s, e))), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})
    case True{}:
      match s:
        case R.IdleSt{+d, +l, +h, over}:
          match over:
            case True{}:
              so.ne("0,", {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(True{}, R.IdleSt{d, l, h, True{}}, e))), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})
            case False{}:
              match e:
                case R.IdleLife{now}:
                  so.ne("0,", {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(True{}, R.IdleSt{d, l, h, False{}}, R.IdleLife{now}))), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})
                case R.IdleHold{}:
                  so.ne("0,", {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(True{}, R.IdleSt{d, l, h, False{}}, R.IdleHold{}))), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})
                case R.IdleFree{now}:
                  so.ne("0,", {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.end(True{}, R.IdleSt{d, l, h, False{}}, R.IdleFree{now}))), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})
                case R.IdleFire{now}:
                  so.w(R.idle.wake(R.idle.held(h), Nat.sub(now, l), d), d, l, h, mid, e2, fits, hs)

def so.r(s: R.IdleSt, r: Wr.Dec<R.IdleEv>, mid: List<&2, R.IdleEv>, +e2: R.IdleEv, fits: {RetryIdle.ev_fits(e2) == True{} : Bool}, hs: {RetryIdle.ri_reply(Fi.step.ev(s, r)) == "1,0," : String}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step.ev(s, r))), RetryIdle.spell_ev(e2))) == "0," : String}:
  match r:
    case Wr.Got{e, rest}:
      so.b(Wr.end(rest), s, e, mid, e2, fits, hs)
    case Wr.Bad{}:
      so.ne(Fi.fail(), {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, Fi.Live{s}), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})

# a reply `1,0,` leaves an ended deadline, which answers every later
# spelled event nothing
def so.st(st: Fi.St, i: String, mid: List<&2, R.IdleEv>, +e2: R.IdleEv, fits: {RetryIdle.ev_fits(e2) == True{} : Bool}, hs: {RetryIdle.ri_reply(Fi.step(st, i)) == "1,0," : String}) -> {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, RetryIdle.ri_state(Fi.step(st, i))), RetryIdle.spell_ev(e2))) == "0," : String}:
  match st:
    case Fi.Live{s}:
      so.r(s, Fi.get_ev(i), mid, e2, fits, hs)
    case Fi.Shut{}:
      so.ne(SCon{'E', SCon{' ', "retry_idle: no deadline"}}, {RetryIdle.ri_reply(Fi.step(RetryIdle.ri_feed(mid, Fi.Shut{}), RetryIdle.spell_ev(e2))) == "0," : String}, hs, {==})

# the events pre then ys, fed one list at a time
def so.feed_app(pre: List<&2, R.IdleEv>, +ys: List<&2, R.IdleEv>, st: Fi.St) -> {RetryIdle.ri_feed(ys, RetryIdle.ri_feed(pre, st)) == RetryIdle.ri_feed(List.append(&2, R.IdleEv, pre, ys), st) : Fi.St}:
  match pre:
    case Nil{}:
      {==}
    case +x <> +rest:
      so.feed_app(rest, ys, RetryIdle.ri_state(Fi.step(st, RetryIdle.spell_ev(x))))

def RetryIdle.idle_stalls_once(d, pre, e, mid, e2, fits, stalled):
  %so.feed_app(pre, e <> mid, RetryIdle.ri_opened(d)) : {RetryIdle.ri_reply(Fi.step(_, RetryIdle.spell_ev(e2))) == "0," : String}
  so.st(RetryIdle.ri_feed(pre, RetryIdle.ri_opened(d)), RetryIdle.spell_ev(e), mid, e2, fits, stalled)
