# eukhe: the proof of LAW notice_ffi_history

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# By induction on the asks: each spelled ask steps the entry as the rule
# answers it (LA.nt.step), the state stays the record of the asks before
# (Notice.nt_book), and the rule's answer is the spec's (LA.nt.rule).
def nh.go(qs: List<&2, No.Ask>, +past: List<&2, No.Ask>, +out: String, +hf: {Notice.nt_asks_fit(qs) == True{} : Bool}) -> {Notice.nt_run(qs, (FNo.Live{Notice.nt_book(past)}, out)) == out <> Notice.nt_replies(qs, past) : List<&2, String>}:
  match qs:
    case Nil{}:
      {==}
    case q <> +t:
      match q:
        case No.Shows{+sid, +m}:
          +bk = Notice.nt_book(past)
          +a = {No.Shows{sid, m} : No.Ask}
          +v = No.visible(bk, sid, m)
          +hq = LA.notice.pn.and_l(Notice.nt_ask_fits(a), Notice.nt_asks_fit(t), hf)
          +ht = LA.notice.pn.and_r(Notice.nt_ask_fits(a), Notice.nt_asks_fit(t), hf)
          %Equal.sym(FNo.St & String, FNo.step(FNo.Live{bk}, Notice.nt_spell_ask(a, "")), Notice.nt_spell_step(No.answer(bk, a)), LA.nt.step(bk, a, hq)) : {out <> Notice.nt_run(t, _) == out <> Notice.nt_replies(a <> t, past) : List<&2, String>}
          %Equal.sym(List<&2, String>, Notice.nt_run(t, (FNo.Live{bk}, Wr.put_bool(v, ""))), Wr.put_bool(v, "") <> Notice.nt_replies(t, a <> past), nh.go(t, a <> past, Wr.put_bool(v, ""), ht)) : {out <> _ == out <> Notice.nt_replies(a <> t, past) : List<&2, String>}
          %LA.nt.rule(past, sid, m) : {out <> (Wr.put_bool(v, "") <> Notice.nt_replies(t, a <> past)) == out <> (Wr.put_bool(_, "") <> Notice.nt_replies(t, a <> past)) : List<&2, String>}
          {==}
        case No.Notes{+sid, +ms}:
          +bk = Notice.nt_book(past)
          +a = {No.Notes{sid, ms} : No.Ask}
          +hq = LA.notice.pn.and_l(Notice.nt_ask_fits(a), Notice.nt_asks_fit(t), hf)
          +ht = LA.notice.pn.and_r(Notice.nt_ask_fits(a), Notice.nt_asks_fit(t), hf)
          %Equal.sym(FNo.St & String, FNo.step(FNo.Live{bk}, Notice.nt_spell_ask(a, "")), Notice.nt_spell_step(No.answer(bk, a)), LA.nt.step(bk, a, hq)) : {out <> Notice.nt_run(t, _) == out <> Notice.nt_replies(a <> t, past) : List<&2, String>}
          %Equal.sym(List<&2, String>, Notice.nt_run(t, (FNo.Live{No.record(bk, sid, ms)}, "")), "" <> Notice.nt_replies(t, a <> past), nh.go(t, a <> past, "", ht)) : {out <> _ == out <> Notice.nt_replies(a <> t, past) : List<&2, String>}
          {==}

def Notice.notice_ffi_history(qs, h):
  nh.go(qs, Nil{}, "", h)
