# eukhe: the proof of LAW retry_ffi_entry_answers
# The laws' spelling of a request is the entry's encoding (LARetryFfi.rf.req),
# so the entry answers as laws/retry.bend's retry_ffi_* laws state; the
# entry's reply writers write what the laws spell.

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_ffi_classify.bend as PRetryFfiClassify
import ../retry/retry_ffi_wait.bend as PRetryFfiWait
import ../retry/retry_ffi_failover.bend as PRetryFfiFailover
import ../retry/retry_ffi_stall.bend as PRetryFfiStall
import ./base.bend as LARetryFfi

def RetryFfi.retry_ffi_entry_answers(q, fits):
  match q:
    case Fr.QClassify{+f}:
      %Equal.sym(String, RetryFfi.spell_req(Fr.QClassify{f}), Fr.put_req(Fr.QClassify{f}, ""), LARetryFfi.rf.req(Fr.QClassify{f})) : {Fr.ffi(_) == RetryFfi.spell_answer(Fr.QClassify{f}) : String}
      Retry.retry_ffi_classify(f, fits)
    case Fr.QWait{+base, +attempt, +cap, +draw, +server}:
      %Equal.sym(String, RetryFfi.spell_req(Fr.QWait{base, attempt, cap, draw, server}), Fr.put_req(Fr.QWait{base, attempt, cap, draw, server}, ""), LARetryFfi.rf.req(Fr.QWait{base, attempt, cap, draw, server})) : {Fr.ffi(_) == RetryFfi.spell_answer(Fr.QWait{base, attempt, cap, draw, server}) : String}
      Equal.trans(String, Fr.ffi(Fr.put_req(Fr.QWait{base, attempt, cap, draw, server}, "")), Fr.put_delay(R.retry_wait(base, attempt, cap, draw, server), ""), RetryFfi.spell_delay(R.retry_wait(base, attempt, cap, draw, server)),
        Retry.retry_ffi_wait(base, attempt, cap, draw, server, fits), LARetryFfi.rf.delay(R.retry_wait(base, attempt, cap, draw, server)))
    case Fr.QFailover{+len, +ts, +p}:
      %Equal.sym(String, RetryFfi.spell_req(Fr.QFailover{len, ts, p}), Fr.put_req(Fr.QFailover{len, ts, p}, ""), LARetryFfi.rf.req(Fr.QFailover{len, ts, p})) : {Fr.ffi(_) == RetryFfi.spell_answer(Fr.QFailover{len, ts, p}) : String}
      Equal.trans(String, Fr.ffi(Fr.put_req(Fr.QFailover{len, ts, p}, "")), Fr.put_switch(R.next(len, ts, p), ""), RetryFfi.spell_switch(R.next(len, ts, p)),
        Retry.retry_ffi_failover(len, ts, p, fits), LARetryFfi.rf.switch(R.next(len, ts, p)))
    case Fr.QStall{+idle}:
      %Equal.sym(String, RetryFfi.spell_req(Fr.QStall{idle}), Fr.put_req(Fr.QStall{idle}, ""), LARetryFfi.rf.req(Fr.QStall{idle})) : {Fr.ffi(_) == RetryFfi.spell_answer(Fr.QStall{idle}) : String}
      Retry.retry_ffi_stall(idle, fits)
