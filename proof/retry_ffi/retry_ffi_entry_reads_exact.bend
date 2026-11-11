# eukhe: the proof of LAW retry_ffi_entry_reads_exact
# The entry decodes the request the laws' reader reads (LARetryFfi.rf.rq),
# finds no input after it, and answers the model's decision, which each
# exact law ties to its spec; the entry's reply writers write what the
# laws spell (LARetryFfi.rf.delay, rf.switch).

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry
import ../../laws/retry_ffi.bend as RetryFfi
import ../retry/retry_classifier_exact.bend as PRetryClassifierExact
import ../retry/failover_exact.bend as PFailoverExact
import ./retry_wait_exact.bend as PRetryWaitExact
import ./base.bend as LARetryFfi

# the model's answer to a request is the specs' answer
def re.answer(q: Fr.Req) -> {Fr.answer(q) == RetryFfi.spec_answer(q) : String}:
  match q:
    case Fr.QClassify{+f}:
      Equal.cong(Bool, String, x => Wr.put_bool(x, ""), R.retryable(f), Retry.rs.retryable(f), Retry.retry_classifier_exact(f))
    case Fr.QWait{+base, +attempt, +cap, +draw, +server}:
      +W = RetryFfi.wait_spec(base, attempt, cap, draw, server)
      Equal.trans(String, Fr.put_delay(R.retry_wait(base, attempt, cap, draw, server), ""), Fr.put_delay(W, ""), RetryFfi.spell_delay(W),
        Equal.cong(R.Delay, String, x => Fr.put_delay(x, ""), R.retry_wait(base, attempt, cap, draw, server), W, RetryFfi.retry_wait_exact(base, attempt, cap, draw, server)), LARetryFfi.rf.delay(W))
    case Fr.QFailover{+len, +ts, +p}:
      +N = Retry.rs.next(len, ts, p)
      Equal.trans(String, Fr.put_switch(R.next(len, ts, p), ""), Fr.put_switch(N, ""), RetryFfi.spell_switch(N),
        Equal.cong(Maybe<&2, R.Switch>, String, x => Fr.put_switch(x, ""), R.next(len, ts, p), N, Retry.failover_exact(len, ts, p)), LARetryFfi.rf.switch(N))
    case Fr.QStall{+idle}:
      {==}

def RetryFfi.retry_ffi_entry_reads_exact(s, q, rest, got, whole):
  %Equal.trans(Wr.Dec<Fr.Req>, Wr.Got{q, rest}, RetryFfi.read_req.go(Wr.get_nat(s)), Fr.get_req.start(Wr.get_nat(s)), Equal.sym(Wr.Dec<Fr.Req>, RetryFfi.read_req(s), Wr.Got{q, rest}, got), LARetryFfi.rf.rq(Wr.get_nat(s))) : {Fr.ffi.got(_) == RetryFfi.spec_answer(q) : String}
  %Equal.sym(Bool, Wr.end(rest), True{}, whole) : {Fr.ffi.done(q, _) == RetryFfi.spec_answer(q) : String}
  re.answer(q)
