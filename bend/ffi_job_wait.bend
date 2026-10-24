import Base
import ./wire.bend as W
import ./job.bend as M

# ffi_job_wait: one poll of a blocking wait on a job (bend/job.bend
# `poll`) as an entry of the compiled Bend core. Request: T|F (the
# deadline passed), then T|F (the job's end is ready). Reply: the turn's
# tag: 0 the call waits, 1 it settles with the end, 2 it detaches. Any
# other input: the error form, `job_wait: malformed request`.

def put_turn(t: M.Turn) -> String:
  match t:
    case M.Waits{}:
      W.put_nat(0n, "")
    case M.Settles{}:
      W.put_nat(1n, "")
    case M.Detaches{}:
      W.put_nat(2n, "")

def run.end(whole: Bool, due: Bool, ready: Bool) -> String:
  match whole:
    case True{}:
      put_turn(M.poll(due, ready))
    case False{}:
      W.err("job_wait: malformed request")

def run.ready(due: Bool, r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{ready, s}:
      run.end(W.end(s), due, ready)
    case W.Bad{}:
      W.err("job_wait: malformed request")

def run(r: W.Dec<Bool>) -> String:
  match r:
    case W.Got{due, s}:
      run.ready(due, W.get_bool(s))
    case W.Bad{}:
      W.err("job_wait: malformed request")

def ffi(input: String) -> String:
  run(W.get_bool(input))
