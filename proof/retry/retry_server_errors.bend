# eukhe: the proof of LAW retry_server_errors

import Base
import ../../bend/retry.bend as R
import ../../laws/retry.bend as Retry
import ../base.bend as L

def rp.server(lt: Bool, +s: Nat, e: {lt == False{} : Bool}) -> {R.status.ok.go(lt, s) == True{} : Bool}:
  match lt:
    case True{}:
      L.rp.absurdT({R.status.ok.go(True{}, s) == True{} : Bool}, e)
    case False{}:
      {==}

def server_errors(kind: Maybe<&2, R.Cause>, text: Bool, +s: Nat, server: {Nat.is_lt(s, 500n) == False{} : Bool}) -> {R.retryable(R.Facts{False{}, False{}, Some{s}, kind, text}) == True{} : Bool}:
  rp.server(Nat.is_lt(s, 500n), s, server)

def Retry.retry_server_errors(kind, text, s, server):
  server_errors(kind, text, s, server)
