# eukhe: the proof of LAW log_ffi_exact
#
# The entry reads the length and the last newline as the spec's reader
# does (lfe.last_tag), then answers the open's decision, which is the
# spec's on any facts (log_tail_exact), spelled as the spec does
# (lfe.spell); every other path is the same error form on both sides.

import Base
import ../../bend/log.bend as Lr
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log
import ./log_tail_exact.bend as PLogTailExact

def lfe.spell(t: Lr.Tail) -> {FLg.put_tail(t, "") == Log.log_spell_tail(t) : String}:
  match t:
    case Lr.Whole{}:
      {==}
    case Lr.Torn{to}:
      {==}
    case Lr.Odd{}:
      {==}

def lfe.last_some(r: Wr.Dec<Nat>) -> {Log.log_rd_last.some(r) == FLg.get_last.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def lfe.last_tag(r: Wr.Dec<Nat>) -> {Log.log_rd_last(r) == FLg.get_last.tag(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              lfe.last_some(Wr.get_nat(s))
            case 1n+q:
              {==}
    case Wr.Bad{}:
      {==}

def lfe.end(b: Bool, +len: Nat, +last: Maybe<&2, Nat>) -> {FLg.ffi.end(b, FLg.Req{len, last}) == Log.log_ffi_spec.end(b, len, last) : String}:
  match b:
    case True{}:
      %Log.log_tail_exact(len, last) : {FLg.put_tail(Lr.tail(len, last), "") == Log.log_spell_tail(_) : String}
      lfe.spell(Lr.tail(len, last))
    case False{}:
      {==}

def lfe.last(len: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {FLg.ffi.go(FLg.get_req.last(len, r)) == Log.log_ffi_spec.last(len, r) : String}:
  match r:
    case Wr.Got{m, s}:
      lfe.end(Wr.end(s), len, m)
    case Wr.Bad{}:
      {==}

def lfe.len(r: Wr.Dec<Nat>) -> {FLg.ffi.go(FLg.get_req.len(r)) == Log.log_ffi_spec.len(r) : String}:
  match r:
    case Wr.Got{n, +s}:
      %lfe.last_tag(Wr.get_nat(s)) : {FLg.ffi.go(FLg.get_req.last(n, _)) == Log.log_ffi_spec.last(n, Log.log_rd_last(Wr.get_nat(s))) : String}
      lfe.last(n, Log.log_rd_last(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def Log.log_ffi_exact(s):
  lfe.len(Wr.get_nat(s))
