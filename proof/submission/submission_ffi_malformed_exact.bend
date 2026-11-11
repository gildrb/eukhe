# eukhe: the proof of LAW submission_ffi_malformed_exact

import Base
import ../../bend/submission.bend as Sb
import ../../bend/ffi_submission.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/submission.bend as Submission

# PROOF of LAW submission_ffi_malformed_exact: the code's decoder and the spec reader read the
# same numbers stage by stage (sb_bad and the stages below it); where the
# reader answers Bad (a missing id, an unknown tag) the decoder answers Bad
# and the entry the malformed error form; where it reads a whole request the
# premise is false (sb_got_bad).

# a request read whole is no Bad: a contradiction
def sb_dec_if(d: Wr.Dec<Submission.SpecReq>, G: Type) -> Type:
  match d:
    case Wr.Got{q, s}:
      Unit
    case Wr.Bad{}:
      G

def sb_got_bad(-q: Submission.SpecReq, -s: String, -G: Type, e: {Wr.Got{q, s} == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> G:
  %e : sb_dec_if(_, G)
  Unit{}

def sb_bad_one(-x: Sb.Sub, d: Wr.Dec<Nat>, k: Nat, no: {Submission.read_req.change(x, Submission.read_change.one(d, k)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.change(x, FSb.get_change.one(d, k)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{n, s}:
      match k:
        case 0n:
          sb_got_bad(Submission.SpecReq{x, Sb.Place{n}}, s, {FSb.ffi.change(x, FSb.get_change.one(Wr.Got{n, s}, 0n)) == Wr.err("submission: malformed request") : String}, no)
        case 1n+u:
          sb_got_bad(Submission.SpecReq{x, Sb.Answer{n}}, s, {FSb.ffi.change(x, FSb.get_change.one(Wr.Got{n, s}, 1n+u)) == Wr.err("submission: malformed request") : String}, no)
    case Wr.Bad{}:
      {==}

def sb_bad_ch(-x: Sb.Sub, d: Wr.Dec<Nat>, no: {Submission.read_req.change(x, Submission.read_change(d)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.change(x, FSb.get_change(d)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sb_bad_one(x, Wr.get_nat(s), 0n, no)
        case 1n:
          sb_bad_one(x, Wr.get_nat(s), 1n, no)
        case 2n:
          sb_got_bad(Submission.SpecReq{x, Sb.Drop{}}, s, {FSb.ffi.change(x, FSb.get_change(Wr.Got{2n, s})) == Wr.err("submission: malformed request") : String}, no)
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def sb_bad_subone(d: Wr.Dec<Nat>, k: Nat, no: {Submission.read_req(Submission.read_sub.one(d, k)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.got(FSb.get_sub.one(d, k)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{e, s}:
      match k:
        case 0n:
          sb_bad_ch(Sb.InPlaced{e}, Wr.get_nat(s), no)
        case 1n:
          sb_bad_ch(Sb.InDropped{Some{e}}, Wr.get_nat(s), no)
        case 2n+u:
          sb_bad_ch(Sb.WrPlaced{e}, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def sb_bad_ans(e: Nat, d: Wr.Dec<Nat>, no: {Submission.read_req(Submission.read_sub.answer(e, d)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.got(FSb.get_sub.answer(e, d)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{a, s}:
      sb_bad_ch(Sb.InAnswered{e, a}, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def sb_bad_two(d: Wr.Dec<Nat>, no: {Submission.read_req(Submission.read_sub.two(d)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.got(FSb.get_sub.two(d)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{e, s}:
      sb_bad_ans(e, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def sb_bad(d: Wr.Dec<Nat>, no: {Submission.read_req(Submission.read_sub(d)) == Wr.Bad{} : Wr.Dec<Submission.SpecReq>}) -> {FSb.ffi.got(FSb.get_sub(d)) == Wr.err("submission: malformed request") : String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          sb_bad_ch(Sb.InQueued{}, Wr.get_nat(s), no)
        case 1n:
          sb_bad_subone(Wr.get_nat(s), 0n, no)
        case 2n:
          sb_bad_two(Wr.get_nat(s), no)
        case 3n:
          sb_bad_ch(Sb.InDropped{None{}}, Wr.get_nat(s), no)
        case 4n:
          sb_bad_subone(Wr.get_nat(s), 1n, no)
        case 5n:
          sb_bad_ch(Sb.WrQueued{}, Wr.get_nat(s), no)
        case 6n:
          sb_bad_subone(Wr.get_nat(s), 2n, no)
        case 7n:
          sb_bad_ch(Sb.WrDropped{}, Wr.get_nat(s), no)
        case 8n+u:
          {==}
    case Wr.Bad{}:
      {==}

def Submission.submission_ffi_malformed_exact(x, no):
  sb_bad(Wr.get_nat(x), no)
