# eukhe: the proof of LAW privacy_ip_entry_spec
#
# PROOF: the entry decodes the list of strings with the same wire
# decoder the laws' reader uses; its pairing is the laws' (pes.pairs) and
# its answers are the laws' (pen.answers), so each decoded input, whole
# or not, answers as the laws' reader says (pes.got).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ./base/entry.bend as LPE
import ../../laws/privacy/entry.bend as PrivacyEntry

def pes.cons(c: FP.Cand, m: Maybe<&2, List<&2, FP.Cand>>) -> {FP.pairs.cons(c, m) == PrivacyEntry.read_pairs.cons(c, m) : Maybe<&2, List<&2, FP.Cand>>}:
  match m:
    case None{}:
      {==}
    case Some{cs}:
      {==}

# the entry pairs strings as the laws do
def pes.pairs(xs: List<&2, String>) -> {FP.pairs(xs) == PrivacyEntry.read_pairs(xs) : Maybe<&2, List<&2, FP.Cand>>}:
  match xs:
    case Nil{}:
      {==}
    case +b <> more:
      match more:
        case Nil{}:
          {==}
        case +r <> +t:
          %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(t), PrivacyEntry.read_pairs(t), pes.pairs(t)) : {FP.pairs.cons(FP.Cand{b, r}, _) == PrivacyEntry.read_pairs.cons(FP.Cand{b, r}, PrivacyEntry.read_pairs(t)) : Maybe<&2, List<&2, FP.Cand>>}
          pes.cons(FP.Cand{b, r}, PrivacyEntry.read_pairs(t))

def pes.m(m: Maybe<&2, List<&2, FP.Cand>>) -> {FP.ffi.end(True{}, m) == PrivacyEntry.call_reply(m) : String}:
  match m:
    case Some{+cs}:
      %Equal.sym(List<&2, Nat>, FP.answers(cs), PrivacyEntry.answers(cs), LPE.pen.answers(cs)) : {Wr.put_list(~Nat, ~Wr.put_nat, _, "") == PrivacyEntry.spell_answers(cs) : String}
      {==}
    case None{}:
      {==}

def pes.end(e: Bool, +xs: List<&2, String>) -> {FP.ffi.end(e, FP.pairs(xs)) == PrivacyEntry.call_reply(PrivacyEntry.read_cands.end(e, xs)) : String}:
  match e:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(xs), PrivacyEntry.read_pairs(xs), pes.pairs(xs)) : {FP.ffi.end(True{}, _) == PrivacyEntry.call_reply(PrivacyEntry.read_pairs(xs)) : String}
      pes.m(PrivacyEntry.read_pairs(xs))
    case False{}:
      {==}

# every decoded input answers as the laws' reader says
def pes.got(d: Wr.Dec<List<&2, String>>) -> {FP.ffi.got(d) == PrivacyEntry.call_reply(PrivacyEntry.read_cands.whole(d)) : String}:
  match d:
    case Wr.Got{+xs, +s}:
      pes.end(Wr.end(s), xs)
    case Wr.Bad{}:
      {==}

def PrivacyEntry.privacy_ip_entry_spec(s):
  pes.got(Wr.get_list(~String, ~Wr.get_str, s))
