# eukhe: the proof of LAW quirks_step_total
# The entry reads every lookup as the laws' reader does; four Nats are
# answered with the model's lookup, which is the spec's
# (quirks_lookup_exact), spelled as the spec spells it (QP.qp.ans);
# anything else is the error form; the rulebook is kept.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP
import ./quirks_lookup_exact.bend as LE

def stt.four(+rs: List<&2, If.Rule>, xs: List<&2, Nat>) -> {FQ.step.ask(rs, FQ.ask(xs)) == Quirks.qs_step.of(rs, Quirks.read_four(xs)) : FQ.St & String}:
  match xs:
    case Nil{}:
      {==}
    case f <> a:
      match a:
        case Nil{}:
          {==}
        case m <> b:
          match b:
            case Nil{}:
              {==}
            case h <> c:
              match c:
                case Nil{}:
                  {==}
                case +d <> e:
                  match e:
                    case Nil{}:
                      +q = {If.Query{f, m, h} : If.Query}
                      %Quirks.quirks_lookup_exact(rs, q, d) : {(FQ.Book{rs}, FQ.put_ans(If.lookup(rs, q, d), "")) == (FQ.Book{rs}, Quirks.spell_ans(_)) : FQ.St & String}
                      %QP.qp.ans(If.lookup(rs, q, d)) : {(FQ.Book{rs}, FQ.put_ans(If.lookup(rs, q, d), "")) == (FQ.Book{rs}, _) : FQ.St & String}
                      {==}
                    case x <> y:
                      {==}

def stt.end(b: Bool, +rs: List<&2, If.Rule>, xs: List<&2, Nat>) -> {FQ.step.end(b, rs, xs) == Quirks.qs_step.of(rs, Quirks.read_lookup.end(b, xs)) : FQ.St & String}:
  match b:
    case True{}:
      stt.four(rs, xs)
    case False{}:
      {==}

def stt.got(+rs: List<&2, If.Rule>, d: Wr.Dec<List<&2, Nat>>) -> {FQ.step.book(rs, d) == Quirks.qs_step.of(rs, Quirks.read_lookup.got(d)) : FQ.St & String}:
  match d:
    case Wr.Got{xs, s}:
      stt.end(Wr.end(s), rs, xs)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_step_total(rs, s):
  stt.got(rs, Wr.get_list(~Nat, ~Wr.get_nat, s))
