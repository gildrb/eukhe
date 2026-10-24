# eukhe: the proof of LAW quirks_lookup_malformed
# The entry reads every lookup as the laws' reader does; where that reader
# finds no four Nats, the entry answers the error form and keeps the
# rulebook.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def lm.four(rs: List<&2, If.Rule>, xs: List<&2, Nat>, no: {Quirks.read_four(xs) == None{} : Maybe<&2, Quirks.QsLookup>}) -> {FQ.step.ask(rs, FQ.ask(xs)) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}:
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
                case d <> e:
                  match e:
                    case Nil{}:
                      QP.qp.some_none(Quirks.QsLookup, Quirks.QsLookup{If.Query{f, m, h}, d}, {FQ.step.ask(rs, FQ.ask([f, m, h, d])) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}, no)
                    case x <> y:
                      {==}

def lm.end(b: Bool, rs: List<&2, If.Rule>, xs: List<&2, Nat>, no: {Quirks.read_lookup.end(b, xs) == None{} : Maybe<&2, Quirks.QsLookup>}) -> {FQ.step.end(b, rs, xs) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}:
  match b:
    case True{}:
      lm.four(rs, xs, no)
    case False{}:
      {==}

def lm.got(rs: List<&2, If.Rule>, d: Wr.Dec<List<&2, Nat>>, no: {Quirks.read_lookup.got(d) == None{} : Maybe<&2, Quirks.QsLookup>}) -> {FQ.step.book(rs, d) == (FQ.Book{rs}, SCon{'E', SCon{' ', "quirks: malformed lookup"}}) : FQ.St & String}:
  match d:
    case Wr.Got{xs, s}:
      lm.end(Wr.end(s), rs, xs, no)
    case Wr.Bad{}:
      {==}

def Quirks.quirks_lookup_malformed(rs, s, no):
  lm.got(rs, Wr.get_list(~Nat, ~Wr.get_nat, s), no)
