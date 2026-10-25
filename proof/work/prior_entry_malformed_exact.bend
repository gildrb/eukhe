# eukhe: the proof of LAW prior_entry_malformed_exact
# The laws' reader and the entry read each stage alike; where the reader
# finds no whole request, the entry answers its error form.

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../base/progress.bend as LProgress

def pme.work(r: Bool, g: Bool, +n: Nat, d: Wr.Dec<Nat>) -> {Work.pe_read.work(r, g, n, d) == FW.get_last.work(r, g, n, d) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match d:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pme.stalls(r: Bool, g: Bool, d: Wr.Dec<Nat>) -> {Work.pe_read.stalls(r, g, d) == FW.get_last.stalls(r, g, d) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match d:
    case Wr.Got{+n, s}:
      pme.work(r, g, n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pme.goal(r: Bool, d: Wr.Dec<Bool>) -> {Work.pe_read.goal(r, d) == FW.get_last.goal(r, d) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match d:
    case Wr.Got{g, s}:
      pme.stalls(r, g, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pme.run(d: Wr.Dec<Bool>) -> {Work.pe_read.run(d) == FW.get_last.run(d) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match d:
    case Wr.Got{r, s}:
      pme.goal(r, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def pme.tag(n: Nat, s: String) -> {Work.pe_read.tag(n, s) == FW.get_last.tag(n, s) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match n:
    case 0n:
      {==}
    case 1n:
      pme.run(Wr.get_bool(s))
    case 2n+q:
      {==}

# the laws' reader of a request is the entry's
def pme.go(r: Wr.Dec<Nat>) -> {Work.pe_read.go(r) == FW.get_last.go(r) : Wr.Dec<Maybe<&2, Pr.Last>>}:
  match r:
    case Wr.Got{n, s}:
      pme.tag(n, s)
    case Wr.Bad{}:
      {==}

def pme.end(b: Bool, m: Maybe<&2, Pr.Last>, no: {Work.pe_read.end(b, m) == None{} : Maybe<&2, Maybe<&2, Pr.Last>>}) -> {FW.run.end(b, m) == SCon{'E', SCon{' ', "work: malformed request"}} : String}:
  match b:
    case True{}:
      LProgress.pw.some_none(Maybe<&2, Pr.Last>, m, {FW.put_prior(Pr.compared(m)) == SCon{'E', SCon{' ', "work: malformed request"}} : String}, no)
    case False{}:
      {==}

def pme.whole(r: Wr.Dec<Maybe<&2, Pr.Last>>, no: {Work.pe_read.whole(r) == None{} : Maybe<&2, Maybe<&2, Pr.Last>>}) -> {FW.run(r) == SCon{'E', SCon{' ', "work: malformed request"}} : String}:
  match r:
    case Wr.Got{m, s}:
      pme.end(Wr.end(s), m, no)
    case Wr.Bad{}:
      {==}

def Work.prior_entry_malformed_exact(s, no):
  %pme.go(Wr.get_nat(s)) : {FW.run(_) == SCon{'E', SCon{' ', "work: malformed request"}} : String}
  pme.whole(Work.pe_read.go(Wr.get_nat(s)), no)
