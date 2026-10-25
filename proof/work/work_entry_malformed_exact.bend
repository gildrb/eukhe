# eukhe: the proof of LAW work_entry_malformed_exact
# The laws' reader and the entry read each stage alike (the list loops
# too, item by item); where the reader finds no whole event, the entry
# answers its error form and keeps the ledger.

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../base/progress.bend as LProgress

# The laws' reader, stage by stage, is the entry's
# ------------------------------------------------

def wq.blk_res(+k: Nat, r: Wr.Dec<Nat>) -> {Work.wk_read_blk.res(k, r) == FW.get_blk.res.fp(k, r) : Wr.Dec<Pr.Blk>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.blk_call(+k: Nat, r: Wr.Dec<Nat>) -> {Work.wk_read_blk.call(k, r) == FW.get_blk.call.fp(k, r) : Wr.Dec<Pr.Blk>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.blk_rkey(r: Wr.Dec<Nat>) -> {Work.wk_read_blk.rkey(r) == FW.get_blk.res(r) : Wr.Dec<Pr.Blk>}:
  match r:
    case Wr.Got{+k, s}:
      wq.blk_res(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wq.blk_ckey(r: Wr.Dec<Nat>) -> {Work.wk_read_blk.ckey(r) == FW.get_blk.call(r) : Wr.Dec<Pr.Blk>}:
  match r:
    case Wr.Got{+k, s}:
      wq.blk_call(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wq.blk_tag(n: Nat, s: String) -> {Work.wk_read_blk.tag(n, s) == FW.get_blk.tag(n, s) : Wr.Dec<Pr.Blk>}:
  match n:
    case 0n:
      wq.blk_ckey(Wr.get_nat(s))
    case 1n:
      wq.blk_rkey(Wr.get_nat(s))
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+q:
      {==}

def wq.blk_go(r: Wr.Dec<Nat>) -> {Work.wk_read_blk.go(r) == FW.get_blk.go(r) : Wr.Dec<Pr.Blk>}:
  match r:
    case Wr.Got{n, s}:
      wq.blk_tag(n, s)
    case Wr.Bad{}:
      {==}

def wq.blk(s: String) -> {Work.wk_read_blk(s) == FW.get_blk(s) : Wr.Dec<Pr.Blk>}:
  wq.blk_go(Wr.get_nat(s))

def wq.blks_go(n: Nat, cur: Wr.Dec<Pr.Blk>) -> {Wr.get_list.go(~Pr.Blk, ~Work.wk_read_blk, n, cur) == Wr.get_list.go(~Pr.Blk, ~FW.get_blk, n, cur) : Wr.Dec<List<&2, Pr.Blk>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %wq.blk(s) : {Wr.get_list.cons(Pr.Blk, x, Wr.get_list.go(~Pr.Blk, ~Work.wk_read_blk, m, Work.wk_read_blk(s))) == Wr.get_list.cons(Pr.Blk, x, Wr.get_list.go(~Pr.Blk, ~FW.get_blk, m, _)) : Wr.Dec<List<&2, Pr.Blk>>}
          Equal.cong(Wr.Dec<List<&2, Pr.Blk>>, Wr.Dec<List<&2, Pr.Blk>>, y => Wr.get_list.cons(Pr.Blk, x, y), Wr.get_list.go(~Pr.Blk, ~Work.wk_read_blk, m, Work.wk_read_blk(s)), Wr.get_list.go(~Pr.Blk, ~FW.get_blk, m, Work.wk_read_blk(s)), wq.blks_go(m, Work.wk_read_blk(s)))
        case Wr.Bad{}:
          {==}

def wq.blks_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Pr.Blk, ~Work.wk_read_blk, r) == Wr.get_list.start(~Pr.Blk, ~FW.get_blk, r) : Wr.Dec<List<&2, Pr.Blk>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %wq.blk(s) : {Wr.get_list.go(~Pr.Blk, ~Work.wk_read_blk, m, Work.wk_read_blk(s)) == Wr.get_list.go(~Pr.Blk, ~FW.get_blk, m, _) : Wr.Dec<List<&2, Pr.Blk>>}
          wq.blks_go(m, Work.wk_read_blk(s))
    case Wr.Bad{}:
      {==}

def wq.blks(+s: String) -> {Wr.get_list(~Pr.Blk, ~Work.wk_read_blk, s) == Wr.get_list(~Pr.Blk, ~FW.get_blk, s) : Wr.Dec<List<&2, Pr.Blk>>}:
  wq.blks_start(Wr.get_nat(s))

def wq.ent_bs(+i: Nat, r: Wr.Dec<List<&2, Pr.Blk>>) -> {Work.wk_read_ent.bs(i, r) == FW.get_ent.bs(i, r) : Wr.Dec<Pr.Ent>}:
  match r:
    case Wr.Got{bs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.ent_go(r: Wr.Dec<Nat>) -> {Work.wk_read_ent.go(r) == FW.get_ent.go(r) : Wr.Dec<Pr.Ent>}:
  match r:
    case Wr.Got{+i, +s}:
      %wq.blks(s) : {Work.wk_read_ent.bs(i, Wr.get_list(~Pr.Blk, ~Work.wk_read_blk, s)) == FW.get_ent.bs(i, _) : Wr.Dec<Pr.Ent>}
      wq.ent_bs(i, Wr.get_list(~Pr.Blk, ~Work.wk_read_blk, s))
    case Wr.Bad{}:
      {==}

def wq.ent(s: String) -> {Work.wk_read_ent(s) == FW.get_ent(s) : Wr.Dec<Pr.Ent>}:
  wq.ent_go(Wr.get_nat(s))

def wq.ents_go(n: Nat, cur: Wr.Dec<Pr.Ent>) -> {Wr.get_list.go(~Pr.Ent, ~Work.wk_read_ent, n, cur) == Wr.get_list.go(~Pr.Ent, ~FW.get_ent, n, cur) : Wr.Dec<List<&2, Pr.Ent>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %wq.ent(s) : {Wr.get_list.cons(Pr.Ent, x, Wr.get_list.go(~Pr.Ent, ~Work.wk_read_ent, m, Work.wk_read_ent(s))) == Wr.get_list.cons(Pr.Ent, x, Wr.get_list.go(~Pr.Ent, ~FW.get_ent, m, _)) : Wr.Dec<List<&2, Pr.Ent>>}
          Equal.cong(Wr.Dec<List<&2, Pr.Ent>>, Wr.Dec<List<&2, Pr.Ent>>, y => Wr.get_list.cons(Pr.Ent, x, y), Wr.get_list.go(~Pr.Ent, ~Work.wk_read_ent, m, Work.wk_read_ent(s)), Wr.get_list.go(~Pr.Ent, ~FW.get_ent, m, Work.wk_read_ent(s)), wq.ents_go(m, Work.wk_read_ent(s)))
        case Wr.Bad{}:
          {==}

def wq.ents_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Pr.Ent, ~Work.wk_read_ent, r) == Wr.get_list.start(~Pr.Ent, ~FW.get_ent, r) : Wr.Dec<List<&2, Pr.Ent>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %wq.ent(s) : {Wr.get_list.go(~Pr.Ent, ~Work.wk_read_ent, m, Work.wk_read_ent(s)) == Wr.get_list.go(~Pr.Ent, ~FW.get_ent, m, _) : Wr.Dec<List<&2, Pr.Ent>>}
          wq.ents_go(m, Work.wk_read_ent(s))
    case Wr.Bad{}:
      {==}

def wq.ents(+s: String) -> {Wr.get_list(~Pr.Ent, ~Work.wk_read_ent, s) == Wr.get_list(~Pr.Ent, ~FW.get_ent, s) : Wr.Dec<List<&2, Pr.Ent>>}:
  wq.ents_start(Wr.get_nat(s))

def wq.at_some(r: Wr.Dec<Nat>) -> {Work.wk_read_at.some(r) == FW.get_at.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.at_tag(n: Nat, s: String) -> {Work.wk_read_at.tag(n, s) == FW.get_at.tag(n, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n:
      wq.at_some(Wr.get_nat(s))
    case 2n+q:
      {==}

def wq.at_go(r: Wr.Dec<Nat>) -> {Work.wk_read_at.go(r) == FW.get_at.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      wq.at_tag(n, s)
    case Wr.Bad{}:
      {==}

def wq.ev_view(at: Maybe<&2, Nat>, r: Wr.Dec<List<&2, Pr.Ent>>) -> {Work.wk_read_ev.view(at, r) == FW.get_ev.view(at, r) : Wr.Dec<Pr.Ev>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.ev_at(r: Wr.Dec<Maybe<&2, Nat>>) -> {Work.wk_read_ev.at(r) == FW.get_ev.at(r) : Wr.Dec<Pr.Ev>}:
  match r:
    case Wr.Got{+at, +s}:
      %wq.ents(s) : {Work.wk_read_ev.view(at, Wr.get_list(~Pr.Ent, ~Work.wk_read_ent, s)) == FW.get_ev.view(at, _) : Wr.Dec<Pr.Ev>}
      wq.ev_view(at, Wr.get_list(~Pr.Ent, ~Work.wk_read_ent, s))
    case Wr.Bad{}:
      {==}

def wq.ev_page(r: Wr.Dec<List<&2, Pr.Ent>>) -> {Work.wk_read_ev.page(r) == FW.get_ev.page(r) : Wr.Dec<Pr.Ev>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.ev_note(r: Wr.Dec<Nat>) -> {Work.wk_read_ev.note(r) == FW.get_ev.note(r) : Wr.Dec<Pr.Ev>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wq.ev_tag(n: Nat, +s: String) -> {Work.wk_read_ev.tag(n, s) == FW.get_ev.tag(n, s) : Wr.Dec<Pr.Ev>}:
  match n:
    case 0n:
      %wq.at_go(Wr.get_nat(s)) : {Work.wk_read_ev.at(Work.wk_read_at.go(Wr.get_nat(s))) == FW.get_ev.at(_) : Wr.Dec<Pr.Ev>}
      wq.ev_at(Work.wk_read_at.go(Wr.get_nat(s)))
    case 1n:
      %wq.ents(s) : {Work.wk_read_ev.page(Wr.get_list(~Pr.Ent, ~Work.wk_read_ent, s)) == FW.get_ev.page(_) : Wr.Dec<Pr.Ev>}
      wq.ev_page(Wr.get_list(~Pr.Ent, ~Work.wk_read_ent, s))
    case 2n:
      wq.ev_note(Wr.get_nat(s))
    case 3n+q:
      {==}

def wq.ev_go(r: Wr.Dec<Nat>) -> {Work.wk_read_ev.go(r) == FW.get_ev.go(r) : Wr.Dec<Pr.Ev>}:
  match r:
    case Wr.Got{n, s}:
      wq.ev_tag(n, s)
    case Wr.Bad{}:
      {==}

# Where the reader finds no whole event, the entry answers its error form
# ----------------------------------------------------------------------

def wme.end(b: Bool, +l: Pr.Led, e: Pr.Ev, no: {Work.wk_read.end(b, e) == None{} : Maybe<&2, Pr.Ev>}) -> {FW.step.end(b, l, e) == (FW.Live{l}, SCon{'E', SCon{' ', "work: malformed event"}}) : FW.St & String}:
  match b:
    case True{}:
      LProgress.pw.some_none(Pr.Ev, e, {FW.step.out(Pr.next(l, e)) == (FW.Live{l}, SCon{'E', SCon{' ', "work: malformed event"}}) : FW.St & String}, no)
    case False{}:
      {==}

def wme.whole(+l: Pr.Led, r: Wr.Dec<Pr.Ev>, no: {Work.wk_read.whole(r) == None{} : Maybe<&2, Pr.Ev>}) -> {FW.step.ev(l, r) == (FW.Live{l}, SCon{'E', SCon{' ', "work: malformed event"}}) : FW.St & String}:
  match r:
    case Wr.Got{e, s}:
      wme.end(Wr.end(s), l, e, no)
    case Wr.Bad{}:
      {==}

def Work.work_entry_malformed_exact(l, s, no):
  %wq.ev_go(Wr.get_nat(s)) : {FW.step.ev(l, _) == (FW.Live{l}, SCon{'E', SCon{' ', "work: malformed event"}}) : FW.St & String}
  wme.whole(l, Work.wk_read_ev.go(Wr.get_nat(s)), no)
