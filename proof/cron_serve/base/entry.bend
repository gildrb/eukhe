# eukhe: lemmas the proofs of the cron_serve entry laws share: the entry
# (bend/ffi_cron_serve.bend) reads every input as the laws' reader does,
# one lemma per stage; the laws' reader reads back every event the laws
# spell; the entry's writers write the laws' spelling; the entry's step is
# ce_entry from every state.

import Base
import ../../../bend/cron.bend as Cr
import ../../../bend/cron_store.bend as CS
import ../../../bend/cron_serve.bend as Sv
import ../../../bend/ffi_cron_serve.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/cron.bend as Cron
import ../../../laws/cron_serve/serve.bend as CronServe
import ../../../laws/cron_serve/entry.bend as CronServeEntry
import ../../base/wire.bend as LWire
import ./read.bend as LCSR
import ./write.bend as LCSW

# The reader, stage by stage
# --------------------------

def pe.jrec_fact(i: Nat, r: Wr.Dec<CS.Fact>) -> {CronServeEntry.ce_read_jrec.fact(i, r) == FC.get_jrec.fact(i, r) : Wr.Dec<Sv.JRec>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.jrec_known(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_jrec.known(r) == FC.get_jrec.known(r) : Wr.Dec<Sv.JRec>}:
  match r:
    case Wr.Got{+i, +s}:
      %LCSR.cre.fact(s) : {CronServeEntry.ce_read_jrec.fact(i, Cron.read_fact(s)) == FC.get_jrec.fact(i, _) : Wr.Dec<Sv.JRec>}
      pe.jrec_fact(i, Cron.read_fact(s))
    case Wr.Bad{}:
      {==}

def pe.jrec_tag(t: Nat, s: String) -> {CronServeEntry.ce_read_jrec.tag(t, s) == FC.get_jrec.tag(t, s) : Wr.Dec<Sv.JRec>}:
  match t:
    case 0n:
      pe.jrec_known(Wr.get_nat(s))
    case 1n:
      {==}
    case 2n+p:
      {==}

def pe.jrec_go(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_jrec.go(r) == FC.get_jrec.go(r) : Wr.Dec<Sv.JRec>}:
  match r:
    case Wr.Got{t, s}:
      pe.jrec_tag(t, s)
    case Wr.Bad{}:
      {==}

def pe.jrec(s: String) -> {CronServeEntry.ce_read_jrec(s) == FC.get_jrec(s) : Wr.Dec<Sv.JRec>}:
  pe.jrec_go(Wr.get_nat(s))

def pe.crec_owner(d: String, j: Nat, r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_crec.owner(d, j, r) == FC.get_crec.owner(d, j, r) : Wr.Dec<Sv.CRec>}:
  match r:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.crec_job(d: String, r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_crec.job(d, r) == FC.get_crec.job(d, r) : Wr.Dec<Sv.CRec>}:
  match r:
    case Wr.Got{j, s}:
      pe.crec_owner(d, j, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pe.crec_known(r: Wr.Dec<String>) -> {CronServeEntry.ce_read_crec.known(r) == FC.get_crec.known(r) : Wr.Dec<Sv.CRec>}:
  match r:
    case Wr.Got{d, s}:
      pe.crec_job(d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pe.crec_tag(t: Nat, s: String) -> {CronServeEntry.ce_read_crec.tag(t, s) == FC.get_crec.tag(t, s) : Wr.Dec<Sv.CRec>}:
  match t:
    case 0n:
      pe.crec_known(Wr.get_str(s))
    case 1n:
      {==}
    case 2n+p:
      {==}

def pe.crec_go(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_crec.go(r) == FC.get_crec.go(r) : Wr.Dec<Sv.CRec>}:
  match r:
    case Wr.Got{t, s}:
      pe.crec_tag(t, s)
    case Wr.Bad{}:
      {==}

def pe.crec(s: String) -> {CronServeEntry.ce_read_crec(s) == FC.get_crec(s) : Wr.Dec<Sv.CRec>}:
  pe.crec_go(Wr.get_nat(s))

def pe.jrecs_go(n: Nat, cur: Wr.Dec<Sv.JRec>) -> {Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, n, cur) == Wr.get_list.go(~Sv.JRec, ~FC.get_jrec, n, cur) : Wr.Dec<List<&2, Sv.JRec>>}:
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
          %pe.jrec(s) : {Wr.get_list.cons(Sv.JRec, x, Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, m, CronServeEntry.ce_read_jrec(s))) == Wr.get_list.cons(Sv.JRec, x, Wr.get_list.go(~Sv.JRec, ~FC.get_jrec, m, _)) : Wr.Dec<List<&2, Sv.JRec>>}
          Equal.cong(Wr.Dec<List<&2, Sv.JRec>>, Wr.Dec<List<&2, Sv.JRec>>, y => Wr.get_list.cons(Sv.JRec, x, y), Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, m, CronServeEntry.ce_read_jrec(s)), Wr.get_list.go(~Sv.JRec, ~FC.get_jrec, m, CronServeEntry.ce_read_jrec(s)), pe.jrecs_go(m, CronServeEntry.ce_read_jrec(s)))
        case Wr.Bad{}:
          {==}

def pe.jrecs_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sv.JRec, ~CronServeEntry.ce_read_jrec, r) == Wr.get_list.start(~Sv.JRec, ~FC.get_jrec, r) : Wr.Dec<List<&2, Sv.JRec>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %pe.jrec(s) : {Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, m, CronServeEntry.ce_read_jrec(s)) == Wr.get_list.go(~Sv.JRec, ~FC.get_jrec, m, _) : Wr.Dec<List<&2, Sv.JRec>>}
          pe.jrecs_go(m, CronServeEntry.ce_read_jrec(s))
    case Wr.Bad{}:
      {==}

def pe.jrecs(+s: String) -> {Wr.get_list(~Sv.JRec, ~CronServeEntry.ce_read_jrec, s) == Wr.get_list(~Sv.JRec, ~FC.get_jrec, s) : Wr.Dec<List<&2, Sv.JRec>>}:
  pe.jrecs_start(Wr.get_nat(s))

def pe.crecs_go(n: Nat, cur: Wr.Dec<Sv.CRec>) -> {Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, n, cur) == Wr.get_list.go(~Sv.CRec, ~FC.get_crec, n, cur) : Wr.Dec<List<&2, Sv.CRec>>}:
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
          %pe.crec(s) : {Wr.get_list.cons(Sv.CRec, x, Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, m, CronServeEntry.ce_read_crec(s))) == Wr.get_list.cons(Sv.CRec, x, Wr.get_list.go(~Sv.CRec, ~FC.get_crec, m, _)) : Wr.Dec<List<&2, Sv.CRec>>}
          Equal.cong(Wr.Dec<List<&2, Sv.CRec>>, Wr.Dec<List<&2, Sv.CRec>>, y => Wr.get_list.cons(Sv.CRec, x, y), Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, m, CronServeEntry.ce_read_crec(s)), Wr.get_list.go(~Sv.CRec, ~FC.get_crec, m, CronServeEntry.ce_read_crec(s)), pe.crecs_go(m, CronServeEntry.ce_read_crec(s)))
        case Wr.Bad{}:
          {==}

def pe.crecs_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sv.CRec, ~CronServeEntry.ce_read_crec, r) == Wr.get_list.start(~Sv.CRec, ~FC.get_crec, r) : Wr.Dec<List<&2, Sv.CRec>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %pe.crec(s) : {Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, m, CronServeEntry.ce_read_crec(s)) == Wr.get_list.go(~Sv.CRec, ~FC.get_crec, m, _) : Wr.Dec<List<&2, Sv.CRec>>}
          pe.crecs_go(m, CronServeEntry.ce_read_crec(s))
    case Wr.Bad{}:
      {==}

def pe.crecs(+s: String) -> {Wr.get_list(~Sv.CRec, ~CronServeEntry.ce_read_crec, s) == Wr.get_list(~Sv.CRec, ~FC.get_crec, s) : Wr.Dec<List<&2, Sv.CRec>>}:
  pe.crecs_start(Wr.get_nat(s))

def pe.disk_claims(js: List<&2, Sv.JRec>, r: Wr.Dec<List<&2, Sv.CRec>>) -> {CronServeEntry.ce_read_disk.claims(js, r) == FC.get_disk.claims(js, r) : Wr.Dec<Sv.Disk>}:
  match r:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.disk_jobs(r: Wr.Dec<List<&2, Sv.JRec>>) -> {CronServeEntry.ce_read_disk.jobs(r) == FC.get_disk.jobs(r) : Wr.Dec<Sv.Disk>}:
  match r:
    case Wr.Got{+js, +s}:
      %pe.crecs(s) : {CronServeEntry.ce_read_disk.claims(js, Wr.get_list(~Sv.CRec, ~CronServeEntry.ce_read_crec, s)) == FC.get_disk.claims(js, _) : Wr.Dec<Sv.Disk>}
      pe.disk_claims(js, Wr.get_list(~Sv.CRec, ~CronServeEntry.ce_read_crec, s))
    case Wr.Bad{}:
      {==}

def pe.disk_tag(t: Nat, +s: String) -> {CronServeEntry.ce_read_disk.tag(t, s) == FC.get_disk.tag(t, s) : Wr.Dec<Sv.Disk>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      %pe.jrecs(s) : {CronServeEntry.ce_read_disk.jobs(Wr.get_list(~Sv.JRec, ~CronServeEntry.ce_read_jrec, s)) == FC.get_disk.jobs(_) : Wr.Dec<Sv.Disk>}
      pe.disk_jobs(Wr.get_list(~Sv.JRec, ~CronServeEntry.ce_read_jrec, s))
    case 3n+p:
      {==}

def pe.disk(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_disk(r) == FC.get_disk(r) : Wr.Dec<Sv.Disk>}:
  match r:
    case Wr.Got{t, s}:
      pe.disk_tag(t, s)
    case Wr.Bad{}:
      {==}

def pe.op_fresh(d: Nat, n: Nat, r: Wr.Dec<List<&2, String>>) -> {CronServeEntry.ce_read_op.fresh(d, n, r) == FC.get_claim.fresh(d, n, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_now(d: Nat, r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.now(d, r) == FC.get_claim.now(d, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{n, s}:
      pe.op_fresh(d, n, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      {==}

def pe.op_claim(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.claim(r) == FC.get_claim(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{d, s}:
      pe.op_now(d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pe.op_recover(r: Wr.Dec<List<&2, Nat>>) -> {CronServeEntry.ce_read_op.recover(r) == FC.get_recover(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_at(d: String, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.at(d, a, b, r) == FC.get_finish.now(d, a, b, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_failed(d: String, a: Bool, r: Wr.Dec<Bool>) -> {CronServeEntry.ce_read_op.failed(d, a, r) == FC.get_finish.failed(d, a, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{b, s}:
      pe.op_at(d, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pe.op_ran(d: String, r: Wr.Dec<Bool>) -> {CronServeEntry.ce_read_op.ran(d, r) == FC.get_finish.ran(d, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{a, s}:
      pe.op_failed(d, a, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def pe.op_finish(r: Wr.Dec<String>) -> {CronServeEntry.ce_read_op.finish(r) == FC.get_finish(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{d, s}:
      pe.op_ran(d, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def pe.op_cancel(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.cancel(r) == FC.get_cancel(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_when(n: Nat, r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.when(n, r) == FC.get_resume.now(n, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_resume(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.resume(r) == FC.get_resume(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{n, s}:
      pe.op_when(n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pe.op_made(n: Nat, r: Wr.Dec<CS.Fact>) -> {CronServeEntry.ce_read_op.made(n, r) == FC.get_create.fact(n, r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.op_create(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op.create(r) == FC.get_create(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{+n, +s}:
      %LCSR.cre.fact(s) : {CronServeEntry.ce_read_op.made(n, Cron.read_fact(s)) == FC.get_create.fact(n, _) : Wr.Dec<Sv.Op>}
      pe.op_made(n, Cron.read_fact(s))
    case Wr.Bad{}:
      {==}

def pe.op_tag(t: Nat, s: String) -> {CronServeEntry.ce_read_op.tag(t, s) == FC.get_op.tag(t, s) : Wr.Dec<Sv.Op>}:
  match t:
    case 0n:
      pe.op_claim(Wr.get_nat(s))
    case 1n:
      pe.op_recover(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      pe.op_finish(Wr.get_str(s))
    case 3n:
      pe.op_cancel(Wr.get_nat(s))
    case 4n:
      pe.op_resume(Wr.get_nat(s))
    case 5n:
      pe.op_create(Wr.get_nat(s))
    case 6n+p:
      {==}

def pe.op(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_op(r) == FC.get_op(r) : Wr.Dec<Sv.Op>}:
  match r:
    case Wr.Got{t, s}:
      pe.op_tag(t, s)
    case Wr.Bad{}:
      {==}

def pe.ev_op(me: Nat, k: Sv.Disk, r: Wr.Dec<Sv.Op>) -> {CronServeEntry.ce_read_ev.op(me, k, r) == FC.get_serve.op(me, k, r) : Wr.Dec<FC.Ev>}:
  match r:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.ev_disk(+me: Nat, r: Wr.Dec<Sv.Disk>) -> {CronServeEntry.ce_read_ev.disk(me, r) == FC.get_serve.disk(me, r) : Wr.Dec<FC.Ev>}:
  match r:
    case Wr.Got{+k, +s}:
      %pe.op(Wr.get_nat(s)) : {CronServeEntry.ce_read_ev.op(me, k, CronServeEntry.ce_read_op(Wr.get_nat(s))) == FC.get_serve.op(me, k, _) : Wr.Dec<FC.Ev>}
      pe.ev_op(me, k, CronServeEntry.ce_read_op(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pe.ev_serve(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_ev.serve(r) == FC.get_serve(r) : Wr.Dec<FC.Ev>}:
  match r:
    case Wr.Got{+me, +s}:
      %pe.disk(Wr.get_nat(s)) : {CronServeEntry.ce_read_ev.disk(me, CronServeEntry.ce_read_disk(Wr.get_nat(s))) == FC.get_serve.disk(me, _) : Wr.Dec<FC.Ev>}
      pe.ev_disk(me, CronServeEntry.ce_read_disk(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pe.ev_end(r: Wr.Dec<String>) -> {CronServeEntry.ce_read_ev.end(r) == FC.get_end(r) : Wr.Dec<FC.Ev>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pe.ev_tag(t: Nat, s: String) -> {CronServeEntry.ce_read_ev.tag(t, s) == FC.get_ev.tag(t, s) : Wr.Dec<FC.Ev>}:
  match t:
    case 0n:
      pe.ev_serve(Wr.get_nat(s))
    case 1n:
      pe.ev_end(Wr.get_str(s))
    case 2n+p:
      {==}

# the entry reads every event as the laws' reader does
def pe.ev(r: Wr.Dec<Nat>) -> {CronServeEntry.ce_read_ev.go(r) == FC.get_ev(r) : Wr.Dec<FC.Ev>}:
  match r:
    case Wr.Got{t, s}:
      pe.ev_tag(t, s)
    case Wr.Bad{}:
      {==}

# The writers
# -----------

def pe.jout(o: Sv.JOut, +rest: String) -> {FC.put_jout(o, rest) == CronServeEntry.ce_spell_jout(o, rest) : String}:
  match o:
    case Sv.JSame{}:
      {==}
    case Sv.JTook{+t}:
      %LCSW.crw.took(t, rest) : {Wr.put_nat(1n, FC.put_took(t, rest)) == Wr.put_nat(1n, _) : String}
      {==}
    case Sv.JBack{+b}:
      %LCSW.crw.back(b, rest) : {Wr.put_nat(2n, FC.put_back(b, rest)) == Wr.put_nat(2n, _) : String}
      {==}
    case Sv.JFin{+x}:
      %LCSW.crw.fin(x, rest) : {Wr.put_nat(3n, FC.put_fin(x, rest)) == Wr.put_nat(3n, _) : String}
      {==}
    case Sv.JCut{+x}:
      %LCSW.crw.cut(x, rest) : {Wr.put_nat(4n, FC.put_cut(x, rest)) == Wr.put_nat(4n, _) : String}
      {==}
    case Sv.JAgain{+x}:
      %LCSW.crw.again(x, rest) : {Wr.put_nat(5n, FC.put_again(x, rest)) == Wr.put_nat(5n, _) : String}
      {==}
    case Sv.JNew{}:
      {==}

def pe.jouts_go(xs: List<&2, Sv.JOut>, +rest: String) -> {Wr.put_list.go(~Sv.JOut, ~FC.put_jout, xs, rest) == (List.length(&2, Sv.JOut, xs), CronServeEntry.ce_spell_jouts(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sv.JOut, ~FC.put_jout, t, rest), (List.length(&2, Sv.JOut, t), CronServeEntry.ce_spell_jouts(t, rest)), pe.jouts_go(t, rest)) : {Wr.put_list.step(~Sv.JOut, ~FC.put_jout, x, _) == (1n+List.length(&2, Sv.JOut, t), CronServeEntry.ce_spell_jout(x, CronServeEntry.ce_spell_jouts(t, rest))) : Nat & String}
      %pe.jout(x, CronServeEntry.ce_spell_jouts(t, rest)) : {(1n+List.length(&2, Sv.JOut, t), FC.put_jout(x, CronServeEntry.ce_spell_jouts(t, rest))) == (1n+List.length(&2, Sv.JOut, t), _) : Nat & String}
      {==}

def pe.jouts(+xs: List<&2, Sv.JOut>, +rest: String) -> {Wr.put_list(~Sv.JOut, ~FC.put_jout, xs, rest) == Wr.put_nat(List.length(&2, Sv.JOut, xs), CronServeEntry.ce_spell_jouts(xs, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Sv.JOut, ~FC.put_jout, xs, rest), (List.length(&2, Sv.JOut, xs), CronServeEntry.ce_spell_jouts(xs, rest)), pe.jouts_go(xs, rest))

def pe.cout(o: Sv.COut, rest: String) -> {FC.put_cout(o, rest) == CronServeEntry.ce_spell_cout(o, rest) : String}:
  match o:
    case Sv.CKeep{}:
      {==}
    case Sv.CDrop{}:
      {==}
    case Sv.CNew{k, d}:
      {==}

def pe.couts_go(xs: List<&2, Sv.COut>, +rest: String) -> {Wr.put_list.go(~Sv.COut, ~FC.put_cout, xs, rest) == (List.length(&2, Sv.COut, xs), CronServeEntry.ce_spell_couts(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sv.COut, ~FC.put_cout, t, rest), (List.length(&2, Sv.COut, t), CronServeEntry.ce_spell_couts(t, rest)), pe.couts_go(t, rest)) : {Wr.put_list.step(~Sv.COut, ~FC.put_cout, x, _) == (1n+List.length(&2, Sv.COut, t), CronServeEntry.ce_spell_cout(x, CronServeEntry.ce_spell_couts(t, rest))) : Nat & String}
      %pe.cout(x, CronServeEntry.ce_spell_couts(t, rest)) : {(1n+List.length(&2, Sv.COut, t), FC.put_cout(x, CronServeEntry.ce_spell_couts(t, rest))) == (1n+List.length(&2, Sv.COut, t), _) : Nat & String}
      {==}

def pe.couts(+xs: List<&2, Sv.COut>, +rest: String) -> {Wr.put_list(~Sv.COut, ~FC.put_cout, xs, rest) == Wr.put_nat(List.length(&2, Sv.COut, xs), CronServeEntry.ce_spell_couts(xs, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~Sv.COut, ~FC.put_cout, xs, rest), (List.length(&2, Sv.COut, xs), CronServeEntry.ce_spell_couts(xs, rest)), pe.couts_go(xs, rest))

# the entry writes the laws' spelling of every answer
def pe.out(o: Sv.Out) -> {FC.put_out(o) == CronServeEntry.ce_spell_out(o) : String}:
  match o:
    case Sv.Out{+a, +w, +js, +cs}:
      %pe.couts(cs, "") : {FC.put_out(Sv.Out{a, w, js, cs}) == Wr.put_bool(a, Wr.put_bool(w, Wr.put_nat(List.length(&2, Sv.JOut, js), CronServeEntry.ce_spell_jouts(js, _)))) : String}
      %pe.jouts(js, Wr.put_list(~Sv.COut, ~FC.put_cout, cs, "")) : {FC.put_out(Sv.Out{a, w, js, cs}) == Wr.put_bool(a, Wr.put_bool(w, _)) : String}
      {==}

# The step, from every state
# --------------------------

def pe.put(r: Sv.Served) -> {FC.step.put(r) == CronServeEntry.ce_served(r) : FC.St & String}:
  match r:
    case Sv.Served{+runs, +o}:
      %pe.out(o) : {(FC.Open{runs}, FC.put_out(o)) == (FC.Open{runs}, _) : FC.St & String}
      {==}

def pe.run(+runs: List<&2, String>, e: FC.Ev) -> {FC.step.run(runs, e) == CronServeEntry.ce_entry.run(runs, e) : FC.St & String}:
  match e:
    case FC.EServe{+me, +k, +o}:
      pe.put(Sv.serve(runs, me, k, o))
    case FC.EEnd{d}:
      {==}

def pe.fin(b: Bool, +runs: List<&2, String>, +x: FC.Ev) -> {FC.step.fin(b, runs, x) == CronServeEntry.ce_entry.at(runs, CronServeEntry.ce_whole(FC.Ev, b, x)) : FC.St & String}:
  match b:
    case True{}:
      pe.run(runs, x)
    case False{}:
      {==}

def pe.go(r: Wr.Dec<FC.Ev>, +runs: List<&2, String>) -> {FC.step.go(runs, r) == CronServeEntry.ce_entry.at(runs, CronServeEntry.ce_read_ev.whole(r)) : FC.St & String}:
  match r:
    case Wr.Got{x, s}:
      pe.fin(Wr.end(s), runs, x)
    case Wr.Bad{}:
      {==}

# the entry's step is ce_entry, from every state and for every input
def pe.entry(st: FC.St, +s: String) -> {FC.step(st, s) == CronServeEntry.ce_entry(st, s) : FC.St & String}:
  match st:
    case FC.Open{+runs}:
      %pe.ev(Wr.get_nat(s)) : {FC.step.go(runs, _) == CronServeEntry.ce_entry.at(runs, CronServeEntry.ce_read_ev(s)) : FC.St & String}
      pe.go(CronServeEntry.ce_read_ev.go(Wr.get_nat(s)), runs)
    case FC.Shut{}:
      {==}

# the code's step is the spec's on every event (cron_serve_exact,
# cron_serve_end_exact)
def pe.run_step(+runs: List<&2, String>, e: FC.Ev) -> {CronServeEntry.ce_entry.run(runs, e) == CronServeEntry.ce_step(runs, e) : FC.St & String}:
  match e:
    case FC.EServe{+me, +k, +o}:
      %CronServe.cron_serve_exact(runs, me, k, o) : {CronServeEntry.ce_served(Sv.serve(runs, me, k, o)) == CronServeEntry.ce_served(_) : FC.St & String}
      {==}
    case FC.EEnd{+d}:
      %CronServe.cron_serve_end_exact(d, runs) : {(FC.Open{Sv.end(d, runs)}, "") == (FC.Open{_}, "") : FC.St & String}
      {==}

def pe.at_some(+runs: List<&2, String>, m: Maybe<&2, FC.Ev>, +e: FC.Ev, got: {m == Some{e} : Maybe<&2, FC.Ev>}) -> {CronServeEntry.ce_entry.at(runs, m) == CronServeEntry.ce_step(runs, e) : FC.St & String}:
  %Equal.sym(Maybe<&2, FC.Ev>, m, Some{e}, got) : {CronServeEntry.ce_entry.at(runs, _) == CronServeEntry.ce_step(runs, e) : FC.St & String}
  pe.run_step(runs, e)

def pe.at_none(+runs: List<&2, String>, m: Maybe<&2, FC.Ev>, no: {m == None{} : Maybe<&2, FC.Ev>}) -> {CronServeEntry.ce_entry.at(runs, m) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}:
  %Equal.sym(Maybe<&2, FC.Ev>, m, None{}, no) : {CronServeEntry.ce_entry.at(runs, _) == (FC.Open{runs}, CronServeEntry.ce_err_event()) : FC.St & String}
  {==}

# a whole event steps the runs as the spec
def pe.step_reads(+runs: List<&2, String>, +s: String, +e: FC.Ev, got: {CronServeEntry.ce_read_ev(s) == Some{e} : Maybe<&2, FC.Ev>}) -> {FC.step(FC.Open{runs}, s) == CronServeEntry.ce_step(runs, e) : FC.St & String}:
  Equal.trans(FC.St & String, FC.step(FC.Open{runs}, s), CronServeEntry.ce_entry.at(runs, CronServeEntry.ce_read_ev(s)), CronServeEntry.ce_step(runs, e), pe.entry(FC.Open{runs}, s), pe.at_some(runs, CronServeEntry.ce_read_ev(s), e, got))

# Reading back what the laws spell
# --------------------------------

def pe.fact_rt(+f: CS.Fact, +rest: String, +h: {Cron.fact_fits(f) == True{} : Bool}) -> {Wr.Got{f, rest} == Cron.read_fact(Cron.spell_fact(f, rest)) : Wr.Dec<CS.Fact>}:
  Equal.trans(Wr.Dec<CS.Fact>, Wr.Got{f, rest}, FC.get_fact(Cron.spell_fact(f, rest)), Cron.read_fact(Cron.spell_fact(f, rest)), LCSR.crr.fact(f, rest, h), Equal.sym(Wr.Dec<CS.Fact>, Cron.read_fact(Cron.spell_fact(f, rest)), FC.get_fact(Cron.spell_fact(f, rest)), LCSR.cre.fact(Cron.spell_fact(f, rest))))

def pe.str_rt(+d: String, +rest: String, h: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}) -> {Wr.Got{d, rest} == Wr.get_str(Wr.put_str(d, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(d, rest)), Wr.Got{d, rest}, Wire.wire_str_round_trip(d, rest, h))

def pe.jrec_rt(r: Sv.JRec, +rest: String, +h: {CronServeEntry.ce_jrec_fits(r) == True{} : Bool}) -> {CronServeEntry.ce_read_jrec(CronServeEntry.ce_spell_jrec(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Sv.JRec>}:
  match r:
    case Sv.JKnown{+i, +f}:
      %LWire.pw6.nat(0n, Wr.put_nat(i, Cron.spell_fact(f, rest)), {==}) : {CronServeEntry.ce_read_jrec.go(_) == Wr.Got{Sv.JKnown{i, f}, rest} : Wr.Dec<Sv.JRec>}
      %LWire.pw6.nat(i, Cron.spell_fact(f, rest), LCSR.cre.and_l(LawsBase.wire_fits(i), Cron.fact_fits(f), h)) : {CronServeEntry.ce_read_jrec.known(_) == Wr.Got{Sv.JKnown{i, f}, rest} : Wr.Dec<Sv.JRec>}
      %pe.fact_rt(f, rest, LCSR.cre.and_r(LawsBase.wire_fits(i), Cron.fact_fits(f), h)) : {CronServeEntry.ce_read_jrec.fact(i, _) == Wr.Got{Sv.JKnown{i, f}, rest} : Wr.Dec<Sv.JRec>}
      {==}
    case Sv.JRaw{}:
      %LWire.pw6.nat(1n, rest, {==}) : {CronServeEntry.ce_read_jrec.go(_) == Wr.Got{Sv.JRaw{}, rest} : Wr.Dec<Sv.JRec>}
      {==}

def pe.crec_rt(c: Sv.CRec, +rest: String, +h: {CronServeEntry.ce_crec_fits(c) == True{} : Bool}) -> {CronServeEntry.ce_read_crec(CronServeEntry.ce_spell_crec(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Sv.CRec>}:
  match c:
    case Sv.CKnown{+d, +j, +o}:
      +h2 = LCSR.cre.and_r(CronServeEntry.ce_str_fits(d), Bool.and(LawsBase.wire_fits(j), LawsBase.wire_fits(o)), h)
      %LWire.pw6.nat(0n, Wr.put_str(d, Wr.put_nat(j, Wr.put_nat(o, rest))), {==}) : {CronServeEntry.ce_read_crec.go(_) == Wr.Got{Sv.CKnown{d, j, o}, rest} : Wr.Dec<Sv.CRec>}
      %pe.str_rt(d, Wr.put_nat(j, Wr.put_nat(o, rest)), LCSR.cre.and_l(CronServeEntry.ce_str_fits(d), Bool.and(LawsBase.wire_fits(j), LawsBase.wire_fits(o)), h)) : {CronServeEntry.ce_read_crec.known(_) == Wr.Got{Sv.CKnown{d, j, o}, rest} : Wr.Dec<Sv.CRec>}
      %LWire.pw6.nat(j, Wr.put_nat(o, rest), LCSR.cre.and_l(LawsBase.wire_fits(j), LawsBase.wire_fits(o), h2)) : {CronServeEntry.ce_read_crec.job(d, _) == Wr.Got{Sv.CKnown{d, j, o}, rest} : Wr.Dec<Sv.CRec>}
      %LWire.pw6.nat(o, rest, LCSR.cre.and_r(LawsBase.wire_fits(j), LawsBase.wire_fits(o), h2)) : {CronServeEntry.ce_read_crec.owner(d, j, _) == Wr.Got{Sv.CKnown{d, j, o}, rest} : Wr.Dec<Sv.CRec>}
      {==}
    case Sv.CRaw{}:
      %LWire.pw6.nat(1n, rest, {==}) : {CronServeEntry.ce_read_crec.go(_) == Wr.Got{Sv.CRaw{}, rest} : Wr.Dec<Sv.CRec>}
      {==}

def pe.jl_go(xs: List<&2, Sv.JRec>, +x: Sv.JRec, +rest: String, +hf: {CronServeEntry.ce_jrecs_fit(x <> xs) == True{} : Bool}) -> {Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, List.length(&2, Sv.JRec, xs), CronServeEntry.ce_read_jrec(CronServeEntry.ce_spell_jrec(x, CronServeEntry.ce_spell_jrecs(xs, rest)))) == Wr.Got{x <> xs, rest} : Wr.Dec<List<&2, Sv.JRec>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sv.JRec>, CronServeEntry.ce_read_jrec(CronServeEntry.ce_spell_jrec(x, rest)), Wr.Got{x, rest}, pe.jrec_rt(x, rest, LCSR.cre.and_l(CronServeEntry.ce_jrec_fits(x), True{}, hf))) : {Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sv.JRec>>}
      {==}
    case +x2 <> +xs2:
      +hr = LCSR.cre.and_r(CronServeEntry.ce_jrec_fits(x), CronServeEntry.ce_jrecs_fit(x2 <> xs2), hf)
      %Equal.sym(Wr.Dec<Sv.JRec>, CronServeEntry.ce_read_jrec(CronServeEntry.ce_spell_jrec(x, CronServeEntry.ce_spell_jrecs(x2 <> xs2, rest))), Wr.Got{x, CronServeEntry.ce_spell_jrecs(x2 <> xs2, rest)}, pe.jrec_rt(x, CronServeEntry.ce_spell_jrecs(x2 <> xs2, rest), LCSR.cre.and_l(CronServeEntry.ce_jrec_fits(x), CronServeEntry.ce_jrecs_fit(x2 <> xs2), hf))) : {Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, 1n+List.length(&2, Sv.JRec, xs2), _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Sv.JRec>>}
      %Equal.sym(Wr.Dec<List<&2, Sv.JRec>>, Wr.get_list.go(~Sv.JRec, ~CronServeEntry.ce_read_jrec, List.length(&2, Sv.JRec, xs2), CronServeEntry.ce_read_jrec(CronServeEntry.ce_spell_jrec(x2, CronServeEntry.ce_spell_jrecs(xs2, rest)))), Wr.Got{x2 <> xs2, rest}, pe.jl_go(xs2, x2, rest, hr)) : {Wr.get_list.cons(Sv.JRec, x, _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Sv.JRec>>}
      {==}

def pe.jl_start(xs: List<&2, Sv.JRec>, +rest: String, +hf: {CronServeEntry.ce_jrecs_fit(xs) == True{} : Bool}) -> {Wr.get_list.start(~Sv.JRec, ~CronServeEntry.ce_read_jrec, Wr.Got{List.length(&2, Sv.JRec, xs), CronServeEntry.ce_spell_jrecs(xs, rest)}) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sv.JRec>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      pe.jl_go(t, x, rest, hf)

def pe.jl_rt(+xs: List<&2, Sv.JRec>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Sv.JRec, xs)) == True{} : Bool}, +hf: {CronServeEntry.ce_jrecs_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Sv.JRec, ~CronServeEntry.ce_read_jrec, Wr.put_nat(List.length(&2, Sv.JRec, xs), CronServeEntry.ce_spell_jrecs(xs, rest))) : Wr.Dec<List<&2, Sv.JRec>>}:
  %LWire.pw6.nat(List.length(&2, Sv.JRec, xs), CronServeEntry.ce_spell_jrecs(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Sv.JRec, ~CronServeEntry.ce_read_jrec, _) : Wr.Dec<List<&2, Sv.JRec>>}
  Equal.sym(Wr.Dec<List<&2, Sv.JRec>>, Wr.get_list.start(~Sv.JRec, ~CronServeEntry.ce_read_jrec, Wr.Got{List.length(&2, Sv.JRec, xs), CronServeEntry.ce_spell_jrecs(xs, rest)}), Wr.Got{xs, rest}, pe.jl_start(xs, rest, hf))

def pe.cl_go(xs: List<&2, Sv.CRec>, +x: Sv.CRec, +rest: String, +hf: {CronServeEntry.ce_crecs_fit(x <> xs) == True{} : Bool}) -> {Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, List.length(&2, Sv.CRec, xs), CronServeEntry.ce_read_crec(CronServeEntry.ce_spell_crec(x, CronServeEntry.ce_spell_crecs(xs, rest)))) == Wr.Got{x <> xs, rest} : Wr.Dec<List<&2, Sv.CRec>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Sv.CRec>, CronServeEntry.ce_read_crec(CronServeEntry.ce_spell_crec(x, rest)), Wr.Got{x, rest}, pe.crec_rt(x, rest, LCSR.cre.and_l(CronServeEntry.ce_crec_fits(x), True{}, hf))) : {Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Sv.CRec>>}
      {==}
    case +x2 <> +xs2:
      +hr = LCSR.cre.and_r(CronServeEntry.ce_crec_fits(x), CronServeEntry.ce_crecs_fit(x2 <> xs2), hf)
      %Equal.sym(Wr.Dec<Sv.CRec>, CronServeEntry.ce_read_crec(CronServeEntry.ce_spell_crec(x, CronServeEntry.ce_spell_crecs(x2 <> xs2, rest))), Wr.Got{x, CronServeEntry.ce_spell_crecs(x2 <> xs2, rest)}, pe.crec_rt(x, CronServeEntry.ce_spell_crecs(x2 <> xs2, rest), LCSR.cre.and_l(CronServeEntry.ce_crec_fits(x), CronServeEntry.ce_crecs_fit(x2 <> xs2), hf))) : {Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, 1n+List.length(&2, Sv.CRec, xs2), _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Sv.CRec>>}
      %Equal.sym(Wr.Dec<List<&2, Sv.CRec>>, Wr.get_list.go(~Sv.CRec, ~CronServeEntry.ce_read_crec, List.length(&2, Sv.CRec, xs2), CronServeEntry.ce_read_crec(CronServeEntry.ce_spell_crec(x2, CronServeEntry.ce_spell_crecs(xs2, rest)))), Wr.Got{x2 <> xs2, rest}, pe.cl_go(xs2, x2, rest, hr)) : {Wr.get_list.cons(Sv.CRec, x, _) == Wr.Got{x <> x2 <> xs2, rest} : Wr.Dec<List<&2, Sv.CRec>>}
      {==}

def pe.cl_start(xs: List<&2, Sv.CRec>, +rest: String, +hf: {CronServeEntry.ce_crecs_fit(xs) == True{} : Bool}) -> {Wr.get_list.start(~Sv.CRec, ~CronServeEntry.ce_read_crec, Wr.Got{List.length(&2, Sv.CRec, xs), CronServeEntry.ce_spell_crecs(xs, rest)}) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Sv.CRec>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      pe.cl_go(t, x, rest, hf)

def pe.cl_rt(+xs: List<&2, Sv.CRec>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Sv.CRec, xs)) == True{} : Bool}, +hf: {CronServeEntry.ce_crecs_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Sv.CRec, ~CronServeEntry.ce_read_crec, Wr.put_nat(List.length(&2, Sv.CRec, xs), CronServeEntry.ce_spell_crecs(xs, rest))) : Wr.Dec<List<&2, Sv.CRec>>}:
  %LWire.pw6.nat(List.length(&2, Sv.CRec, xs), CronServeEntry.ce_spell_crecs(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Sv.CRec, ~CronServeEntry.ce_read_crec, _) : Wr.Dec<List<&2, Sv.CRec>>}
  Equal.sym(Wr.Dec<List<&2, Sv.CRec>>, Wr.get_list.start(~Sv.CRec, ~CronServeEntry.ce_read_crec, Wr.Got{List.length(&2, Sv.CRec, xs), CronServeEntry.ce_spell_crecs(xs, rest)}), Wr.Got{xs, rest}, pe.cl_start(xs, rest, hf))

def pe.disk_rt(k: Sv.Disk, +rest: String, +h: {CronServeEntry.ce_disk_fits(k) == True{} : Bool}) -> {CronServeEntry.ce_read_disk(Wr.get_nat(CronServeEntry.ce_spell_disk(k, rest))) == Wr.Got{k, rest} : Wr.Dec<Sv.Disk>}:
  match k:
    case Sv.Missing{}:
      %LWire.pw6.nat(0n, rest, {==}) : {CronServeEntry.ce_read_disk(_) == Wr.Got{Sv.Missing{}, rest} : Wr.Dec<Sv.Disk>}
      {==}
    case Sv.Torn{}:
      %LWire.pw6.nat(1n, rest, {==}) : {CronServeEntry.ce_read_disk(_) == Wr.Got{Sv.Torn{}, rest} : Wr.Dec<Sv.Disk>}
      {==}
    case Sv.Parsed{+js, +cs}:
      +hj = LCSR.cre.and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Sv.JRec, js)), CronServeEntry.ce_jrecs_fit(js)), Bool.and(LawsBase.wire_fits(List.length(&2, Sv.CRec, cs)), CronServeEntry.ce_crecs_fit(cs)), h)
      +hc = LCSR.cre.and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Sv.JRec, js)), CronServeEntry.ce_jrecs_fit(js)), Bool.and(LawsBase.wire_fits(List.length(&2, Sv.CRec, cs)), CronServeEntry.ce_crecs_fit(cs)), h)
      +mid = Wr.put_nat(List.length(&2, Sv.CRec, cs), CronServeEntry.ce_spell_crecs(cs, rest))
      %LWire.pw6.nat(2n, Wr.put_nat(List.length(&2, Sv.JRec, js), CronServeEntry.ce_spell_jrecs(js, mid)), {==}) : {CronServeEntry.ce_read_disk(_) == Wr.Got{Sv.Parsed{js, cs}, rest} : Wr.Dec<Sv.Disk>}
      %pe.jl_rt(js, mid, LCSR.cre.and_l(LawsBase.wire_fits(List.length(&2, Sv.JRec, js)), CronServeEntry.ce_jrecs_fit(js), hj), LCSR.cre.and_r(LawsBase.wire_fits(List.length(&2, Sv.JRec, js)), CronServeEntry.ce_jrecs_fit(js), hj)) : {CronServeEntry.ce_read_disk.jobs(_) == Wr.Got{Sv.Parsed{js, cs}, rest} : Wr.Dec<Sv.Disk>}
      %pe.cl_rt(cs, rest, LCSR.cre.and_l(LawsBase.wire_fits(List.length(&2, Sv.CRec, cs)), CronServeEntry.ce_crecs_fit(cs), hc), LCSR.cre.and_r(LawsBase.wire_fits(List.length(&2, Sv.CRec, cs)), CronServeEntry.ce_crecs_fit(cs), hc)) : {CronServeEntry.ce_read_disk.claims(js, _) == Wr.Got{Sv.Parsed{js, cs}, rest} : Wr.Dec<Sv.Disk>}
      {==}

def pe.op_rt(op: Sv.Op, +rest: String, +h: {CronServeEntry.ce_op_fits(op) == True{} : Bool}) -> {CronServeEntry.ce_read_op(Wr.get_nat(CronServeEntry.ce_spell_op(op, rest))) == Wr.Got{op, rest} : Wr.Dec<Sv.Op>}:
  match op:
    case Sv.OClaim{+due, +now, +fresh}:
      +hn = LCSR.cre.and_l(Bool.and(LawsBase.wire_fits(due), LawsBase.wire_fits(now)), LawsBase.wire_strs_fit(fresh), h)
      %LWire.pw6.nat(0n, Wr.put_nat(due, Wr.put_nat(now, LawsBase.wire_spell_strs(fresh, rest))), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.OClaim{due, now, fresh}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(due, Wr.put_nat(now, LawsBase.wire_spell_strs(fresh, rest)), LCSR.cre.and_l(LawsBase.wire_fits(due), LawsBase.wire_fits(now), hn)) : {CronServeEntry.ce_read_op.claim(_) == Wr.Got{Sv.OClaim{due, now, fresh}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(now, LawsBase.wire_spell_strs(fresh, rest), LCSR.cre.and_r(LawsBase.wire_fits(due), LawsBase.wire_fits(now), hn)) : {CronServeEntry.ce_read_op.now(due, _) == Wr.Got{Sv.OClaim{due, now, fresh}, rest} : Wr.Dec<Sv.Op>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(fresh, rest)), Wr.Got{fresh, rest}, Wire.wire_strs_round_trip(fresh, rest, LCSR.cre.and_r(Bool.and(LawsBase.wire_fits(due), LawsBase.wire_fits(now)), LawsBase.wire_strs_fit(fresh), h))) : {CronServeEntry.ce_read_op.fresh(due, now, _) == Wr.Got{Sv.OClaim{due, now, fresh}, rest} : Wr.Dec<Sv.Op>}
      {==}
    case Sv.ORecover{+dead}:
      %LWire.pw6.nat(1n, LawsBase.wire_spell_nats(dead, rest), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.ORecover{dead}, rest} : Wr.Dec<Sv.Op>}
      %Wire.wire_nats_spells(dead, rest) : {CronServeEntry.ce_read_op.recover(Wr.get_list(~Nat, ~Wr.get_nat, _)) == Wr.Got{Sv.ORecover{dead}, rest} : Wr.Dec<Sv.Op>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, dead, rest)), Wr.Got{dead, rest}, Wire.wire_list_round_trip(dead, rest, h)) : {CronServeEntry.ce_read_op.recover(_) == Wr.Got{Sv.ORecover{dead}, rest} : Wr.Dec<Sv.Op>}
      {==}
    case Sv.OFinish{+d, +ran, +failed, +now}:
      %LWire.pw6.nat(2n, Wr.put_str(d, Wr.put_bool(ran, Wr.put_bool(failed, Wr.put_nat(now, rest)))), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.OFinish{d, ran, failed, now}, rest} : Wr.Dec<Sv.Op>}
      %pe.str_rt(d, Wr.put_bool(ran, Wr.put_bool(failed, Wr.put_nat(now, rest))), LCSR.cre.and_l(CronServeEntry.ce_str_fits(d), LawsBase.wire_fits(now), h)) : {CronServeEntry.ce_read_op.finish(_) == Wr.Got{Sv.OFinish{d, ran, failed, now}, rest} : Wr.Dec<Sv.Op>}
      %LCSR.crr.bool(ran, Wr.put_bool(failed, Wr.put_nat(now, rest))) : {CronServeEntry.ce_read_op.ran(d, _) == Wr.Got{Sv.OFinish{d, ran, failed, now}, rest} : Wr.Dec<Sv.Op>}
      %LCSR.crr.bool(failed, Wr.put_nat(now, rest)) : {CronServeEntry.ce_read_op.failed(d, ran, _) == Wr.Got{Sv.OFinish{d, ran, failed, now}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(now, rest, LCSR.cre.and_r(CronServeEntry.ce_str_fits(d), LawsBase.wire_fits(now), h)) : {CronServeEntry.ce_read_op.at(d, ran, failed, _) == Wr.Got{Sv.OFinish{d, ran, failed, now}, rest} : Wr.Dec<Sv.Op>}
      {==}
    case Sv.OCancel{+n}:
      %LWire.pw6.nat(3n, Wr.put_nat(n, rest), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.OCancel{n}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(n, rest, h) : {CronServeEntry.ce_read_op.cancel(_) == Wr.Got{Sv.OCancel{n}, rest} : Wr.Dec<Sv.Op>}
      {==}
    case Sv.OResume{+n, +now}:
      %LWire.pw6.nat(4n, Wr.put_nat(n, Wr.put_nat(now, rest)), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.OResume{n, now}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(n, Wr.put_nat(now, rest), LCSR.cre.and_l(LawsBase.wire_fits(n), LawsBase.wire_fits(now), h)) : {CronServeEntry.ce_read_op.resume(_) == Wr.Got{Sv.OResume{n, now}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(now, rest, LCSR.cre.and_r(LawsBase.wire_fits(n), LawsBase.wire_fits(now), h)) : {CronServeEntry.ce_read_op.when(n, _) == Wr.Got{Sv.OResume{n, now}, rest} : Wr.Dec<Sv.Op>}
      {==}
    case Sv.OCreate{+n, +f}:
      %LWire.pw6.nat(5n, Wr.put_nat(n, Cron.spell_fact(f, rest)), {==}) : {CronServeEntry.ce_read_op(_) == Wr.Got{Sv.OCreate{n, f}, rest} : Wr.Dec<Sv.Op>}
      %LWire.pw6.nat(n, Cron.spell_fact(f, rest), LCSR.cre.and_l(LawsBase.wire_fits(n), Cron.fact_fits(f), h)) : {CronServeEntry.ce_read_op.create(_) == Wr.Got{Sv.OCreate{n, f}, rest} : Wr.Dec<Sv.Op>}
      %pe.fact_rt(f, rest, LCSR.cre.and_r(LawsBase.wire_fits(n), Cron.fact_fits(f), h)) : {CronServeEntry.ce_read_op.made(n, _) == Wr.Got{Sv.OCreate{n, f}, rest} : Wr.Dec<Sv.Op>}
      {==}

# every event Rust writes reads back
def pe.ev_rt(e: FC.Ev, +h: {CronServeEntry.ce_ev_fits(e) == True{} : Bool}) -> {CronServeEntry.ce_read_ev(CronServeEntry.ce_spell_ev(e)) == Some{e} : Maybe<&2, FC.Ev>}:
  match e:
    case FC.EServe{+me, +k, +op}:
      +hr = LCSR.cre.and_r(LawsBase.wire_fits(me), Bool.and(CronServeEntry.ce_disk_fits(k), CronServeEntry.ce_op_fits(op)), h)
      %LWire.pw6.nat(0n, Wr.put_nat(me, CronServeEntry.ce_spell_disk(k, CronServeEntry.ce_spell_op(op, ""))), {==}) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.go(_)) == Some{FC.EServe{me, k, op}} : Maybe<&2, FC.Ev>}
      %LWire.pw6.nat(me, CronServeEntry.ce_spell_disk(k, CronServeEntry.ce_spell_op(op, "")), LCSR.cre.and_l(LawsBase.wire_fits(me), Bool.and(CronServeEntry.ce_disk_fits(k), CronServeEntry.ce_op_fits(op)), h)) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.serve(_)) == Some{FC.EServe{me, k, op}} : Maybe<&2, FC.Ev>}
      %Equal.sym(Wr.Dec<Sv.Disk>, CronServeEntry.ce_read_disk(Wr.get_nat(CronServeEntry.ce_spell_disk(k, CronServeEntry.ce_spell_op(op, "")))), Wr.Got{k, CronServeEntry.ce_spell_op(op, "")}, pe.disk_rt(k, CronServeEntry.ce_spell_op(op, ""), LCSR.cre.and_l(CronServeEntry.ce_disk_fits(k), CronServeEntry.ce_op_fits(op), hr))) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.disk(me, _)) == Some{FC.EServe{me, k, op}} : Maybe<&2, FC.Ev>}
      %Equal.sym(Wr.Dec<Sv.Op>, CronServeEntry.ce_read_op(Wr.get_nat(CronServeEntry.ce_spell_op(op, ""))), Wr.Got{op, ""}, pe.op_rt(op, "", LCSR.cre.and_r(CronServeEntry.ce_disk_fits(k), CronServeEntry.ce_op_fits(op), hr))) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.op(me, k, _)) == Some{FC.EServe{me, k, op}} : Maybe<&2, FC.Ev>}
      {==}
    case FC.EEnd{+d}:
      %LWire.pw6.nat(1n, Wr.put_str(d, ""), {==}) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.go(_)) == Some{FC.EEnd{d}} : Maybe<&2, FC.Ev>}
      %pe.str_rt(d, "", h) : {CronServeEntry.ce_read_ev.whole(CronServeEntry.ce_read_ev.end(_)) == Some{FC.EEnd{d}} : Maybe<&2, FC.Ev>}
      {==}

# The call
# --------

def pe.ask_end(b: Bool, f: CS.Fact, +n: Nat) -> {FC.ffi.end(b, f, n) == CronServeEntry.ce_ask(CronServeEntry.ce_whole(CronServeEntry.CeAsk, b, CronServeEntry.CeAsk{n, f})) : String}:
  match b:
    case True{}:
      %CronServe.cron_serve_due_exact(f, n) : {Wr.put_bool(Sv.due(f, n), "") == Wr.put_bool(_, "") : String}
      {==}
    case False{}:
      {==}

def pe.ask_fact(+n: Nat, r: Wr.Dec<CS.Fact>) -> {FC.ffi.fact(n, r) == CronServeEntry.ce_ask(CronServeEntry.ce_read_ask.fact(n, r)) : String}:
  match r:
    case Wr.Got{f, s}:
      pe.ask_end(Wr.end(s), f, n)
    case Wr.Bad{}:
      {==}

def pe.ask_go(r: Wr.Dec<Nat>) -> {FC.ffi.go(r) == CronServeEntry.ce_ask(CronServeEntry.ce_read_ask.go(r)) : String}:
  match r:
    case Wr.Got{+n, +s}:
      %LCSR.cre.fact(s) : {FC.ffi.fact(n, _) == CronServeEntry.ce_ask(CronServeEntry.ce_read_ask.fact(n, Cron.read_fact(s))) : String}
      pe.ask_fact(n, Cron.read_fact(s))
    case Wr.Bad{}:
      {==}

# the call answers every input as the laws' reader reads it
def pe.ask(s: String) -> {FC.ffi(s) == CronServeEntry.ce_ask(CronServeEntry.ce_read_ask(s)) : String}:
  pe.ask_go(Wr.get_nat(s))

# every question Rust writes reads back
def pe.ask_rt(+now: Nat, +f: CS.Fact, +h: {Bool.and(LawsBase.wire_fits(now), Cron.fact_fits(f)) == True{} : Bool}) -> {CronServeEntry.ce_ask(CronServeEntry.ce_read_ask(CronServeEntry.ce_spell_ask(now, f))) == CronServeEntry.ce_due(now, f) : String}:
  %LWire.pw6.nat(now, Cron.spell_fact(f, ""), LCSR.cre.and_l(LawsBase.wire_fits(now), Cron.fact_fits(f), h)) : {CronServeEntry.ce_ask(CronServeEntry.ce_read_ask.go(_)) == CronServeEntry.ce_due(now, f) : String}
  %pe.fact_rt(f, "", LCSR.cre.and_r(LawsBase.wire_fits(now), Cron.fact_fits(f), h)) : {CronServeEntry.ce_ask(CronServeEntry.ce_read_ask.fact(now, _)) == CronServeEntry.ce_due(now, f) : String}
  {==}
