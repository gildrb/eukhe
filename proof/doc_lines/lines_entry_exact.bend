# eukhe: the proof of LAW lines_entry_exact

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/ffi_doc_lines/exact.bend as Fdx

# the law's claim on s: s spells a request whose numbers fit
def fle_Ex(s: String) -> Type:
  &r: DocLines.lines.Req -> ({s == DocLines.lines.spell_req(r) : String} & {DocLines.lines.ReqFits(r) == True{} : Bool})

# ==== a run ====

# what a run decoder's answer says about its input s
def fle_pr(s: String, d: Wr.Dec<Dl.Run>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == DocLines.lines.spell_run(x, r) : String} & {DocLines.lines.RunFit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a spelled ending, then a spelled length that fits
def fle_run_n(-s: String, -o: Maybe<&2, Dl.End>, -s2: String, eo: {s == LawsBase.proj_spell_mend(o, s2) : String},
  d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s2, d)) -> fle_pr(s, Fdl.get_run.n(o, d)):
  match d:
    case Wr.Got{+n, +r}:
      (en, fn) = pn
      (Equal.trans(String, s, LawsBase.proj_spell_mend(o, s2), LawsBase.proj_spell_mend(o, Wr.put_nat(n, r)), eo,
        Equal.cong(String, String, z => LawsBase.proj_spell_mend(o, z), s2, Wr.put_nat(n, r), en)), fn)
    case Wr.Bad{}:
      Unit{}

# a spelled ending, then the length
def fle_run_end(-s: String, d: Wr.Dec<Maybe<&2, Dl.End>>, pm: Fdx.fdx_pm(s, d)) -> fle_pr(s, Fdl.get_run.end(d)):
  match d:
    case Wr.Got{+o, +s2}:
      fle_run_n(s, o, s2, pm, Wr.get_nat(s2), Fdx.fdx_nat(s2))
    case Wr.Bad{}:
      Unit{}

# every run the decoder reads is spelled and fits
def fle_run(+s: String) -> fle_pr(s, Fdl.get_run(s)):
  fle_run_end(s, Fdl.get_mend(s), Fdx.fdx_mend(s))

# ==== a list of runs ====

# the spellings of the runs xs, then rest
def fle_runs_items(xs: List<&2, Dl.Run>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocLines.lines.spell_run(x, fle_runs_items(t, rest))

# the list encoder's loop: the count and the items
def fle_runs_go(xs: List<&2, Dl.Run>, -rest: String) -> {Wr.put_list.go(~Dl.Run, ~DocLines.lines.spell_run, xs, rest) == (List.length(&2, Dl.Run, xs), fle_runs_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Run, ~DocLines.lines.spell_run, t, rest), (List.length(&2, Dl.Run, t), fle_runs_items(t, rest)), fle_runs_go(t, rest)) : {Wr.put_list.step(~Dl.Run, ~DocLines.lines.spell_run, x, _) == (1n+List.length(&2, Dl.Run, t), DocLines.lines.spell_run(x, fle_runs_items(t, rest))) : Nat & String}
      {==}

# a list of runs is its count, then its items
def fle_runs_put(+xs: List<&2, Dl.Run>, -rest: String) -> {Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, xs, rest) == Wr.put_nat(List.length(&2, Dl.Run, xs), fle_runs_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Run, ~DocLines.lines.spell_run, xs, rest), (List.length(&2, Dl.Run, xs), fle_runs_items(xs, rest)), fle_runs_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dl.Run, xs), fle_runs_items(xs, rest)) : String}
  {==}

# what the item loop's answer says about its input s (m + 1 items)
def fle_pll(s: String, m: Nat, d: Wr.Dec<List<&2, Dl.Run>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == fle_runs_items(xs, r) : String} & ({List.length(&2, Dl.Run, xs) == 1n+m : Nat} & {DocLines.lines.RunsFit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# one more spelled run before the rest of the loop
def fle_runs_step(-s: String, +x: Dl.Run, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Dl.Run>>,
  ih: fle_pll(s3, k, d), px: fle_pr(s, Wr.Got{x, s3})) -> fle_pll(s, 1n+k, Wr.get_list.cons(Dl.Run, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, (e2, e3)) = ih
      (ex, fx) = px
      (Equal.trans(String, s, DocLines.lines.spell_run(x, s3), DocLines.lines.spell_run(x, fle_runs_items(ys, r)), ex,
          Equal.cong(String, String, z => DocLines.lines.spell_run(x, z), s3, fle_runs_items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dl.Run, ys), 1n+k, e2),
          Fdx.fdx_and(DocLines.lines.RunFit(x), DocLines.lines.RunsFit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled runs that fit
def fle_runs_loop(m: Nat, cur: Wr.Dec<Dl.Run>, +s: String, pc: fle_pr(s, cur)) ->
  fle_pll(s, m, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, s3}:
      (ex, fx) = pc
      (ex, ({==}, Fdx.fdx_and(DocLines.lines.RunFit(x), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      fle_runs_step(s, x, s3, k, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, k, Fdl.get_run(s3)),
        fle_runs_loop(k, Fdl.get_run(s3), s3, fle_run(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-runs decoder's answer says about its input s
def fle_pls(s: String, d: Wr.Dec<List<&2, Dl.Run>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, xs, r) : String} & {DocLines.lines.WireFits(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the count spelled before the items is the list's length
def fle_runs_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Dl.Run>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == fle_runs_items(xs, r) : String},
  e2: {List.length(&2, Dl.Run, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, xs, r), Wr.put_nat(List.length(&2, Dl.Run, xs), fle_runs_items(xs, r)), fle_runs_put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Dl.Run, xs), 1n+m, e2) : {s == Wr.put_nat(_, fle_runs_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

# m + 1 spelled runs after their count: a spelled list that fits
def fle_runs_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dl.Run>>, pl: fle_pll(s2, m, d)) -> fle_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (+e2, e3)) = pl
      (fle_runs_eq(s, s2, m, xs, r, en, e1, e2),
        Fdx.fdx_and(LawsBase.wire_fits(List.length(&2, Dl.Run, xs)), DocLines.lines.RunsFit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Dl.Run, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Dl.Run, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

# the count 0 is the empty list; else the item loop runs
def fle_runs_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> fle_pls(s, Wr.get_list.start(~Dl.Run, ~Fdl.get_run, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      fle_runs_conv(s, s2, m, en, fn, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, m, Fdl.get_run(s2)),
        fle_runs_loop(m, Fdl.get_run(s2), s2, fle_run(s2)))

# a list starts with a spelled count that fits
def fle_runs_top(+s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d)) -> fle_pls(s, Wr.get_list.start(~Dl.Run, ~Fdl.get_run, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fle_runs_nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of runs the decoder reads is spelled and fits
def fle_runs(+s: String) -> fle_pls(s, Wr.get_list(~Dl.Run, ~Fdl.get_run, s)):
  fle_runs_top(s, Wr.get_nat(s), Fdx.fdx_nat(s))

# ==== the entry ====

# a plan with nothing left over
def fle_plan_done(+s3: String, -s: String, +rs: List<&2, Dl.Run>, +c: Dl.End, -s2: String,
  er: {s == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, s2) : String},
  fr: {DocLines.lines.WireFits(rs) == True{} : Bool}, ec: {s2 == LawsBase.proj_spell_end(c, s3) : String},
  h: {LawsBase.wire_opens_err(Fdl.run.done(rs, c, Wr.end(s3))) == False{} : Bool}) -> fle_Ex(s):
  match s3:
    case SNil{}:
      (DocLines.lines.Plan{rs, c},
        (Equal.trans(String, s, Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, s2), Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, LawsBase.proj_spell_end(c, "")), er,
          Equal.cong(String, String, z => Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, z), s2, LawsBase.proj_spell_end(c, ""), ec)), fr))
    case SCon{ch, t}:
      Fdx.fdx_absurd(fle_Ex(s), h)

# the carry of a plan
def fle_plan_carry(-s: String, +rs: List<&2, Dl.Run>, -s2: String,
  er: {s == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, rs, s2) : String},
  fr: {DocLines.lines.WireFits(rs) == True{} : Bool}, d: Wr.Dec<Dl.End>, pe: Fdx.fdx_pe(s2, d),
  h: {LawsBase.wire_opens_err(Fdl.run.carry(rs, d)) == False{} : Bool}) -> fle_Ex(s):
  match d:
    case Wr.Got{+c, +s3}:
      fle_plan_done(s3, s, rs, c, s2, er, fr, pe, h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fle_Ex(s), h)

# a load with nothing left over
def fle_load_done(+s2: String, -t: String, +p: Dl.Proj, ep: {t == LawsBase.proj_spell(p, s2) : String},
  fp: {LawsBase.proj_fits(p) == True{} : Bool},
  h: {LawsBase.wire_opens_err(Fdl.load.done(p, Wr.end(s2))) == False{} : Bool}) -> fle_Ex(SCon{'L', t}):
  match s2:
    case SNil{}:
      (DocLines.lines.Load{p}, (Equal.cong(String, String, z => SCon{'L', z}, t, LawsBase.proj_spell(p, ""), ep), fp))
    case SCon{ch, u}:
      Fdx.fdx_absurd(fle_Ex(SCon{'L', t}), h)

# `L` then a projection
def fle_load(-t: String, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(t, d),
  h: {LawsBase.wire_opens_err(Fdl.load.run(d)) == False{} : Bool}) -> fle_Ex(SCon{'L', t}):
  match d:
    case Wr.Got{+p, +s2}:
      (ep, fp) = pd
      fle_load_done(s2, t, p, ep, fp, h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fle_Ex(SCon{'L', t}), h)

# a write with nothing left over
def fle_write_done(+s3: String, -t: String, +p: Dl.Proj, -s2: String, ep: {t == LawsBase.proj_spell(p, s2) : String},
  fp: {LawsBase.proj_fits(p) == True{} : Bool}, +q: Dl.Proj, eq: {s2 == LawsBase.proj_spell(q, s3) : String},
  fq: {LawsBase.proj_fits(q) == True{} : Bool},
  h: {LawsBase.wire_opens_err(Fdl.write.done(p, q, Wr.end(s3))) == False{} : Bool}) -> fle_Ex(SCon{'W', t}):
  match s3:
    case SNil{}:
      (DocLines.lines.Write{p, q},
        (Equal.cong(String, String, z => SCon{'W', z}, t, LawsBase.proj_spell(p, LawsBase.proj_spell(q, "")),
            Equal.trans(String, t, LawsBase.proj_spell(p, s2), LawsBase.proj_spell(p, LawsBase.proj_spell(q, "")), ep,
              Equal.cong(String, String, z => LawsBase.proj_spell(p, z), s2, LawsBase.proj_spell(q, ""), eq))),
          Fdx.fdx_and(LawsBase.proj_fits(p), LawsBase.proj_fits(q), fp, fq)))
    case SCon{ch, u}:
      Fdx.fdx_absurd(fle_Ex(SCon{'W', t}), h)

# the second projection of a write
def fle_write_next(-t: String, +p: Dl.Proj, -s2: String, ep: {t == LawsBase.proj_spell(p, s2) : String},
  fp: {LawsBase.proj_fits(p) == True{} : Bool}, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(s2, d),
  h: {LawsBase.wire_opens_err(Fdl.write.next(p, d)) == False{} : Bool}) -> fle_Ex(SCon{'W', t}):
  match d:
    case Wr.Got{+q, +s3}:
      (eq, fq) = pd
      fle_write_done(s3, t, p, s2, ep, fp, q, eq, fq, h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fle_Ex(SCon{'W', t}), h)

# `W` then two projections
def fle_write(-t: String, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(t, d),
  h: {LawsBase.wire_opens_err(Fdl.write.run(d)) == False{} : Bool}) -> fle_Ex(SCon{'W', t}):
  match d:
    case Wr.Got{+p, +s2}:
      (ep, fp) = pd
      fle_write_next(t, p, s2, ep, fp, Fdl.get_proj(s2), Fdx.fdx_proj(s2), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fle_Ex(SCon{'W', t}), h)

# the dispatch: a char equal to 76 is `L`, to 87 is `W`, else an error
def fle_pick(+x: U32, +t: String, l: Bool, el: {U32.is_eq(x, 76) == l : Bool}, w: Bool, ew: {U32.is_eq(x, 87) == w : Bool},
  h: {LawsBase.wire_opens_err(Fdl.kind.pick(l, w, t)) == False{} : Bool}) -> fle_Ex(SCon{Chr{x}, t}):
  match l:
    case True{}:
      %Equal.sym(U32, x, 76, PWireBoolExact.wr_eq_sound(x, 76, el)) : fle_Ex(SCon{Chr{_}, t})
      fle_load(t, Fdl.get_proj(t), Fdx.fdx_proj(t), h)
    case False{}:
      match w:
        case True{}:
          %Equal.sym(U32, x, 87, PWireBoolExact.wr_eq_sound(x, 87, ew)) : fle_Ex(SCon{Chr{_}, t})
          fle_write(t, Fdl.get_proj(t), Fdx.fdx_proj(t), h)
        case False{}:
          Fdx.fdx_absurd(fle_Ex(SCon{Chr{x}, t}), h)

# an input that is no plan
def fle_kind(+s: String, h: {LawsBase.wire_opens_err(Fdl.kind(s)) == False{} : Bool}) -> fle_Ex(s):
  match s:
    case SNil{}:
      Fdx.fdx_absurd(fle_Ex(SNil{}), h)
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          fle_pick(x, t, U32.is_eq(x, 76), {==}, U32.is_eq(x, 87), {==}, h)

# the runs decoder tried first: a plan, else `L` / `W`
def fle_entry(+s: String, d: Wr.Dec<List<&2, Dl.Run>>, pd: fle_pls(s, d),
  h: {LawsBase.wire_opens_err(Fdl.run.runs(d, s)) == False{} : Bool}) -> fle_Ex(s):
  match d:
    case Wr.Got{+rs, +s2}:
      (er, fr) = pd
      fle_plan_carry(s, rs, s2, er, fr, Fdl.get_end(s2), Fdx.fdx_end(s2), h)
    case Wr.Bad{}:
      fle_kind(s, h)

# the law: follow the entry's decoders on s
def DocLines.lines_entry_exact(s, h):
  fle_entry(s, Wr.get_list(~Dl.Run, ~Fdl.get_run, s), fle_runs(s), h)
