# eukhe: the proof of LAW doc_lines_ffi_exact
# The entry reads every input as the spec's reader does (each item reader
# is the spec's, so each list reader is) and answers what the spec
# decides (the model's plan, carry and write are the spec's on every
# projection), spelled as the spec spells it.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/doc_lines.bend as DocLines

# The item readers
# ----------------

def dlx.end_tag(r: Wr.Dec<Nat>) -> {Fdl.get_end.tag(r) == DocLines.lines.sp_end.tag(r) : Wr.Dec<Dl.End>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def dlx.end(s: String) -> {Fdl.get_end(s) == DocLines.lines.sp_end(s) : Wr.Dec<Dl.End>}:
  dlx.end_tag(Wr.get_nat(s))

def dlx.mend_some(r: Wr.Dec<Dl.End>) -> {Fdl.get_mend.some(r) == DocLines.lines.sp_mend.some(r) : Wr.Dec<Maybe<&2, Dl.End>>}:
  match r:
    case Wr.Got{e, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dlx.mend_tag(r: Wr.Dec<Nat>) -> {Fdl.get_mend.tag(r) == DocLines.lines.sp_mend.tag(r) : Wr.Dec<Maybe<&2, Dl.End>>}:
  match r:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(s), DocLines.lines.sp_end(s), dlx.end(s)) : {Fdl.get_mend.some(_) == DocLines.lines.sp_mend.some(DocLines.lines.sp_end(s)) : Wr.Dec<Maybe<&2, Dl.End>>}
          dlx.mend_some(DocLines.lines.sp_end(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def dlx.mend(s: String) -> {Fdl.get_mend(s) == DocLines.lines.sp_mend(s) : Wr.Dec<Maybe<&2, Dl.End>>}:
  dlx.mend_tag(Wr.get_nat(s))

def dlx.run_n(o: Maybe<&2, Dl.End>, r: Wr.Dec<Nat>) -> {Fdl.get_run.n(o, r) == DocLines.lines.sp_run.n(o, r) : Wr.Dec<Dl.Run>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dlx.run_end(r: Wr.Dec<Maybe<&2, Dl.End>>) -> {Fdl.get_run.end(r) == DocLines.lines.sp_run.end(r) : Wr.Dec<Dl.Run>}:
  match r:
    case Wr.Got{o, s}:
      dlx.run_n(o, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def dlx.run(+s: String) -> {Fdl.get_run(s) == DocLines.lines.sp_run(s) : Wr.Dec<Dl.Run>}:
  %Equal.sym(Wr.Dec<Maybe<&2, Dl.End>>, Fdl.get_mend(s), DocLines.lines.sp_mend(s), dlx.mend(s)) : {Fdl.get_run.end(_) == DocLines.lines.sp_run(s) : Wr.Dec<Dl.Run>}
  dlx.run_end(DocLines.lines.sp_mend(s))

def dlx.line_end(n: Nat, r: Wr.Dec<Maybe<&2, Dl.End>>) -> {Fdl.get_line.end(n, r) == DocLines.lines.sp_line.end(n, r) : Wr.Dec<Dl.Line>}:
  match r:
    case Wr.Got{o, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dlx.line_len(r: Wr.Dec<Nat>) -> {Fdl.get_line.len(r) == DocLines.lines.sp_line.len(r) : Wr.Dec<Dl.Line>}:
  match r:
    case Wr.Got{+n, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Dl.End>>, Fdl.get_mend(s), DocLines.lines.sp_mend(s), dlx.mend(s)) : {Fdl.get_line.end(n, _) == DocLines.lines.sp_line.len(Wr.Got{n, s}) : Wr.Dec<Dl.Line>}
      dlx.line_end(n, DocLines.lines.sp_mend(s))
    case Wr.Bad{}:
      {==}

def dlx.line(s: String) -> {Fdl.get_line(s) == DocLines.lines.sp_line(s) : Wr.Dec<Dl.Line>}:
  dlx.line_len(Wr.get_nat(s))

# The list readers
# ----------------

def dlx.runs_go(n: Nat, cur: Wr.Dec<Dl.Run>) -> {Wr.get_list.go(~Dl.Run, ~Fdl.get_run, n, cur) == Wr.get_list.go(~Dl.Run, ~DocLines.lines.sp_run, n, cur) : Wr.Dec<List<&2, Dl.Run>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Dl.Run>, Fdl.get_run(r), DocLines.lines.sp_run(r), dlx.run(r)) : {Wr.get_list.cons(Dl.Run, x, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, k, _)) == Wr.get_list.cons(Dl.Run, x, Wr.get_list.go(~Dl.Run, ~DocLines.lines.sp_run, k, DocLines.lines.sp_run(r))) : Wr.Dec<List<&2, Dl.Run>>}
      %Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, k, DocLines.lines.sp_run(r)), Wr.get_list.go(~Dl.Run, ~DocLines.lines.sp_run, k, DocLines.lines.sp_run(r)), dlx.runs_go(k, DocLines.lines.sp_run(r))) : {Wr.get_list.cons(Dl.Run, x, _) == Wr.get_list.cons(Dl.Run, x, Wr.get_list.go(~Dl.Run, ~DocLines.lines.sp_run, k, DocLines.lines.sp_run(r))) : Wr.Dec<List<&2, Dl.Run>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def dlx.runs_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Dl.Run, ~Fdl.get_run, d) == Wr.get_list.start(~Dl.Run, ~DocLines.lines.sp_run, d) : Wr.Dec<List<&2, Dl.Run>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Dl.Run>, Fdl.get_run(s), DocLines.lines.sp_run(s), dlx.run(s)) : {Wr.get_list.go(~Dl.Run, ~Fdl.get_run, m, _) == Wr.get_list.go(~Dl.Run, ~DocLines.lines.sp_run, m, DocLines.lines.sp_run(s)) : Wr.Dec<List<&2, Dl.Run>>}
          dlx.runs_go(m, DocLines.lines.sp_run(s))
    case Wr.Bad{}:
      {==}

def dlx.lines_go(n: Nat, cur: Wr.Dec<Dl.Line>) -> {Wr.get_list.go(~Dl.Line, ~Fdl.get_line, n, cur) == Wr.get_list.go(~Dl.Line, ~DocLines.lines.sp_line, n, cur) : Wr.Dec<List<&2, Dl.Line>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Dl.Line>, Fdl.get_line(r), DocLines.lines.sp_line(r), dlx.line(r)) : {Wr.get_list.cons(Dl.Line, x, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, k, _)) == Wr.get_list.cons(Dl.Line, x, Wr.get_list.go(~Dl.Line, ~DocLines.lines.sp_line, k, DocLines.lines.sp_line(r))) : Wr.Dec<List<&2, Dl.Line>>}
      %Equal.sym(Wr.Dec<List<&2, Dl.Line>>, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, k, DocLines.lines.sp_line(r)), Wr.get_list.go(~Dl.Line, ~DocLines.lines.sp_line, k, DocLines.lines.sp_line(r)), dlx.lines_go(k, DocLines.lines.sp_line(r))) : {Wr.get_list.cons(Dl.Line, x, _) == Wr.get_list.cons(Dl.Line, x, Wr.get_list.go(~Dl.Line, ~DocLines.lines.sp_line, k, DocLines.lines.sp_line(r))) : Wr.Dec<List<&2, Dl.Line>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def dlx.lines_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Dl.Line, ~Fdl.get_line, d) == Wr.get_list.start(~Dl.Line, ~DocLines.lines.sp_line, d) : Wr.Dec<List<&2, Dl.Line>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Dl.Line>, Fdl.get_line(s), DocLines.lines.sp_line(s), dlx.line(s)) : {Wr.get_list.go(~Dl.Line, ~Fdl.get_line, m, _) == Wr.get_list.go(~Dl.Line, ~DocLines.lines.sp_line, m, DocLines.lines.sp_line(s)) : Wr.Dec<List<&2, Dl.Line>>}
          dlx.lines_go(m, DocLines.lines.sp_line(s))
    case Wr.Bad{}:
      {==}

def dlx.proj_lines(b: Bool, r: Wr.Dec<List<&2, Dl.Line>>) -> {Fdl.get_proj.lines(b, r) == DocLines.lines.sp_proj.lines(b, r) : Wr.Dec<Dl.Proj>}:
  match r:
    case Wr.Got{ls, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dlx.proj_bom(r: Wr.Dec<Bool>) -> {Fdl.get_proj.bom(r) == DocLines.lines.sp_proj.bom(r) : Wr.Dec<Dl.Proj>}:
  match r:
    case Wr.Got{+b, +s}:
      %Equal.sym(Wr.Dec<List<&2, Dl.Line>>, Wr.get_list.start(~Dl.Line, ~Fdl.get_line, Wr.get_nat(s)), Wr.get_list.start(~Dl.Line, ~DocLines.lines.sp_line, Wr.get_nat(s)), dlx.lines_start(Wr.get_nat(s))) : {Fdl.get_proj.lines(b, _) == DocLines.lines.sp_proj.bom(Wr.Got{b, s}) : Wr.Dec<Dl.Proj>}
      dlx.proj_lines(b, Wr.get_list(~Dl.Line, ~DocLines.lines.sp_line, s))
    case Wr.Bad{}:
      {==}

def dlx.proj(s: String) -> {Fdl.get_proj(s) == DocLines.lines.sp_proj(s) : Wr.Dec<Dl.Proj>}:
  dlx.proj_bom(Wr.get_bool(s))

# The decisions
# -------------

def dlx.sep(o: Maybe<&2, Dl.End>, -c: Dl.End) -> {Dl.sep(o, c) == DocLines.lines.sp_sep(o, c) : Dl.End}:
  match o:
    case None{}:
      {==}
    case Some{e}:
      {==}

def dlx.plan(rs: List<&2, Dl.Run>, c: Dl.End) -> {Dl.plan(rs, c) == DocLines.lines.sp_plan(rs, c) : List<&2, Dl.Seps>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Dl.Run{+o, n}:
          match n:
            case 0n:
              dlx.plan(rest, c)
            case 1n+m:
              %Equal.sym(Dl.End, Dl.sep(o, c), DocLines.lines.sp_sep(o, c), dlx.sep(o, c)) : {Dl.Seps{_, 1n+m} <> Dl.plan(rest, _) == DocLines.lines.sp_plan(Dl.Run{o, 1n+m} <> rest, c) : List<&2, Dl.Seps>}
              %Equal.sym(List<&2, Dl.Seps>, Dl.plan(rest, DocLines.lines.sp_sep(o, c)), DocLines.lines.sp_plan(rest, DocLines.lines.sp_sep(o, c)), dlx.plan(rest, DocLines.lines.sp_sep(o, c))) : {Dl.Seps{DocLines.lines.sp_sep(o, c), 1n+m} <> _ == DocLines.lines.sp_plan(Dl.Run{o, 1n+m} <> rest, c) : List<&2, Dl.Seps>}
              {==}

def dlx.first(ls: List<&2, Dl.Line>) -> {Dl.first_end(ls) == DocLines.lines.sp_first(ls) : Maybe<&2, Dl.End>}:
  match ls:
    case Nil{}:
      {==}
    case l <> rest:
      match l:
        case Dl.Line{n, en}:
          match en:
            case None{}:
              dlx.first(rest)
            case Some{e}:
              {==}

def dlx.or_lf(m: Maybe<&2, Dl.End>) -> {Dl.or_lf(m) == DocLines.lines.OrLf(m) : Dl.End}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

def dlx.warn_two(e: Dl.End, f: Dl.End) -> {Bool.not(Dl.End.same(e, f)) == DocLines.lines.Warn.two(e, f) : Bool}:
  match e f:
    case Dl.Lf{} Dl.Lf{}:
      {==}
    case Dl.Lf{} Dl.CrLf{}:
      {==}
    case Dl.CrLf{} Dl.Lf{}:
      {==}
    case Dl.CrLf{} Dl.CrLf{}:
      {==}

def dlx.warn(k: Maybe<&2, Dl.End>, a: Maybe<&2, Dl.End>) -> {Dl.warn(k, a) == DocLines.lines.Warn(k, a) : Bool}:
  match k:
    case None{}:
      {==}
    case Some{e}:
      match a:
        case None{}:
          {==}
        case Some{f}:
          dlx.warn_two(e, f)

def dlx.carry(p: Dl.Proj) -> {Dl.carry(p) == DocLines.lines.sp_carry(p) : Dl.End}:
  match p:
    case Dl.Proj{b, +ls}:
      %Equal.sym(Maybe<&2, Dl.End>, Dl.first_end(ls), DocLines.lines.sp_first(ls), dlx.first(ls)) : {Dl.or_lf(_) == DocLines.lines.sp_carry(Dl.Proj{b, ls}) : Dl.End}
      dlx.or_lf(DocLines.lines.sp_first(ls))

def dlx.kept(p: Dl.Proj, q: Dl.Proj) -> {Dl.write(p, q) == DocLines.lines.sp_kept(p, q) : Dl.Kept}:
  match p q:
    case Dl.Proj{b, +ls} Dl.Proj{c, +ms}:
      %Equal.sym(Maybe<&2, Dl.End>, Dl.first_end(ls), DocLines.lines.sp_first(ls), dlx.first(ls)) : {Dl.Kept{b, Dl.or_lf(_), Dl.warn(_, Dl.first_end(ms))} == DocLines.lines.sp_kept(Dl.Proj{b, ls}, Dl.Proj{c, ms}) : Dl.Kept}
      %Equal.sym(Maybe<&2, Dl.End>, Dl.first_end(ms), DocLines.lines.sp_first(ms), dlx.first(ms)) : {Dl.Kept{b, Dl.or_lf(DocLines.lines.sp_first(ls)), Dl.warn(DocLines.lines.sp_first(ls), _)} == DocLines.lines.sp_kept(Dl.Proj{b, ls}, Dl.Proj{c, ms}) : Dl.Kept}
      %Equal.sym(Dl.End, Dl.or_lf(DocLines.lines.sp_first(ls)), DocLines.lines.OrLf(DocLines.lines.sp_first(ls)), dlx.or_lf(DocLines.lines.sp_first(ls))) : {Dl.Kept{b, _, Dl.warn(DocLines.lines.sp_first(ls), DocLines.lines.sp_first(ms))} == DocLines.lines.sp_kept(Dl.Proj{b, ls}, Dl.Proj{c, ms}) : Dl.Kept}
      %Equal.sym(Bool, Dl.warn(DocLines.lines.sp_first(ls), DocLines.lines.sp_first(ms)), DocLines.lines.Warn(DocLines.lines.sp_first(ls), DocLines.lines.sp_first(ms)), dlx.warn(DocLines.lines.sp_first(ls), DocLines.lines.sp_first(ms))) : {Dl.Kept{b, DocLines.lines.OrLf(DocLines.lines.sp_first(ls)), _} == DocLines.lines.sp_kept(Dl.Proj{b, ls}, Dl.Proj{c, ms}) : Dl.Kept}
      {==}

# The spellings
# -------------

def dlx.put_end(e: Dl.End, -rest: String) -> {Fdl.put_end(e, rest) == LawsBase.proj_spell_end(e, rest) : String}:
  match e:
    case Dl.Lf{}:
      {==}
    case Dl.CrLf{}:
      {==}

def dlx.seps(x: Dl.Seps, -rest: String) -> {Fdl.put_seps(x, rest) == DocLines.lines.spell_seps(x, rest) : String}:
  match x:
    case Dl.Seps{e, n}:
      dlx.put_end(e, Wr.put_nat(n, rest))

def dlx.seps_list_go(xs: List<&2, Dl.Seps>, -rest: String) -> {Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, xs, rest) == (List.length(&2, Dl.Seps, xs), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, t, rest), (List.length(&2, Dl.Seps, t), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest)), dlx.seps_list_go(t, rest)) : {Wr.put_list.step(~Dl.Seps, ~Fdl.put_seps, x, _) == (1n+List.length(&2, Dl.Seps, t), DocLines.lines.spell_seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest))) : Nat & String}
      %Equal.sym(String, Fdl.put_seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest)), DocLines.lines.spell_seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest)), dlx.seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest))) : {(1n+List.length(&2, Dl.Seps, t), _) == (1n+List.length(&2, Dl.Seps, t), DocLines.lines.spell_seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest))) : Nat & String}
      {==}

def dlx.seps_list_go_sp(xs: List<&2, Dl.Seps>, -rest: String) -> {Wr.put_list.go(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest) == (List.length(&2, Dl.Seps, xs), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest), (List.length(&2, Dl.Seps, t), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest)), dlx.seps_list_go_sp(t, rest)) : {Wr.put_list.step(~Dl.Seps, ~DocLines.lines.spell_seps, x, _) == (1n+List.length(&2, Dl.Seps, t), DocLines.lines.spell_seps(x, LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, t, rest))) : Nat & String}
      {==}

def dlx.seps_list(+xs: List<&2, Dl.Seps>, +rest: String) -> {Wr.put_list(~Dl.Seps, ~Fdl.put_seps, xs, rest) == Wr.put_list(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, xs, rest), (List.length(&2, Dl.Seps, xs), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest)), dlx.seps_list_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest), (List.length(&2, Dl.Seps, xs), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest)), dlx.seps_list_go_sp(xs, rest)) : {Wr.put_list.fin((List.length(&2, Dl.Seps, xs), LawsBase.wire_put_items(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

def dlx.put_kept(k: Dl.Kept) -> {Fdl.put_kept(k) == DocLines.lines.spell_kept(k) : String}:
  match k:
    case Dl.Kept{b, e, w}:
      match e:
        case Dl.Lf{}:
          {==}
        case Dl.CrLf{}:
          {==}

# The entry
# ---------

def dlx.plan_done(+rs: List<&2, Dl.Run>, +c: Dl.End, b: Bool) -> {Fdl.run.done(rs, c, b) == DocLines.lines.sp_plan_done(rs, c, b) : String}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Dl.Seps>, Dl.plan(rs, c), DocLines.lines.sp_plan(rs, c), dlx.plan(rs, c)) : {Wr.put_list(~Dl.Seps, ~Fdl.put_seps, _, "") == DocLines.lines.sp_plan_done(rs, c, True{}) : String}
      dlx.seps_list(DocLines.lines.sp_plan(rs, c), "")
    case False{}:
      {==}

def dlx.plan_carry(+rs: List<&2, Dl.Run>, r: Wr.Dec<Dl.End>) -> {Fdl.run.carry(rs, r) == DocLines.lines.sp_plan_carry(rs, r) : String}:
  match r:
    case Wr.Got{c, s}:
      dlx.plan_done(rs, c, Wr.end(s))
    case Wr.Bad{}:
      {==}

def dlx.load_done(+p: Dl.Proj, b: Bool) -> {Fdl.load.done(p, b) == DocLines.lines.sp_load_done(p, b) : String}:
  match b:
    case True{}:
      %Equal.sym(Dl.End, Dl.carry(p), DocLines.lines.sp_carry(p), dlx.carry(p)) : {Fdl.put_end(_, "") == DocLines.lines.sp_load_done(p, True{}) : String}
      dlx.put_end(DocLines.lines.sp_carry(p), "")
    case False{}:
      {==}

def dlx.load(r: Wr.Dec<Dl.Proj>) -> {Fdl.load.run(r) == DocLines.lines.sp_load(r) : String}:
  match r:
    case Wr.Got{p, s}:
      dlx.load_done(p, Wr.end(s))
    case Wr.Bad{}:
      {==}

def dlx.write_done(+p: Dl.Proj, +q: Dl.Proj, b: Bool) -> {Fdl.write.done(p, q, b) == DocLines.lines.sp_write_done(p, q, b) : String}:
  match b:
    case True{}:
      %Equal.sym(Dl.Kept, Dl.write(p, q), DocLines.lines.sp_kept(p, q), dlx.kept(p, q)) : {Fdl.put_kept(_) == DocLines.lines.sp_write_done(p, q, True{}) : String}
      dlx.put_kept(DocLines.lines.sp_kept(p, q))
    case False{}:
      {==}

def dlx.write_next(+p: Dl.Proj, r: Wr.Dec<Dl.Proj>) -> {Fdl.write.next(p, r) == DocLines.lines.sp_write_next(p, r) : String}:
  match r:
    case Wr.Got{q, s}:
      dlx.write_done(p, q, Wr.end(s))
    case Wr.Bad{}:
      {==}

def dlx.write(r: Wr.Dec<Dl.Proj>) -> {Fdl.write.run(r) == DocLines.lines.sp_write(r) : String}:
  match r:
    case Wr.Got{+p, +s}:
      %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(s), DocLines.lines.sp_proj(s), dlx.proj(s)) : {Fdl.write.next(p, _) == DocLines.lines.sp_write(Wr.Got{p, s}) : String}
      dlx.write_next(p, DocLines.lines.sp_proj(s))
    case Wr.Bad{}:
      {==}

def dlx.pick(l: Bool, w: Bool, +t: String) -> {Fdl.kind.pick(l, w, t) == DocLines.lines.sp_kind.pick(l, w, t) : String}:
  match l:
    case True{}:
      %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(t), DocLines.lines.sp_proj(t), dlx.proj(t)) : {Fdl.load.run(_) == DocLines.lines.sp_kind.pick(True{}, w, t) : String}
      dlx.load(DocLines.lines.sp_proj(t))
    case False{}:
      match w:
        case True{}:
          %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(t), DocLines.lines.sp_proj(t), dlx.proj(t)) : {Fdl.write.run(_) == DocLines.lines.sp_kind.pick(False{}, True{}, t) : String}
          dlx.write(DocLines.lines.sp_proj(t))
        case False{}:
          {==}

def dlx.kind(s: String) -> {Fdl.kind(s) == DocLines.lines.sp_kind(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          dlx.pick(U32.is_eq(x, 76), U32.is_eq(x, 87), t)

def dlx.runs(r: Wr.Dec<List<&2, Dl.Run>>, +s: String) -> {Fdl.run.runs(r, s) == DocLines.lines.sp_runs(r, s) : String}:
  match r:
    case Wr.Got{+rs, +t}:
      %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(t), DocLines.lines.sp_end(t), dlx.end(t)) : {Fdl.run.carry(rs, _) == DocLines.lines.sp_runs(Wr.Got{rs, t}, s) : String}
      dlx.plan_carry(rs, DocLines.lines.sp_end(t))
    case Wr.Bad{}:
      dlx.kind(s)

def DocLines.doc_lines_ffi_exact(s):
  %Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list.start(~Dl.Run, ~Fdl.get_run, Wr.get_nat(s)), Wr.get_list.start(~Dl.Run, ~DocLines.lines.sp_run, Wr.get_nat(s)), dlx.runs_start(Wr.get_nat(s))) : {Fdl.run.runs(_, s) == DocLines.lines.sp_entry(s) : String}
  dlx.runs(Wr.get_list(~Dl.Run, ~DocLines.lines.sp_run, s), s)
