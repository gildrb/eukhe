# eukhe: lemmas of the refine_plan entry proofs: the entry's reply
# encoders are the spec spellers (rpe.*), and no reply opens with 'E'

import Base
import ../../../bend/refine_plan.bend as Rp
import ../../../bend/ffi_refine_plan.bend as FRp
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/refine_plan/entry.bend as E
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool

# Encoders
# --------

def rpe.verb(x: Rp.Verb, rest: String) -> {FRp.put_verb(x, rest) == E.rp_w_verb(x, rest) : String}:
  match x:
    case Rp.ACreate{}:
      {==}
    case Rp.AUpdate{}:
      {==}
    case Rp.ADelete{}:
      {==}

def rpe.comp(x: Rp.Comp, rest: String) -> {FRp.put_comp(x, rest) == E.rp_w_comp(x, rest) : String}:
  match x:
    case Rp.KPrompt{}:
      {==}
    case Rp.KMemory{}:
      {==}
    case Rp.KSkill{}:
      {==}
    case Rp.KSubagent{}:
      {==}
    case Rp.KFactory{}:
      {==}

def rpe.ms(m: Maybe<&2, String>, +rest: String) -> {FRp.put_ms(m, rest) == E.rp_w_ms(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def rpe.mss.items(xs: List<&2, Maybe<&2, String>>, +rest: String) -> {FRp.put_mss.items(xs, rest) == E.rp_w_mss.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +u}:
      %Equal.sym(String, FRp.put_mss.items(u, rest), E.rp_w_mss.items(u, rest), rpe.mss.items(u, rest)) : {FRp.put_ms(x, _) == E.rp_w_mss.items(x <> u, rest) : String}
      %Equal.sym(String, FRp.put_ms(x, E.rp_w_mss.items(u, rest)), E.rp_w_ms(x, E.rp_w_mss.items(u, rest)), rpe.ms(x, E.rp_w_mss.items(u, rest))) : {_ == E.rp_w_mss.items(x <> u, rest) : String}
      {==}

def rpe.mss(+xs: List<&2, Maybe<&2, String>>, +rest: String) -> {FRp.put_mss(xs, rest) == E.rp_w_mss(xs, rest) : String}:
  %Equal.sym(String, FRp.put_mss.items(xs, rest), E.rp_w_mss.items(xs, rest), rpe.mss.items(xs, rest)) : {Wr.put_nat(List.length(&2, Maybe<&2, String>, xs), _) == E.rp_w_mss(xs, rest) : String}
  {==}

def rpe.out(x: Rp.Out, +rest: String) -> {FRp.put_out(x, rest) == E.rp_w_out(x, rest) : String}:
  match x:
    case Rp.OInvalid{+v1}:
      {==}
    case Rp.ORefused{+v1}:
      {==}
    case Rp.ORemoved{}:
      {==}
    case Rp.OWritten{}:
      {==}

def rpe.row(x: Rp.Row, +rest: String) -> {FRp.put_row(x, rest) == E.rp_w_row(x, rest) : String}:
  match x:
    case Rp.Row{+v1, +v2, +v3, +v4}:
      %Equal.sym(String, FRp.put_out(v4, rest), E.rp_w_out(v4, rest), rpe.out(v4, rest)) : {FRp.put_verb(v1, FRp.put_comp(v2, Wr.put_str(v3, _))) == E.rp_w_row(Rp.Row{v1, v2, v3, v4}, rest) : String}
      %Equal.sym(String, FRp.put_comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest))), E.rp_w_comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest))), rpe.comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest)))) : {FRp.put_verb(v1, _) == E.rp_w_row(Rp.Row{v1, v2, v3, v4}, rest) : String}
      %Equal.sym(String, FRp.put_verb(v1, E.rp_w_comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest)))), E.rp_w_verb(v1, E.rp_w_comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest)))), rpe.verb(v1, E.rp_w_comp(v2, Wr.put_str(v3, E.rp_w_out(v4, rest))))) : {_ == E.rp_w_row(Rp.Row{v1, v2, v3, v4}, rest) : String}
      {==}

def rpe.rows.items(xs: List<&2, Rp.Row>, +rest: String) -> {FRp.put_rows.items(xs, rest) == E.rp_w_rows.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +u}:
      %Equal.sym(String, FRp.put_rows.items(u, rest), E.rp_w_rows.items(u, rest), rpe.rows.items(u, rest)) : {FRp.put_row(x, _) == E.rp_w_rows.items(x <> u, rest) : String}
      %Equal.sym(String, FRp.put_row(x, E.rp_w_rows.items(u, rest)), E.rp_w_row(x, E.rp_w_rows.items(u, rest)), rpe.row(x, E.rp_w_rows.items(u, rest))) : {_ == E.rp_w_rows.items(x <> u, rest) : String}
      {==}

def rpe.rows(+xs: List<&2, Rp.Row>, +rest: String) -> {FRp.put_rows(xs, rest) == E.rp_w_rows(xs, rest) : String}:
  %Equal.sym(String, FRp.put_rows.items(xs, rest), E.rp_w_rows.items(xs, rest), rpe.rows.items(xs, rest)) : {Wr.put_nat(List.length(&2, Rp.Row, xs), _) == E.rp_w_rows(xs, rest) : String}
  {==}

def rpe.strs.items(xs: List<&2, String>, +rest: String) -> {FRp.put_strs.items(xs, rest) == E.rp_w_strs.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +u}:
      %Equal.sym(String, FRp.put_strs.items(u, rest), E.rp_w_strs.items(u, rest), rpe.strs.items(u, rest)) : {Wr.put_str(x, _) == E.rp_w_strs.items(x <> u, rest) : String}
      {==}

def rpe.strs(+xs: List<&2, String>, +rest: String) -> {FRp.put_strs(xs, rest) == E.rp_w_strs(xs, rest) : String}:
  %Equal.sym(String, FRp.put_strs.items(xs, rest), E.rp_w_strs.items(xs, rest), rpe.strs.items(xs, rest)) : {Wr.put_nat(List.length(&2, String, xs), _) == E.rp_w_strs(xs, rest) : String}
  {==}

def rpe.plan(x: Rp.Plan, +rest: String) -> {FRp.put_plan(x, rest) == E.rp_w_plan(x, rest) : String}:
  match x:
    case Rp.Plan{+v1, +v2}:
      %Equal.sym(String, FRp.put_strs(v2, rest), E.rp_w_strs(v2, rest), rpe.strs(v2, rest)) : {FRp.put_rows(v1, _) == E.rp_w_plan(Rp.Plan{v1, v2}, rest) : String}
      %Equal.sym(String, FRp.put_rows(v1, E.rp_w_strs(v2, rest)), E.rp_w_rows(v1, E.rp_w_strs(v2, rest)), rpe.rows(v1, E.rp_w_strs(v2, rest))) : {_ == E.rp_w_plan(Rp.Plan{v1, v2}, rest) : String}
      {==}

def rpe.pick(x: Rp.Pick, +rest: String) -> {FRp.put_pick(x, rest) == E.rp_w_pick(x, rest) : String}:
  match x:
    case Rp.Pick{+v1, +v2}:
      %Equal.sym(String, FRp.put_verb(v2, rest), E.rp_w_verb(v2, rest), rpe.verb(v2, rest)) : {Wr.put_nat(v1, _) == E.rp_w_pick(Rp.Pick{v1, v2}, rest) : String}
      {==}

def rpe.picks.items(xs: List<&2, Rp.Pick>, +rest: String) -> {FRp.put_picks.items(xs, rest) == E.rp_w_picks.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +u}:
      %Equal.sym(String, FRp.put_picks.items(u, rest), E.rp_w_picks.items(u, rest), rpe.picks.items(u, rest)) : {FRp.put_pick(x, _) == E.rp_w_picks.items(x <> u, rest) : String}
      %Equal.sym(String, FRp.put_pick(x, E.rp_w_picks.items(u, rest)), E.rp_w_pick(x, E.rp_w_picks.items(u, rest)), rpe.pick(x, E.rp_w_picks.items(u, rest))) : {_ == E.rp_w_picks.items(x <> u, rest) : String}
      {==}

def rpe.picks(+xs: List<&2, Rp.Pick>, +rest: String) -> {FRp.put_picks(xs, rest) == E.rp_w_picks(xs, rest) : String}:
  %Equal.sym(String, FRp.put_picks.items(xs, rest), E.rp_w_picks.items(xs, rest), rpe.picks.items(xs, rest)) : {Wr.put_nat(List.length(&2, Rp.Pick, xs), _) == E.rp_w_picks(xs, rest) : String}
  {==}

def rpe.back(x: Rp.Back, +rest: String) -> {FRp.put_back(x, rest) == E.rp_w_back(x, rest) : String}:
  match x:
    case Rp.Back{+v1, +v2, +v3, +v4, +v5}:
      %Equal.sym(String, FRp.put_picks(v5, rest), E.rp_w_picks(v5, rest), rpe.picks(v5, rest)) : {Wr.put_str(v1, Wr.put_str(v2, Wr.put_str(v3, Wr.put_str(v4, _)))) == E.rp_w_back(Rp.Back{v1, v2, v3, v4, v5}, rest) : String}
      {==}

def rpe.texts(x: Rp.Texts, +rest: String) -> {FRp.put_texts(x, rest) == E.rp_w_texts(x, rest) : String}:
  match x:
    case Rp.Texts{+v1, +v2, +v3}:
      {==}

def rpe.search(x: Rp.Search, +rest: String) -> {FRp.put_search(x, rest) == E.rp_w_search(x, rest) : String}:
  match x:
    case Rp.SFull{}:
      {==}
    case Rp.SProbe{+v1, +v2, +v3}:
      {==}
    case Rp.SFinal{}:
      {==}

def rpe.step(x: Rp.Step, +rest: String) -> {FRp.put_step(x, rest) == E.rp_w_step(x, rest) : String}:
  match x:
    case Rp.TTry{+v1, +v2}:
      %Equal.sym(String, FRp.put_search(v2, rest), E.rp_w_search(v2, rest), rpe.search(v2, rest)) : {Wr.put_nat(0n, Wr.put_nat(v1, _)) == E.rp_w_step(Rp.TTry{v1, v2}, rest) : String}
      {==}
    case Rp.TOk{+v1}:
      {==}
    case Rp.TNo{+v1}:
      {==}

# Replies never open with 'E'
# ---------------------------

def rpe.plan_ok(p: Rp.Plan) -> {LawsBase.wire_opens_err(FRp.put_plan(p, "")) == False{} : Bool}:
  match p:
    case Rp.Plan{+rows, cs}:
      Wire.wire_nat_not_err(List.length(&2, Rp.Row, rows), FRp.put_rows.items(rows, FRp.put_strs(cs, "")))

def rpe.back_ok(b: Rp.Back) -> {LawsBase.wire_opens_err(FRp.put_back(b, "")) == False{} : Bool}:
  match b:
    case Rp.Back{su, ra, ou, re, pi}:
      LE.dcw.sfin_ok(Wr.put_str.go(su, SNil{}, 0n), Wr.put_str(ra, Wr.put_str(ou, Wr.put_str(re, FRp.put_picks(pi, "")))))

def rpe.texts_ok(x: Rp.Texts) -> {LawsBase.wire_opens_err(FRp.put_texts(x, "")) == False{} : Bool}:
  match x:
    case Rp.Texts{su, ra, ou}:
      LE.dcw.sfin_ok(Wr.put_str.go(su, SNil{}, 0n), Wr.put_str(ra, Wr.put_str(ou, "")))

def rpe.step_ok(x: Rp.Step) -> {LawsBase.wire_opens_err(FRp.put_step(x, "")) == False{} : Bool}:
  match x:
    case Rp.TTry{n, st}:
      {==}
    case Rp.TOk{n}:
      {==}
    case Rp.TNo{t}:
      {==}

# every answer opens with a count, a length, a tag or a Bool: never 'E'
def rpe.reply_ok(q: FRp.Req) -> {LawsBase.wire_opens_err(FRp.answer(q)) == False{} : Bool}:
  match q:
    case FRp.QIds{+eds}:
      Wire.wire_nat_not_err(List.length(&2, Maybe<&2, String>, Rp.ids(eds)), FRp.put_mss.items(Rp.ids(eds), ""))
    case FRp.QPlan{o, eds}:
      rpe.plan_ok(Rp.plan(o, eds))
    case FRp.QBack{id, was}:
      rpe.back_ok(Rp.back(id, was))
    case FRp.QNorm{s, r, o}:
      rpe.texts_ok(Rp.norm(s, r, o))
    case FRp.QScan{t}:
      Wire.wire_bool_not_err(Rp.incomplete(t), "")
    case FRp.QFit{w, c, st, p}:
      rpe.step_ok(Rp.fit(w, c, st, p))
