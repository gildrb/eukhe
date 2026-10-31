# eukhe: lemmas the proofs of area autoresearch share: the stepper entry
# bend/ffi_autoresearch.bend
#
# The entry spells replies as the laws do (ae.snap, ae.serve); the entry
# reads back every request the laws spell that fits the wire (ae.req).

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/ffi_autoresearch.bend as FAr
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../bend/autoresearch/stats.bend as ArT
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/autoresearch/model.bend as ArM
import ../../../laws/autoresearch/entry.bend as ArE
import ../../wire/wire_strs_spells.bend as PWStrsSpells
import ../../wire/wire_nats_spells.bend as PWNatsSpells
import ../../wire/wire_bool_round_trip.bend as PWBoolRt
import ../../wire/wire_strs_round_trip.bend as PWStrsRt
import ../../base/logic/bool.bend as LLogicBool

# Logic
# -----

def ae.l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  LLogicBool.wr_and_l(a, b, e)

def ae.r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  LLogicBool.wr_and_r(a, b, e)

def ae.and(+a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# The replies
# -----------

def ae.mnat(m: Maybe<&2, Nat>, -rest: String) -> {ArE.ar_w_mnat(m, rest) == FAr.put_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def ae.mode(m: ArS.Mode, -rest: String) -> {Wr.put_nat(ArE.ar_w_mode(m), rest) == FAr.put_mode(m, rest) : String}:
  match m:
    case ArS.On{}:
      {==}
    case ArS.Off{}:
      {==}

def ae.dir(d: ArS.Dir, -rest: String) -> {Wr.put_nat(ArE.ar_w_dir(d), rest) == FAr.put_dir(d, rest) : String}:
  match d:
    case ArS.Lower{}:
      {==}
    case ArS.Higher{}:
      {==}

def ae.mstatus(m: Maybe<&2, ArS.Status>, -rest: String) -> {ArE.ar_w_mstatus(m, rest) == FAr.put_mstatus(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case ArS.Keep{}:
          {==}
        case ArS.Discard{}:
          {==}
        case ArS.Crash{}:
          {==}
        case ArS.Checks{}:
          {==}

def ae.strs(+xs: List<&2, String>, rest: String) -> {LawsBase.wire_spell_strs(xs, rest) == FAr.put_strs(xs, rest) : String}:
  +r = rest
  Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), LawsBase.wire_spell_strs(xs, r), Wire.wire_strs_spells(xs, r))

def ae.cfg(c: ArS.Cfg, +rest: String) -> {ArE.ar_w_cfg(c, rest) == FAr.put_cfg(c, rest) : String}:
  match c:
    case ArS.Cfg{+a, +b, +m, +u, +d, +sec, +scope, +off, +max}:
      %ae.mnat(max, rest) : {ArE.ar_w_cfg(ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest) == Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, FAr.put_dir(d, FAr.put_strs(sec, FAr.put_strs(scope, FAr.put_strs(off, _)))))))) : String}
      %ae.strs(off, ArE.ar_w_mnat(max, rest)) : {ArE.ar_w_cfg(ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest) == Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, FAr.put_dir(d, FAr.put_strs(sec, FAr.put_strs(scope, _))))))) : String}
      %ae.strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest))) : {ArE.ar_w_cfg(ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest) == Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, FAr.put_dir(d, FAr.put_strs(sec, _)))))) : String}
      %ae.strs(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest)))) : {ArE.ar_w_cfg(ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest) == Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, FAr.put_dir(d, _))))) : String}
      %ae.dir(d, LawsBase.wire_spell_strs(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest))))) : {ArE.ar_w_cfg(ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest) == Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, _)))) : String}
      {==}

def ae.mcfg(m: Maybe<&2, ArS.Cfg>, +rest: String) -> {ArE.ar_w_mcfg(m, rest) == FAr.put_mcfg(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Equal.cong(String, String, x => Wr.put_nat(1n, x), ArE.ar_w_cfg(c, rest), FAr.put_cfg(c, rest), ae.cfg(c, rest))

def ae.dec(d: ArD.Dec, +rest: String) -> {ArE.ar_w_dec(d, rest) == FAr.put_dec(d, rest) : String}:
  match d:
    case ArD.Dec{+neg, +ds, +scale}:
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, ds, Wr.put_nat(scale, rest)), LawsBase.wire_spell_nats(ds, Wr.put_nat(scale, rest)), Wire.wire_nats_spells(ds, Wr.put_nat(scale, rest))) : {ArE.ar_w_dec(ArD.Dec{neg, ds, scale}, rest) == Wr.put_bool(neg, _) : String}
      {==}

def ae.mdec(m: Maybe<&2, ArD.Dec>, +rest: String) -> {ArE.ar_w_mdec(m, rest) == FAr.put_mdec(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      Equal.cong(String, String, x => Wr.put_nat(1n, x), ArE.ar_w_dec(d, rest), FAr.put_dec(d, rest), ae.dec(d, rest))

def ae.kvs_items(kvs: List<&2, ArL.Kv>, +rest: String) -> {Wr.put_list.go(~ArL.Kv, ~FAr.put_kv, kvs, rest) == (List.length(&2, ArL.Kv, kvs), ArE.ar_w_kvs.items(kvs, rest)) : Nat & String}:
  match kvs:
    case Nil{}:
      {==}
    case ArL.Kv{+n, +v} <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~ArL.Kv, ~FAr.put_kv, t, rest), (List.length(&2, ArL.Kv, t), ArE.ar_w_kvs.items(t, rest)), ae.kvs_items(t, rest)) : {Wr.put_list.step(~ArL.Kv, ~FAr.put_kv, ArL.Kv{n, v}, _) == (1n+List.length(&2, ArL.Kv, t), Wr.put_str(n, ArE.ar_w_dec(v, ArE.ar_w_kvs.items(t, rest)))) : Nat & String}
      %ae.dec(v, ArE.ar_w_kvs.items(t, rest)) : {(1n+List.length(&2, ArL.Kv, t), Wr.put_str(n, _)) == (1n+List.length(&2, ArL.Kv, t), Wr.put_str(n, ArE.ar_w_dec(v, ArE.ar_w_kvs.items(t, rest)))) : Nat & String}
      {==}

def ae.kvs(+kvs: List<&2, ArL.Kv>, +rest: String) -> {ArE.ar_w_kvs(kvs, rest) == FAr.put_kvs(kvs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~ArL.Kv, ~FAr.put_kv, kvs, rest), (List.length(&2, ArL.Kv, kvs), ArE.ar_w_kvs.items(kvs, rest)), ae.kvs_items(kvs, rest)) : {ArE.ar_w_kvs(kvs, rest) == Wr.put_list.fin(_) : String}
  {==}

def ae.row(+ab: Bool, r: ArS.Row, +rest: String) -> {ArE.ar_w_row(ab, r, rest) == FAr.put_row(ab, r, rest) : String}:
  match r:
    case ArS.Row{+id, +sg, +st, +m, +ms, +ps, +fn, +fl, +desc}:
      %ae.kvs(ms, Wr.put_bool(ps, Wr.put_bool(fl, Wr.put_str(desc, rest)))) : {ArE.ar_w_row(ab, ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}, rest) == Wr.put_nat(id, Wr.put_nat(sg, FAr.put_mstatus(st, Wr.put_bool(ab, Wr.put_bool(fn, FAr.put_mdec(m, _)))))) : String}
      %ae.mdec(m, ArE.ar_w_kvs(ms, Wr.put_bool(ps, Wr.put_bool(fl, Wr.put_str(desc, rest))))) : {ArE.ar_w_row(ab, ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}, rest) == Wr.put_nat(id, Wr.put_nat(sg, FAr.put_mstatus(st, Wr.put_bool(ab, Wr.put_bool(fn, _))))) : String}
      %ae.mstatus(st, Wr.put_bool(ab, Wr.put_bool(fn, ArE.ar_w_mdec(m, ArE.ar_w_kvs(ms, Wr.put_bool(ps, Wr.put_bool(fl, Wr.put_str(desc, rest)))))))) : {ArE.ar_w_row(ab, ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}, rest) == Wr.put_nat(id, Wr.put_nat(sg, _)) : String}
      {==}

def ae.ended(r: ArS.Row, +rest: String) -> {ArE.ar_w_row(ArE.ar_ended_abandoned(r), r, rest) == FAr.put_ended(r, rest) : String}:
  match r:
    case ArS.Row{+id, +sg, +st, +m, +ms, +ps, +fn, +fl, +desc}:
      ae.row(Bool.not(ArS.has(st)), ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}, rest)

def ae.items(rs: List<&2, ArS.Row>, +rest: String) -> {ArE.ar_w_rows.items(rs, rest) == FAr.put_rows.go(rs, rest) : String}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      %ae.items(t, rest) : {ArE.ar_w_row(ArE.ar_ended_abandoned(r), r, ArE.ar_w_rows.items(t, rest)) == FAr.put_ended(r, _) : String}
      ae.ended(r, ArE.ar_w_rows.items(t, rest))

def ae.count(rs: List<&2, ArS.Row>) -> {ArM.ar_count_runs(rs) == ArS.rlen(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      %ae.count(t) : {1n+ArM.ar_count_runs(t) == 1n+_ : Nat}
      {==}

def ae.name(c: Maybe<&2, ArS.Cfg>) -> {ArM.ar_name(c) == ArS.primary(c) : String}:
  match c:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case ArS.Cfg{a, b, m, u, d, sec, scope, off, max}:
          {==}

def ae.prow(+c: Maybe<&2, ArS.Cfg>, +seg: Nat, p: ArS.Pend) -> {ArM.ar_row(c, seg, p, None{}, "") == ArS.row(ArS.primary(c), seg, p, None{}, "") : ArS.Row}:
  match p:
    case ArS.Pend{+id, +kvs, fin}:
      match fin:
        case None{}:
          %ae.name(c) : {ArM.ar_row(c, seg, ArS.Pend{id, kvs, None{}}, None{}, "") == ArS.row(_, seg, ArS.Pend{id, kvs, None{}}, None{}, "") : ArS.Row}
          {==}
        case Some{+f}:
          %ae.name(c) : {ArM.ar_row(c, seg, ArS.Pend{id, kvs, Some{f}}, None{}, "") == ArS.row(_, seg, ArS.Pend{id, kvs, Some{f}}, None{}, "") : ArS.Row}
          {==}

def ae.rows(+c: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, +rest: String) -> {ArE.ar_w_rows(ArS.St{c, seg, mode, runs, pend}, rest) == FAr.put_rows(ArS.primary(c), seg, runs, pend, rest) : String}:
  match pend:
    case None{}:
      %ae.count(runs) : {Wr.put_nat(ArM.ar_count_runs(runs), ArE.ar_w_rows.items(runs, rest)) == Wr.put_nat(_, FAr.put_rows.go(runs, rest)) : String}
      %ae.items(runs, rest) : {Wr.put_nat(ArM.ar_count_runs(runs), ArE.ar_w_rows.items(runs, rest)) == Wr.put_nat(ArM.ar_count_runs(runs), _) : String}
      {==}
    case Some{+p}:
      %ae.count(runs) : {ArE.ar_w_rows(ArS.St{c, seg, mode, runs, Some{p}}, rest) == Wr.put_nat(1n+_, FAr.put_rows.go(runs, FAr.put_row(False{}, ArS.row(ArS.primary(c), seg, p, None{}, ""), rest))) : String}
      %ae.prow(c, seg, p) : {ArE.ar_w_rows(ArS.St{c, seg, mode, runs, Some{p}}, rest) == Wr.put_nat(1n+ArM.ar_count_runs(runs), FAr.put_rows.go(runs, FAr.put_row(False{}, _, rest))) : String}
      %ae.row(False{}, ArM.ar_row(c, seg, p, None{}, ""), rest) : {ArE.ar_w_rows(ArS.St{c, seg, mode, runs, Some{p}}, rest) == Wr.put_nat(1n+ArM.ar_count_runs(runs), FAr.put_rows.go(runs, _)) : String}
      %ae.items(runs, ArE.ar_w_row(False{}, ArM.ar_row(c, seg, p, None{}, ""), rest)) : {ArE.ar_w_rows(ArS.St{c, seg, mode, runs, Some{p}}, rest) == Wr.put_nat(1n+ArM.ar_count_runs(runs), _) : String}
      {==}

def ae.mpend(p: Maybe<&2, ArS.Pend>, -rest: String) -> {ArE.ar_w_mnat(ArE.ar_mpending(p), rest) == FAr.put_mnat(FAr.pending(p), rest) : String}:
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case ArS.Pend{id, kvs, fin}:
          {==}

# the snapshot's tail after the best: the logged count and the confidence
def ae.sx1(+runs: List<&2, ArS.Row>, +seg: Nat, conf: Maybe<&2, Nat>) -> String:
  Wr.put_nat(ArS.logged(runs, seg), ArE.ar_w_mnat(conf, ""))

# ... from the pending id on
def ae.sx3(+c: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>) -> String:
  ArE.ar_w_mnat(ArE.ar_mpending(pend), ArE.ar_w_mdec(ArS.first(runs, seg), ArE.ar_w_mdec(ArS.last(runs, seg), ae.sx1(runs, seg, ArT.St.confidence(ArS.St{c, seg, mode, runs, pend})))))

# the entry spells the snapshot as the laws do
def ae.snap(s: ArS.St) -> {ArE.ar_w_snap(s) == FAr.put_snap(s) : String}:
  match s:
    case ArS.St{+c, +seg, +mode, +runs, +pend}:
      %ae.mnat(ArT.St.confidence(ArS.St{c, seg, mode, runs, pend}), "") : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, FAr.put_mode(mode, FAr.put_rows(ArS.primary(c), seg, runs, pend, FAr.put_mnat(FAr.pending(pend), FAr.put_mdec(ArS.first(runs, seg), FAr.put_mdec(ArS.last(runs, seg), Wr.put_nat(ArS.logged(runs, seg), _)))))))) : String}
      %ae.mdec(ArS.last(runs, seg), ae.sx1(runs, seg, ArT.St.confidence(ArS.St{c, seg, mode, runs, pend}))) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, FAr.put_mode(mode, FAr.put_rows(ArS.primary(c), seg, runs, pend, FAr.put_mnat(FAr.pending(pend), FAr.put_mdec(ArS.first(runs, seg), _)))))) : String}
      %ae.mdec(ArS.first(runs, seg), ArE.ar_w_mdec(ArS.last(runs, seg), ae.sx1(runs, seg, ArT.St.confidence(ArS.St{c, seg, mode, runs, pend})))) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, FAr.put_mode(mode, FAr.put_rows(ArS.primary(c), seg, runs, pend, FAr.put_mnat(FAr.pending(pend), _))))) : String}
      %ae.mpend(pend, ArE.ar_w_mdec(ArS.first(runs, seg), ArE.ar_w_mdec(ArS.last(runs, seg), ae.sx1(runs, seg, ArT.St.confidence(ArS.St{c, seg, mode, runs, pend}))))) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, FAr.put_mode(mode, FAr.put_rows(ArS.primary(c), seg, runs, pend, _)))) : String}
      %ae.rows(c, seg, mode, runs, pend, ae.sx3(c, seg, mode, runs, pend)) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, FAr.put_mode(mode, _))) : String}
      %ae.mode(mode, ArE.ar_w_rows(ArS.St{c, seg, mode, runs, pend}, ae.sx3(c, seg, mode, runs, pend))) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == FAr.put_mcfg(c, Wr.put_nat(seg, _)) : String}
      %ae.mcfg(c, Wr.put_nat(seg, Wr.put_nat(ArE.ar_w_mode(mode), ArE.ar_w_rows(ArS.St{c, seg, mode, runs, pend}, ae.sx3(c, seg, mode, runs, pend))))) : {ArE.ar_w_snap(ArS.St{c, seg, mode, runs, pend}) == _ : String}
      {==}

def ae.answer(r: ArS.Res, +s: ArS.St) -> {FAr.answer(r, s) == (FAr.Live{ArM.ar_after(r, s)}, ArE.ar_w_res(r)) : FAr.St & String}:
  match r:
    case ArS.Took{s2, e, stop}:
      match e:
        case ArS.Nothing{}:
          {==}
        case ArS.Commit{}:
          {==}
        case ArS.Reset{}:
          {==}
    case ArS.Refuse{t}:
      {==}

# a whole request runs as the laws' model asks
def ae.serve(+s: ArS.St, q: FAr.Q) -> {FAr.serve(s, q) == (FAr.Live{ArE.ar_next(s, q)}, ArE.ar_reply(s, q)) : FAr.St & String}:
  match q:
    case FAr.QEv{e}:
      ae.answer(ArP.step(s, e), s)
    case FAr.QSnap{}:
      Equal.cong(String, FAr.St & String, x => (FAr.Live{s}, x), FAr.put_snap(s), ArE.ar_w_snap(s), Equal.sym(String, ArE.ar_w_snap(s), FAr.put_snap(s), ae.snap(s)))

# Spelled requests read back
# --------------------------

def ae.rn(+n: Nat, rest: String, f: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  +r = rest
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r)), Wr.Got{n, r}, Wire.wire_nat_round_trip(n, r, f))

def ae.rs(+a: String, rest: String, f: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  +r = rest
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, r)), Wr.Got{a, r}, Wire.wire_str_round_trip(a, r, f))

def ae.rb(+b: Bool, rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  +r = rest
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, r)), Wr.Got{b, r}, Wire.wire_bool_round_trip(b, r))

def ae.rss(+xs: List<&2, String>, rest: String, f: {LawsBase.wire_strs_fit(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == FAr.get_strs(LawsBase.wire_spell_strs(xs, rest)) : Wr.Dec<List<&2, String>>}:
  +r = rest
  Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(xs, r)), Wr.Got{xs, r}, Wire.wire_strs_round_trip(xs, r, f))

def ae.rdir(d: ArS.Dir, +rest: String) -> {Wr.Got{d, rest} == FAr.get_dir(Wr.get_nat(Wr.put_nat(ArE.ar_w_dir(d), rest))) : Wr.Dec<ArS.Dir>}:
  match d:
    case ArS.Lower{}:
      %ae.rn(0n, rest, {==}) : {Wr.Got{ArS.Lower{}, rest} == FAr.get_dir(_) : Wr.Dec<ArS.Dir>}
      {==}
    case ArS.Higher{}:
      %ae.rn(1n, rest, {==}) : {Wr.Got{ArS.Higher{}, rest} == FAr.get_dir(_) : Wr.Dec<ArS.Dir>}
      {==}

def ae.rmode(m: ArS.Mode, +rest: String) -> {Wr.Got{m, rest} == FAr.get_mode(Wr.get_nat(Wr.put_nat(ArE.ar_w_mode(m), rest))) : Wr.Dec<ArS.Mode>}:
  match m:
    case ArS.On{}:
      %ae.rn(0n, rest, {==}) : {Wr.Got{ArS.On{}, rest} == FAr.get_mode(_) : Wr.Dec<ArS.Mode>}
      {==}
    case ArS.Off{}:
      %ae.rn(1n, rest, {==}) : {Wr.Got{ArS.Off{}, rest} == FAr.get_mode(_) : Wr.Dec<ArS.Mode>}
      {==}

def ae.rstatus(t: ArS.Status, +rest: String) -> {Wr.Got{t, rest} == FAr.get_status(Wr.get_nat(Wr.put_nat(ArE.ar_w_status(t), rest))) : Wr.Dec<ArS.Status>}:
  match t:
    case ArS.Keep{}:
      %ae.rn(0n, rest, {==}) : {Wr.Got{ArS.Keep{}, rest} == FAr.get_status(_) : Wr.Dec<ArS.Status>}
      {==}
    case ArS.Discard{}:
      %ae.rn(1n, rest, {==}) : {Wr.Got{ArS.Discard{}, rest} == FAr.get_status(_) : Wr.Dec<ArS.Status>}
      {==}
    case ArS.Crash{}:
      %ae.rn(2n, rest, {==}) : {Wr.Got{ArS.Crash{}, rest} == FAr.get_status(_) : Wr.Dec<ArS.Status>}
      {==}
    case ArS.Checks{}:
      %ae.rn(3n, rest, {==}) : {Wr.Got{ArS.Checks{}, rest} == FAr.get_status(_) : Wr.Dec<ArS.Status>}
      {==}

def ae.rmnat(m: Maybe<&2, Nat>, +rest: String, f: {ArE.ar_fits_mnat(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FAr.get_mnat(Wr.get_nat(ArE.ar_w_mnat(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %ae.rn(0n, rest, {==}) : {Wr.Got{None{}, rest} == FAr.get_mnat(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+n}:
      %ae.rn(1n, Wr.put_nat(n, rest), {==}) : {Wr.Got{Some{n}, rest} == FAr.get_mnat(_) : Wr.Dec<Maybe<&2, Nat>>}
      %ae.rn(n, rest, f) : {Wr.Got{Some{n}, rest} == FAr.get_maybe.some(Nat, _) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def ae.rmstr(m: Maybe<&2, String>, +rest: String, f: {ArE.ar_fits_mstr(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FAr.get_mstr(Wr.get_nat(ArE.ar_w_mstr(m, rest))) : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      %ae.rn(0n, rest, {==}) : {Wr.Got{None{}, rest} == FAr.get_mstr(_) : Wr.Dec<Maybe<&2, String>>}
      {==}
    case Some{+t}:
      %ae.rn(1n, Wr.put_str(t, rest), {==}) : {Wr.Got{Some{t}, rest} == FAr.get_mstr(_) : Wr.Dec<Maybe<&2, String>>}
      %ae.rs(t, rest, f) : {Wr.Got{Some{t}, rest} == FAr.get_maybe.some(String, _) : Wr.Dec<Maybe<&2, String>>}
      {==}

# the spelling of a configuration from its direction on
def ae.x4(+d: ArS.Dir, +sec: List<&2, String>, +scope: List<&2, String>, +off: List<&2, String>, max: Maybe<&2, Nat>, rest: String) -> String:
  Wr.put_nat(ArE.ar_w_dir(d), LawsBase.wire_spell_strs(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest)))))

def ae.rcfg(c: ArS.Cfg, +rest: String, +f: {ArE.ar_fits_cfg(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FAr.get_cfg(ArE.ar_w_cfg(c, rest)) : Wr.Dec<ArS.Cfg>}:
  match c:
    case ArS.Cfg{+a, +b, +m, +u, +d, +sec, +scope, +off, +max}:
      +fA = ae.l(Bool.and(ArE.ar_fits_str(a), Bool.and(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u)))), Bool.and(Bool.and(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off))), ArE.ar_fits_mnat(max)), f)
      +fB = ae.r(Bool.and(ArE.ar_fits_str(a), Bool.and(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u)))), Bool.and(Bool.and(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off))), ArE.ar_fits_mnat(max)), f)
      +fbmu = ae.r(ArE.ar_fits_str(a), Bool.and(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u))), fA)
      +fmu = ae.r(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u)), fbmu)
      +fL = ae.l(Bool.and(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off))), ArE.ar_fits_mnat(max), fB)
      +fso = ae.r(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off)), fL)
      %ae.rs(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, ae.x4(d, sec, scope, off, max, rest)))), ae.l(ArE.ar_fits_str(a), Bool.and(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u))), fA)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.name(_) : Wr.Dec<ArS.Cfg>}
      %ae.rs(b, Wr.put_str(m, Wr.put_str(u, ae.x4(d, sec, scope, off, max, rest))), ae.l(ArE.ar_fits_str(b), Bool.and(ArE.ar_fits_str(m), ArE.ar_fits_str(u)), fbmu)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.goal(a, _) : Wr.Dec<ArS.Cfg>}
      %ae.rs(m, Wr.put_str(u, ae.x4(d, sec, scope, off, max, rest)), ae.l(ArE.ar_fits_str(m), ArE.ar_fits_str(u), fmu)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.metric(a, b, _) : Wr.Dec<ArS.Cfg>}
      %ae.rs(u, ae.x4(d, sec, scope, off, max, rest), ae.r(ArE.ar_fits_str(m), ArE.ar_fits_str(u), fmu)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.unit(a, b, m, _) : Wr.Dec<ArS.Cfg>}
      %ae.rdir(d, LawsBase.wire_spell_strs(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest))))) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.dir(a, b, m, u, _) : Wr.Dec<ArS.Cfg>}
      %ae.rss(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest))), ae.l(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off)), fL)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.sec(a, b, m, u, d, _) : Wr.Dec<ArS.Cfg>}
      %ae.rss(scope, LawsBase.wire_spell_strs(off, ArE.ar_w_mnat(max, rest)), ae.l(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off), fso)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.scope(a, b, m, u, d, sec, _) : Wr.Dec<ArS.Cfg>}
      %ae.rss(off, ArE.ar_w_mnat(max, rest), ae.r(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off), fso)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.off(a, b, m, u, d, sec, scope, _) : Wr.Dec<ArS.Cfg>}
      %ae.rmnat(max, rest, ae.r(Bool.and(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off))), ArE.ar_fits_mnat(max), fB)) : {Wr.Got{ArS.Cfg{a, b, m, u, d, sec, scope, off, max}, rest} == FAr.get_cfg.max(a, b, m, u, d, sec, scope, off, _) : Wr.Dec<ArS.Cfg>}
      {==}

# the entry reads back every request the laws spell that fits the wire
def ae.req(q: FAr.Q, +f: {ArE.ar_fits(q) == True{} : Bool}) -> {Wr.Got{q, ""} == FAr.get_q(ArE.ar_w_req(q)) : Wr.Dec<FAr.Q>}:
  match q:
    case FAr.QEv{e}:
      match e:
        case ArS.Init{+c, +fresh, +harness}:
          %ae.rn(0n, ArE.ar_w_cfg(c, Wr.put_bool(fresh, Wr.put_bool(harness, ""))), {==}) : {Wr.Got{FAr.QEv{ArS.Init{c, fresh, harness}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rcfg(c, Wr.put_bool(fresh, Wr.put_bool(harness, "")), f) : {Wr.Got{FAr.QEv{ArS.Init{c, fresh, harness}}, ""} == FAr.get_init(_) : Wr.Dec<FAr.Q>}
          %ae.rb(fresh, Wr.put_bool(harness, "")) : {Wr.Got{FAr.QEv{ArS.Init{c, fresh, harness}}, ""} == FAr.get_init.fresh(c, _) : Wr.Dec<FAr.Q>}
          %ae.rb(harness, "") : {Wr.Got{FAr.QEv{ArS.Init{c, fresh, harness}}, ""} == FAr.get_init.harness(c, fresh, _) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.Begin{+n}:
          %ae.rn(1n, Wr.put_nat(n, ""), {==}) : {Wr.Got{FAr.QEv{ArS.Begin{n}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rn(n, "", f) : {Wr.Got{FAr.QEv{ArS.Begin{n}}, ""} == FAr.get_begin(_) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.Line{+t}:
          %ae.rn(2n, Wr.put_str(t, ""), {==}) : {Wr.Got{FAr.QEv{ArS.Line{t}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rs(t, "", f) : {Wr.Got{FAr.QEv{ArS.Line{t}}, ""} == FAr.get_line(_) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.Finish{+neg, +code, +timeout}:
          %ae.rn(3n, Wr.put_bool(neg, Wr.put_nat(code, Wr.put_bool(timeout, ""))), {==}) : {Wr.Got{FAr.QEv{ArS.Finish{neg, code, timeout}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rb(neg, Wr.put_nat(code, Wr.put_bool(timeout, ""))) : {Wr.Got{FAr.QEv{ArS.Finish{neg, code, timeout}}, ""} == FAr.get_finish(_) : Wr.Dec<FAr.Q>}
          %ae.rn(code, Wr.put_bool(timeout, ""), f) : {Wr.Got{FAr.QEv{ArS.Finish{neg, code, timeout}}, ""} == FAr.get_finish.code(neg, _) : Wr.Dec<FAr.Q>}
          %ae.rb(timeout, "") : {Wr.Got{FAr.QEv{ArS.Finish{neg, code, timeout}}, ""} == FAr.get_finish.timeout(neg, code, _) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.Log{+st, +desc, +why, +devs}:
          +fw = ae.r(ArE.ar_fits_str(desc), Bool.and(ArE.ar_fits_mstr(why), LawsBase.wire_fits(devs)), f)
          %ae.rn(4n, Wr.put_nat(ArE.ar_w_status(st), Wr.put_str(desc, ArE.ar_w_mstr(why, Wr.put_nat(devs, "")))), {==}) : {Wr.Got{FAr.QEv{ArS.Log{st, desc, why, devs}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rstatus(st, Wr.put_str(desc, ArE.ar_w_mstr(why, Wr.put_nat(devs, "")))) : {Wr.Got{FAr.QEv{ArS.Log{st, desc, why, devs}}, ""} == FAr.get_log(_) : Wr.Dec<FAr.Q>}
          %ae.rs(desc, ArE.ar_w_mstr(why, Wr.put_nat(devs, "")), ae.l(ArE.ar_fits_str(desc), Bool.and(ArE.ar_fits_mstr(why), LawsBase.wire_fits(devs)), f)) : {Wr.Got{FAr.QEv{ArS.Log{st, desc, why, devs}}, ""} == FAr.get_log.desc(st, _) : Wr.Dec<FAr.Q>}
          %ae.rmstr(why, Wr.put_nat(devs, ""), ae.l(ArE.ar_fits_mstr(why), LawsBase.wire_fits(devs), fw)) : {Wr.Got{FAr.QEv{ArS.Log{st, desc, why, devs}}, ""} == FAr.get_log.why(st, desc, _) : Wr.Dec<FAr.Q>}
          %ae.rn(devs, "", ae.r(ArE.ar_fits_mstr(why), LawsBase.wire_fits(devs), fw)) : {Wr.Got{FAr.QEv{ArS.Log{st, desc, why, devs}}, ""} == FAr.get_log.devs(st, desc, why, _) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.Flag{+n, +reason}:
          +fr = f
          %ae.rn(5n, Wr.put_nat(n, Wr.put_str(reason, "")), {==}) : {Wr.Got{FAr.QEv{ArS.Flag{n, reason}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rn(n, Wr.put_str(reason, ""), ae.l(LawsBase.wire_fits(n), ArE.ar_fits_str(reason), fr)) : {Wr.Got{FAr.QEv{ArS.Flag{n, reason}}, ""} == FAr.get_flag(_) : Wr.Dec<FAr.Q>}
          %ae.rs(reason, "", ae.r(LawsBase.wire_fits(n), ArE.ar_fits_str(reason), fr)) : {Wr.Got{FAr.QEv{ArS.Flag{n, reason}}, ""} == FAr.get_flag.reason(n, _) : Wr.Dec<FAr.Q>}
          {==}
        case ArS.SetMode{+m}:
          %ae.rn(6n, Wr.put_nat(ArE.ar_w_mode(m), ""), {==}) : {Wr.Got{FAr.QEv{ArS.SetMode{m}}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
          %ae.rmode(m, "") : {Wr.Got{FAr.QEv{ArS.SetMode{m}}, ""} == FAr.get_set_mode(_) : Wr.Dec<FAr.Q>}
          {==}
    case FAr.QSnap{}:
      %ae.rn(7n, "", {==}) : {Wr.Got{FAr.QSnap{}, ""} == FAr.get_q.go(_) : Wr.Dec<FAr.Q>}
      {==}
