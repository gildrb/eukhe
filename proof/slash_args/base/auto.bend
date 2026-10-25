# eukhe: lemmas of area slash_args: the `/autonomous` answer of
# bend/slash_args.bend is the spec helper's of laws/slash_args/model.bend
# (each option, the reads of the words by induction on them, the options
# as `/autonomous on` takes them, the keywords)

import Base
import ../../../bend/slash_args.bend as Sa
import ../../../laws/slash_args/model.bend as SlashArgs
import ./text.bend as LT

# Options
# -------

def saa.later(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, A>) -> {Sa.later(A, a, b) == SlashArgs.sa_later(A, a, b) : Maybe<&2, A>}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      {==}

def saa.then(a: Sa.Opts, b: Sa.Opts) -> {Sa.opts.then(a, b) == SlashArgs.sa_opts.then(a, b) : Sa.Opts}:
  match a:
    case Sa.Opts{+c1, +t1, +k1, +m1, g1, d1, +r1, +s1, +p1}:
      match b:
        case Sa.Opts{+c2, +t2, +k2, +m2, g2, d2, +r2, +s2, +p2}:
          %Equal.sym(Maybe<&2, Sa.Lim>, Sa.later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, c1, c2), saa.later(Sa.Lim, c1, c2)) : {Sa.Opts{_, Sa.later(Sa.Lim, t1, t2), Sa.later(Sa.Lim, k1, k2), Sa.later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), Sa.later(String, r1, r2), Sa.later(String, s1, s2), Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, Sa.Lim>, Sa.later(Sa.Lim, t1, t2), SlashArgs.sa_later(Sa.Lim, t1, t2), saa.later(Sa.Lim, t1, t2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), _, Sa.later(Sa.Lim, k1, k2), Sa.later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), Sa.later(String, r1, r2), Sa.later(String, s1, s2), Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, Sa.Lim>, Sa.later(Sa.Lim, k1, k2), SlashArgs.sa_later(Sa.Lim, k1, k2), saa.later(Sa.Lim, k1, k2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, t1, t2), _, Sa.later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), Sa.later(String, r1, r2), Sa.later(String, s1, s2), Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, Sa.Lim>, Sa.later(Sa.Lim, m1, m2), SlashArgs.sa_later(Sa.Lim, m1, m2), saa.later(Sa.Lim, m1, m2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, t1, t2), SlashArgs.sa_later(Sa.Lim, k1, k2), _, List.append(&2, String, g1, g2), Bool.or(d1, d2), Sa.later(String, r1, r2), Sa.later(String, s1, s2), Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, String>, Sa.later(String, r1, r2), SlashArgs.sa_later(String, r1, r2), saa.later(String, r1, r2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, t1, t2), SlashArgs.sa_later(Sa.Lim, k1, k2), SlashArgs.sa_later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), _, Sa.later(String, s1, s2), Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, String>, Sa.later(String, s1, s2), SlashArgs.sa_later(String, s1, s2), saa.later(String, s1, s2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, t1, t2), SlashArgs.sa_later(Sa.Lim, k1, k2), SlashArgs.sa_later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), SlashArgs.sa_later(String, r1, r2), _, Sa.later(String, p1, p2)} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          %Equal.sym(Maybe<&2, String>, Sa.later(String, p1, p2), SlashArgs.sa_later(String, p1, p2), saa.later(String, p1, p2)) : {Sa.Opts{SlashArgs.sa_later(Sa.Lim, c1, c2), SlashArgs.sa_later(Sa.Lim, t1, t2), SlashArgs.sa_later(Sa.Lim, k1, k2), SlashArgs.sa_later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), SlashArgs.sa_later(String, r1, r2), SlashArgs.sa_later(String, s1, s2), _} == SlashArgs.sa_opts.then(Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}, Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}) : Sa.Opts}
          {==}

def saa.read_then(a: Sa.Read, b: Sa.Read) -> {Sa.read.then(a, b) == SlashArgs.sa_read.then(a, b) : Sa.Read}:
  match a:
    case Sa.ROk{+x}:
      match b:
        case Sa.ROk{+y}:
          %Equal.sym(Sa.Opts, Sa.opts.then(x, y), SlashArgs.sa_opts.then(x, y), saa.then(x, y)) : {Sa.ROk{_} == Sa.ROk{SlashArgs.sa_opts.then(x, y)} : Sa.Read}
          {==}
        case Sa.RErr{e}:
          {==}
    case Sa.RErr{e}:
      {==}

def saa.lim_num(ok: Bool, d: String) -> {Sa.lim.num(ok, d) == SlashArgs.sa_lim.num(ok, d) : Maybe<&2, Sa.Lim>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.lim_of(unl: Bool, +v: String) -> {Sa.lim.of(unl, v) == SlashArgs.sa_lim.of(unl, v) : Maybe<&2, Sa.Lim>}:
  match unl:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, Sa.ungroup(v), SlashArgs.sa_ungroup(v), LT.sab.ungroup(v)) : {Sa.lim.num(Sa.u64(_), _) == SlashArgs.sa_lim.of(False{}, v) : Maybe<&2, Sa.Lim>}
      %Equal.sym(Bool, Sa.u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), LT.sab.u64(SlashArgs.sa_ungroup(v))) : {Sa.lim.num(_, SlashArgs.sa_ungroup(v)) == SlashArgs.sa_lim.of(False{}, v) : Maybe<&2, Sa.Lim>}
      saa.lim_num(SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v))

def saa.opt_lim(+name: String, m: Maybe<&2, Sa.Lim>, k: Nat) -> {Sa.opt.lim(name, m, k) == SlashArgs.sa_opt.lim(name, m, k) : Sa.Read}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      match k:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}

def saa.opt_gate(+name: String, ok: Bool, d: String, retries: Bool) -> {Sa.opt.gate(name, ok, d, retries) == SlashArgs.sa_opt.gate(name, ok, d, retries) : Sa.Read}:
  match ok:
    case True{}:
      match retries:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def saa.opt_keep(ok: Bool, d: String) -> {Sa.opt.keep(ok, d) == SlashArgs.sa_opt.keep(ok, d) : Sa.Read}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.keep_ok(+d: String) -> {Sa.keep_ok(d) == SlashArgs.sa_keep_ok(d) : Bool}:
  %Equal.sym(Bool, Sa.positive(d), SlashArgs.sa_positive(d), LT.sab.positive(d)) : {Bool.or(String.eq(d, "0"), Bool.and(_, Bool.or(Nat.is_lt(String.length(d), 10n), Bool.and(Nat.is_eq(String.length(d), 10n), String.is_le(d, "2147483647"))))) == SlashArgs.sa_keep_ok(d) : Bool}
  {==}

def saa.index_at(b: Bool, i: Nat, r: Maybe<&2, Nat>) -> {Sa.index.at(b, i, r) == SlashArgs.sa_index.at(b, i, r) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.index(+n: String, xs: List<&2, String>, +i: Nat) -> {Sa.index(n, xs, i) == SlashArgs.sa_index(n, xs, i) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Maybe<&2, Nat>, Sa.index(n, t, 1n+i), SlashArgs.sa_index(n, t, 1n+i), saa.index(n, t, 1n+i)) : {Sa.index.at(String.eq(n, x), i, _) == SlashArgs.sa_index.at(String.eq(n, x), i, SlashArgs.sa_index(n, t, 1n+i)) : Maybe<&2, Nat>}
      saa.index_at(String.eq(n, x), i, SlashArgs.sa_index(n, t, 1n+i))

def saa.value.lim(+name: String, +v: String, k: Nat) -> {Sa.opt.lim(name, Sa.lim.of(String.eq(String.to_lower(v), "unlimited"), v), k) == SlashArgs.sa_opt.lim(name, SlashArgs.sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), k) : Sa.Read}:
  %Equal.sym(Maybe<&2, Sa.Lim>, Sa.lim.of(String.eq(String.to_lower(v), "unlimited"), v), SlashArgs.sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), saa.lim_of(String.eq(String.to_lower(v), "unlimited"), v)) : {Sa.opt.lim(name, _, k) == SlashArgs.sa_opt.lim(name, SlashArgs.sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), k) : Sa.Read}
  saa.opt_lim(name, SlashArgs.sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), k)

def saa.value.gate(+name: String, +v: String, retries: Bool) -> {Sa.opt.gate(name, Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), retries) == SlashArgs.sa_opt.gate(name, SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v), retries) : Sa.Read}:
  %Equal.sym(String, Sa.ungroup(v), SlashArgs.sa_ungroup(v), LT.sab.ungroup(v)) : {Sa.opt.gate(name, Sa.u64(_), _, retries) == SlashArgs.sa_opt.gate(name, SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v), retries) : Sa.Read}
  %Equal.sym(Bool, Sa.u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), LT.sab.u64(SlashArgs.sa_ungroup(v))) : {Sa.opt.gate(name, _, SlashArgs.sa_ungroup(v), retries) == SlashArgs.sa_opt.gate(name, SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v), retries) : Sa.Read}
  saa.opt_gate(name, SlashArgs.sa_u64(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v), retries)

def saa.value(k: Nat, +name: String, +v: String) -> {Sa.opt.value(k, name, v) == SlashArgs.sa_opt.value(k, name, v) : Sa.Read}:
  match k:
    case 0n:
      saa.value.lim(name, v, 0n)
    case 1n:
      saa.value.lim(name, v, 1n)
    case 2n:
      saa.value.lim(name, v, 2n)
    case 3n:
      saa.value.lim(name, v, 3n)
    case 4n:
      {==}
    case 5n:
      saa.value.gate(name, v, True{})
    case 6n:
      saa.value.gate(name, v, False{})
    case 7n+u:
      %Equal.sym(String, Sa.ungroup(v), SlashArgs.sa_ungroup(v), LT.sab.ungroup(v)) : {Sa.opt.keep(Sa.keep_ok(_), _) == SlashArgs.sa_opt.keep(SlashArgs.sa_keep_ok(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v)) : Sa.Read}
      %Equal.sym(Bool, Sa.keep_ok(SlashArgs.sa_ungroup(v)), SlashArgs.sa_keep_ok(SlashArgs.sa_ungroup(v)), saa.keep_ok(SlashArgs.sa_ungroup(v))) : {Sa.opt.keep(_, SlashArgs.sa_ungroup(v)) == SlashArgs.sa_opt.keep(SlashArgs.sa_keep_ok(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v)) : Sa.Read}
      saa.opt_keep(SlashArgs.sa_keep_ok(SlashArgs.sa_ungroup(v)), SlashArgs.sa_ungroup(v))

# Words of an option
# ------------------

def saa.next_at(flag: Bool, w: String) -> {Sa.val.next.at(flag, w) == SlashArgs.sa_val.next.at(flag, w) : Sa.Val}:
  match flag:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.next(ws: List<&2, String>) -> {Sa.val.next(ws) == SlashArgs.sa_val.next(ws) : Sa.Val}:
  match ws:
    case Nil{}:
      {==}
    case +w <> t:
      saa.next_at(String.starts_with(w, "--"), w)

def saa.val_of(eq: Bool, +tok: String, ws: List<&2, String>) -> {Sa.val.of(eq, tok, ws) == SlashArgs.sa_val.of(eq, tok, ws) : Sa.Val}:
  match eq:
    case True{}:
      %Equal.sym(String, Sa.after_eq(tok), SlashArgs.sa_after_eq(tok), LT.sab.after_eq(tok)) : {Sa.VAt{_, False{}} == Sa.VAt{SlashArgs.sa_after_eq(tok), False{}} : Sa.Val}
      {==}
    case False{}:
      saa.next(ws)

def saa.before_at(b: Bool, c: Char, r: String) -> {Sa.before_eq.at(b, c, r) == SlashArgs.sa_before_eq.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.before(s: String) -> {Sa.before_eq(s) == SlashArgs.sa_before_eq(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.before_eq(t), SlashArgs.sa_before_eq(t), saa.before(t)) : {Sa.before_eq.at(Char.is_eq(c, '='), c, _) == SlashArgs.sa_before_eq.at(Char.is_eq(c, '='), c, SlashArgs.sa_before_eq(t)) : String}
      saa.before_at(Char.is_eq(c, '='), c, SlashArgs.sa_before_eq(t))

def saa.dashes(b: Bool, raw: String) -> {Sa.name.dashes(b, raw) == SlashArgs.sa_name.dashes(b, raw) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def saa.name(b: Bool, +raw: String) -> {Sa.name.of(b, raw) == SlashArgs.sa_name.of(b, raw) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      saa.dashes(String.starts_with(raw, "--"), raw)

# Steps
# -----

def saa.took(empty: Bool, took: Bool, +raw: String, +k: Nat, +name: String, +x: String, r1: Sa.Read, r2: Sa.Read) -> {Sa.step.took(empty, took, raw, k, name, x, r1, r2) == SlashArgs.sa_step.took(empty, took, raw, k, name, x, r1, r2) : Sa.Read}:
  match empty:
    case True{}:
      {==}
    case False{}:
      match took:
        case True{}:
          %Equal.sym(Sa.Read, Sa.opt.value(k, name, x), SlashArgs.sa_opt.value(k, name, x), saa.value(k, name, x)) : {Sa.read.then(_, r2) == SlashArgs.sa_read.then(SlashArgs.sa_opt.value(k, name, x), r2) : Sa.Read}
          saa.read_then(SlashArgs.sa_opt.value(k, name, x), r2)
        case False{}:
          %Equal.sym(Sa.Read, Sa.opt.value(k, name, x), SlashArgs.sa_opt.value(k, name, x), saa.value(k, name, x)) : {Sa.read.then(_, r1) == SlashArgs.sa_read.then(SlashArgs.sa_opt.value(k, name, x), r1) : Sa.Read}
          saa.read_then(SlashArgs.sa_opt.value(k, name, x), r1)

def saa.val(v: Sa.Val, +raw: String, k: Nat, +name: String, r1: Sa.Read, r2: Sa.Read) -> {Sa.step.val(v, raw, k, name, r1, r2) == SlashArgs.sa_step.val(v, raw, k, name, r1, r2) : Sa.Read}:
  match v:
    case Sa.VNone{}:
      {==}
    case Sa.VAt{+x, took}:
      saa.took(String.is_empty(x), took, raw, k, name, x, r1, r2)

def saa.known(m: Maybe<&2, Nat>, +w: String, +raw: String, +name: String, +ws: List<&2, String>, r1: Sa.Read, r2: Sa.Read) -> {Sa.step.known(m, w, raw, name, ws, r1, r2) == SlashArgs.sa_step.known(m, w, raw, name, ws, r1, r2) : Sa.Read}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      %Equal.sym(Sa.Val, Sa.val.of(String.contains(w, "="), w, ws), SlashArgs.sa_val.of(String.contains(w, "="), w, ws), saa.val_of(String.contains(w, "="), w, ws)) : {Sa.step.val(_, raw, k, name, r1, r2) == SlashArgs.sa_step.val(SlashArgs.sa_val.of(String.contains(w, "="), w, ws), raw, k, name, r1, r2) : Sa.Read}
      saa.val(SlashArgs.sa_val.of(String.contains(w, "="), w, ws), raw, k, name, r1, r2)

def saa.flag(+w: String, +ws: List<&2, String>, +r1: Sa.Read, +r2: Sa.Read) -> {Sa.step.flag(w, ws, r1, r2) == SlashArgs.sa_step.flag(w, ws, r1, r2) : Sa.Read}:
  %Equal.sym(String, Sa.before_eq(w), SlashArgs.sa_before_eq(w), saa.before(w)) : {Sa.step.known(Sa.index(Sa.name.of(String.starts_with(_, "--autonomous-"), _), Sa.flags(), 0n), w, _, Sa.name.of(String.starts_with(_, "--autonomous-"), _), ws, r1, r2) == SlashArgs.sa_step.flag(w, ws, r1, r2) : Sa.Read}
  +raw = SlashArgs.sa_before_eq(w)
  %Equal.sym(String, Sa.name.of(String.starts_with(raw, "--autonomous-"), raw), SlashArgs.sa_name.of(String.starts_with(raw, "--autonomous-"), raw), saa.name(String.starts_with(raw, "--autonomous-"), raw)) : {Sa.step.known(Sa.index(_, Sa.flags(), 0n), w, raw, _, ws, r1, r2) == SlashArgs.sa_step.flag(w, ws, r1, r2) : Sa.Read}
  +name = SlashArgs.sa_name.of(String.starts_with(raw, "--autonomous-"), raw)
  %Equal.sym(Maybe<&2, Nat>, Sa.index(name, Sa.flags(), 0n), SlashArgs.sa_index(name, Sa.flags(), 0n), saa.index(name, Sa.flags(), 0n)) : {Sa.step.known(_, w, raw, name, ws, r1, r2) == SlashArgs.sa_step.flag(w, ws, r1, r2) : Sa.Read}
  saa.known(SlashArgs.sa_index(name, Sa.flags(), 0n), w, raw, name, ws, r1, r2)

def saa.step(dash: Bool, +w: String, +ws: List<&2, String>, +r1: Sa.Read, +r2: Sa.Read) -> {Sa.step(dash, w, ws, r1, r2) == SlashArgs.sa_step(dash, w, ws, r1, r2) : Sa.Read}:
  match dash:
    case True{}:
      saa.flag(w, ws, r1, r2)
    case False{}:
      {==}

def saa.reads_of(+w: String, +t: List<&2, String>, rr: Sa.Read & Sa.Read) -> {Sa.reads.of(w, t, rr) == SlashArgs.sa_reads.of(w, t, rr) : Sa.Read & Sa.Read}:
  (r1, r2) = rr
  %Equal.sym(Sa.Read, Sa.step(String.starts_with(w, "--"), w, t, r1, r2), SlashArgs.sa_step(String.starts_with(w, "--"), w, t, r1, r2), saa.step(String.starts_with(w, "--"), w, t, r1, r2)) : {(_, r1) == (SlashArgs.sa_step(String.starts_with(w, "--"), w, t, r1, r2), r1) : Sa.Read & Sa.Read}
  {==}

def saa.reads(ws: List<&2, String>) -> {Sa.reads(ws) == SlashArgs.sa_reads(ws) : Sa.Read & Sa.Read}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +t:
      %Equal.sym(Sa.Read & Sa.Read, Sa.reads(t), SlashArgs.sa_reads(t), saa.reads(t)) : {Sa.reads.of(w, t, _) == SlashArgs.sa_reads.of(w, t, SlashArgs.sa_reads(t)) : Sa.Read & Sa.Read}
      saa.reads_of(w, t, SlashArgs.sa_reads(t))

def saa.fst(rr: Sa.Read & Sa.Read) -> {Sa.options.fst(rr) == SlashArgs.sa_options.fst(rr) : Sa.Read}:
  (r, s) = rr
  {==}

def saa.options(+ws: List<&2, String>) -> {Sa.options(ws) == SlashArgs.sa_options(ws) : Sa.Read}:
  %Equal.sym(Sa.Read & Sa.Read, Sa.reads(ws), SlashArgs.sa_reads(ws), saa.reads(ws)) : {Sa.options.fst(_) == SlashArgs.sa_options(ws) : Sa.Read}
  saa.fst(SlashArgs.sa_reads(ws))

# The answer
# ----------

def saa.unl(m: Maybe<&2, Sa.Lim>) -> {Sa.unl(m) == SlashArgs.sa_unl(m) : Maybe<&2, Sa.Lim>}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      {==}

def saa.gates(cmds: List<&2, String>, gated: Bool, r: Maybe<&2, String>, s: Maybe<&2, String>) -> {Sa.conf.gates(cmds, gated, r, s) == SlashArgs.sa_conf.gates(cmds, gated, r, s) : Maybe<&2, Sa.Gates>}:
  match cmds:
    case Nil{}:
      match gated:
        case True{}:
          {==}
        case False{}:
          {==}
    case c <> t:
      {==}

def saa.limits(named: Bool, +c: Maybe<&2, Sa.Lim>, +t: Maybe<&2, Sa.Lim>, +k: Maybe<&2, Sa.Lim>, +m: Maybe<&2, Sa.Lim>, g: Maybe<&2, Sa.Gates>, p: Maybe<&2, String>) -> {Sa.conf.limits(named, c, t, k, m, g, p) == SlashArgs.sa_conf.limits(named, c, t, k, m, g, p) : Sa.Conf}:
  match named:
    case True{}:
      %Equal.sym(Maybe<&2, Sa.Lim>, Sa.unl(c), SlashArgs.sa_unl(c), saa.unl(c)) : {Sa.Conf{_, Sa.unl(t), Sa.unl(k), Sa.unl(m), g, p} == SlashArgs.sa_conf.limits(True{}, c, t, k, m, g, p) : Sa.Conf}
      %Equal.sym(Maybe<&2, Sa.Lim>, Sa.unl(t), SlashArgs.sa_unl(t), saa.unl(t)) : {Sa.Conf{SlashArgs.sa_unl(c), _, Sa.unl(k), Sa.unl(m), g, p} == SlashArgs.sa_conf.limits(True{}, c, t, k, m, g, p) : Sa.Conf}
      %Equal.sym(Maybe<&2, Sa.Lim>, Sa.unl(k), SlashArgs.sa_unl(k), saa.unl(k)) : {Sa.Conf{SlashArgs.sa_unl(c), SlashArgs.sa_unl(t), _, Sa.unl(m), g, p} == SlashArgs.sa_conf.limits(True{}, c, t, k, m, g, p) : Sa.Conf}
      %Equal.sym(Maybe<&2, Sa.Lim>, Sa.unl(m), SlashArgs.sa_unl(m), saa.unl(m)) : {Sa.Conf{SlashArgs.sa_unl(c), SlashArgs.sa_unl(t), SlashArgs.sa_unl(k), _, g, p} == SlashArgs.sa_conf.limits(True{}, c, t, k, m, g, p) : Sa.Conf}
      {==}
    case False{}:
      {==}

def saa.some(-A: Data, m: Maybe<&2, A>) -> {Sa.some(A, m) == SlashArgs.sa_some(A, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def saa.conf(o: Sa.Opts) -> {Sa.conf(o) == SlashArgs.sa_conf(o) : Sa.Conf}:
  match o:
    case Sa.Opts{+c, +t, +k, +m, +g, +d, +r, +s, +p}:
      %Equal.sym(Bool, Sa.some(Sa.Lim, c), SlashArgs.sa_some(Sa.Lim, c), saa.some(Sa.Lim, c)) : {Sa.conf.limits(Bool.or(Bool.or(_, Sa.some(Sa.Lim, t)), Bool.or(Sa.some(Sa.Lim, k), Sa.some(Sa.Lim, m))), c, t, k, m, Sa.conf.gates(g, d, r, s), p) == SlashArgs.sa_conf(Sa.Opts{c, t, k, m, g, d, r, s, p}) : Sa.Conf}
      %Equal.sym(Bool, Sa.some(Sa.Lim, t), SlashArgs.sa_some(Sa.Lim, t), saa.some(Sa.Lim, t)) : {Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_some(Sa.Lim, c), _), Bool.or(Sa.some(Sa.Lim, k), Sa.some(Sa.Lim, m))), c, t, k, m, Sa.conf.gates(g, d, r, s), p) == SlashArgs.sa_conf(Sa.Opts{c, t, k, m, g, d, r, s, p}) : Sa.Conf}
      %Equal.sym(Bool, Sa.some(Sa.Lim, k), SlashArgs.sa_some(Sa.Lim, k), saa.some(Sa.Lim, k)) : {Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_some(Sa.Lim, c), SlashArgs.sa_some(Sa.Lim, t)), Bool.or(_, Sa.some(Sa.Lim, m))), c, t, k, m, Sa.conf.gates(g, d, r, s), p) == SlashArgs.sa_conf(Sa.Opts{c, t, k, m, g, d, r, s, p}) : Sa.Conf}
      %Equal.sym(Bool, Sa.some(Sa.Lim, m), SlashArgs.sa_some(Sa.Lim, m), saa.some(Sa.Lim, m)) : {Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_some(Sa.Lim, c), SlashArgs.sa_some(Sa.Lim, t)), Bool.or(SlashArgs.sa_some(Sa.Lim, k), _)), c, t, k, m, Sa.conf.gates(g, d, r, s), p) == SlashArgs.sa_conf(Sa.Opts{c, t, k, m, g, d, r, s, p}) : Sa.Conf}
      %Equal.sym(Maybe<&2, Sa.Gates>, Sa.conf.gates(g, d, r, s), SlashArgs.sa_conf.gates(g, d, r, s), saa.gates(g, d, r, s)) : {Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_some(Sa.Lim, c), SlashArgs.sa_some(Sa.Lim, t)), Bool.or(SlashArgs.sa_some(Sa.Lim, k), SlashArgs.sa_some(Sa.Lim, m))), c, t, k, m, _, p) == SlashArgs.sa_conf(Sa.Opts{c, t, k, m, g, d, r, s, p}) : Sa.Conf}
      saa.limits(Bool.or(Bool.or(SlashArgs.sa_some(Sa.Lim, c), SlashArgs.sa_some(Sa.Lim, t)), Bool.or(SlashArgs.sa_some(Sa.Lim, k), SlashArgs.sa_some(Sa.Lim, m))), c, t, k, m, SlashArgs.sa_conf.gates(g, d, r, s), p)

def saa.on(r: Sa.Read) -> {Sa.auto.on(r) == SlashArgs.sa_auto.on(r) : Sa.Auto}:
  match r:
    case Sa.ROk{+o}:
      %Equal.sym(Sa.Conf, Sa.conf(o), SlashArgs.sa_conf(o), saa.conf(o)) : {Sa.AOn{_} == Sa.AOn{SlashArgs.sa_conf(o)} : Sa.Auto}
      {==}
    case Sa.RErr{e}:
      {==}

def saa.alone(ws: List<&2, String>, a: Sa.Auto) -> {Sa.auto.alone(ws, a) == SlashArgs.sa_auto.alone(ws, a) : Sa.Auto}:
  match ws:
    case Nil{}:
      {==}
    case w <> t:
      {==}

def saa.kw(status: Bool, on: Bool, off: Bool, +ws: List<&2, String>) -> {Sa.auto.kw(status, on, off, ws) == SlashArgs.sa_auto.kw(status, on, off, ws) : Sa.Auto}:
  match status:
    case True{}:
      saa.alone(ws, Sa.AStatus{})
    case False{}:
      match on:
        case True{}:
          %Equal.sym(Sa.Read, Sa.options(ws), SlashArgs.sa_options(ws), saa.options(ws)) : {Sa.auto.on(_) == SlashArgs.sa_auto.on(SlashArgs.sa_options(ws)) : Sa.Auto}
          saa.on(SlashArgs.sa_options(ws))
        case False{}:
          match off:
            case True{}:
              saa.alone(ws, Sa.AOff{})
            case False{}:
              {==}

def saa.words(ws: List<&2, String>) -> {Sa.auto.words(ws) == SlashArgs.sa_auto.words(ws) : Sa.Auto}:
  match ws:
    case Nil{}:
      {==}
    case w <> +t:
      +l = String.to_lower(w)
      saa.kw(String.eq(l, "status"), Bool.or(String.eq(l, "on"), Bool.or(String.eq(l, "enable"), String.eq(l, "enabled"))), Bool.or(String.eq(l, "off"), Bool.or(String.eq(l, "disable"), String.eq(l, "disabled"))), t)

def saa.auto(+s: String) -> {Sa.auto(s) == SlashArgs.sa_auto(s) : Sa.Auto}:
  %Equal.sym(List<&2, String>, Sa.words(s), SlashArgs.sa_words(s), LT.sab.words(s)) : {Sa.auto.words(_) == SlashArgs.sa_auto(s) : Sa.Auto}
  saa.words(SlashArgs.sa_words(s))
