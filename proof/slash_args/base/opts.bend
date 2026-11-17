# eukhe: lemmas of area slash_args: options read in order (R7-R9), for
# LAW slash_args_auto_options, slash_args_auto_bad_value and
# slash_args_auto_first_error. One option's words read its value, then
# the options after them (sao.one); the value of an option read without
# an error is the options it names (sao.val_ok); reading options in turn
# keeps each flag's last value and the gate commands in order
# (sao.merge), and `/autonomous on` takes them as R9 says (sao.conf).

import Base
import ../../../bend/slash_args.bend as Sa
import ../../../laws/slash_args/model.bend as SlashArgs
import ../../base/staging.bend as LStg
import ../base.bend as LA
import ./auto.bend as LAA
import ../slash_args_auto_option.bend as PSO

def sao.and_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, e)

def sao.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LStg.stg.absurdF({b == True{} : Bool}, e)

def sao.app_nil(xs: List<&2, String>) -> {List.append(&2, String, xs, Nil{}) == xs : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, List.append(&2, String, u, Nil{}), u, sao.app_nil(u))

# The value of an option, read by the code, and that value then x
# ---------------------------------------------------------------

def sao.val(o: SlashArgs.SaOpt) -> Sa.Read:
  match o:
    case SlashArgs.SaOpt{p, +k, e, v}:
      Sa.opt.value(k, SlashArgs.sa_flag_name(k), v)

def sao.at(o: SlashArgs.SaOpt, x: Sa.Read) -> Sa.Read:
  Sa.read.then(sao.val(o), x)

# the options os read in turn, then x
def sao.fold(os: List<&2, SlashArgs.SaOpt>, x: Sa.Read) -> Sa.Read:
  match os:
    case Nil{}:
      x
    case o <> t:
      sao.at(o, sao.fold(t, x))

# One option's words
# ------------------

# the reads of v then r, without v: the options of r
def sao.snd(+v: String, +r: List<&2, String>, rr: Sa.Read & Sa.Read) -> {LA.sab.snd(Sa.reads.of(v, r, rr)) == Sa.options.fst(rr) : Sa.Read}:
  match rr:
    case (a, b):
      {==}

# a flag word x then r: x's step
def sao.word(+x: String, +r: List<&2, String>, +rhs: Sa.Read, sw: {String.starts_with(x, "--") == True{} : Bool}, st: {Sa.step(True{}, x, r, Sa.options(r), LA.sab.snd(Sa.reads(r))) == rhs : Sa.Read}) -> {Sa.options(x <> r) == rhs : Sa.Read}:
  Equal.trans(Sa.Read, Sa.options(x <> r), Sa.step(String.starts_with(x, "--"), x, r, Sa.options(r), LA.sab.snd(Sa.reads(r))), rhs, LA.sab.first_word(x, r, Sa.reads(r)), Equal.trans(Sa.Read, Sa.step(String.starts_with(x, "--"), x, r, Sa.options(r), LA.sab.snd(Sa.reads(r))), Sa.step(True{}, x, r, Sa.options(r), LA.sab.snd(Sa.reads(r))), rhs, Equal.cong(Bool, Sa.Read, z => Sa.step(z, x, r, Sa.options(r), LA.sab.snd(Sa.reads(r))), String.starts_with(x, "--"), True{}, sw), st))

# the option word `<prefix><name>=v`
def sao.eqw(p: Bool, k: Nat, v: String) -> String:
  String.append(String.append(SlashArgs.sa_prefix(p), SlashArgs.sa_flag_name(k)), SCon{'=', v})

# the option word `<prefix><name>`
def sao.spw(p: Bool, k: Nat) -> String:
  String.append(SlashArgs.sa_prefix(p), SlashArgs.sa_flag_name(k))

# after a flag word f, the next word v (not starting with `--`) is its
# value, and the reads go on after v
def sao.sp.tail(+f: String, +j: Nat, +nm: String, +c: Char, +t: String, +r: List<&2, String>, sv: {String.starts_with(SCon{c, t}, "--") == False{} : Bool}) -> {Sa.step.val(Sa.val.next(SCon{c, t} <> r), f, j, nm, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))) == Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), Sa.options(r)) : Sa.Read}:
  %Equal.sym(Bool, String.starts_with(SCon{c, t}, "--"), False{}, sv) : {Sa.step.val(Sa.val.next.at(_, SCon{c, t}), f, j, nm, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))) == Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), Sa.options(r)) : Sa.Read}
  %Equal.sym(Sa.Read, LA.sab.snd(Sa.reads.of(SCon{c, t}, r, Sa.reads(r))), Sa.options.fst(Sa.reads(r)), sao.snd(SCon{c, t}, r, Sa.reads(r))) : {Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), _) == Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), Sa.options(r)) : Sa.Read}
  {==}

def sao.sp.case(+f: String, +j: Nat, +nm: String, +c: Char, +t: String, +r: List<&2, String>, sv: {String.starts_with(SCon{c, t}, "--") == False{} : Bool}, sw: {String.starts_with(f, "--") == True{} : Bool}, st: {Sa.step(True{}, f, SCon{c, t} <> r, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))) == Sa.step.val(Sa.val.next(SCon{c, t} <> r), f, j, nm, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))) : Sa.Read}) -> {Sa.options(f <> SCon{c, t} <> r) == Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), Sa.options(r)) : Sa.Read}:
  Equal.trans(Sa.Read, Sa.options(f <> SCon{c, t} <> r), Sa.step.val(Sa.val.next(SCon{c, t} <> r), f, j, nm, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))), Sa.read.then(Sa.opt.value(j, nm, SCon{c, t}), Sa.options(r)), sao.word(f, SCon{c, t} <> r, Sa.step.val(Sa.val.next(SCon{c, t} <> r), f, j, nm, Sa.options(SCon{c, t} <> r), LA.sab.snd(Sa.reads(SCon{c, t} <> r))), sw, st), sao.sp.tail(f, j, nm, c, t, r, sv))

# the word `<prefix><name>=v` (v not empty) then r: v read, then the
# options of r
def sao.one.eq(p: Bool, k: Nat, +c: Char, +t: String, +r: List<&2, String>) -> {Sa.options(sao.eqw(p, k, SCon{c, t}) <> r) == Sa.read.then(Sa.opt.value(k, SlashArgs.sa_flag_name(k), SCon{c, t}), Sa.options(r)) : Sa.Read}:
  match p:
    case True{}:
      match k:
        case 0n:
          sao.word(sao.eqw(True{}, 0n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(0n, "max-continuations", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 1n:
          sao.word(sao.eqw(True{}, 1n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(1n, "max-turns", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 2n:
          sao.word(sao.eqw(True{}, 2n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(2n, "max-tokens", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 3n:
          sao.word(sao.eqw(True{}, 3n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(3n, "timeout-ms", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 4n:
          sao.word(sao.eqw(True{}, 4n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(4n, "gate", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 5n:
          sao.word(sao.eqw(True{}, 5n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(5n, "gate-retries", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 6n:
          sao.word(sao.eqw(True{}, 6n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(6n, "gate-timeout-ms", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 7n+u:
          sao.word(sao.eqw(True{}, 7n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(7n, "subagent-keep-alive-ms", SCon{c, t}), Sa.options(r)), {==}, {==})
    case False{}:
      match k:
        case 0n:
          sao.word(sao.eqw(False{}, 0n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(0n, "max-continuations", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 1n:
          sao.word(sao.eqw(False{}, 1n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(1n, "max-turns", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 2n:
          sao.word(sao.eqw(False{}, 2n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(2n, "max-tokens", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 3n:
          sao.word(sao.eqw(False{}, 3n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(3n, "timeout-ms", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 4n:
          sao.word(sao.eqw(False{}, 4n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(4n, "gate", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 5n:
          sao.word(sao.eqw(False{}, 5n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(5n, "gate-retries", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 6n:
          sao.word(sao.eqw(False{}, 6n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(6n, "gate-timeout-ms", SCon{c, t}), Sa.options(r)), {==}, {==})
        case 7n+u:
          sao.word(sao.eqw(False{}, 7n, SCon{c, t}), r, Sa.read.then(Sa.opt.value(7n, "subagent-keep-alive-ms", SCon{c, t}), Sa.options(r)), {==}, {==})

# the words `<prefix><name>` and v (v not empty, not starting with `--`)
# then r: v read, then the options of r
def sao.one.sp(p: Bool, k: Nat, +c: Char, +t: String, +r: List<&2, String>, sv: {String.starts_with(SCon{c, t}, "--") == False{} : Bool}) -> {Sa.options(sao.spw(p, k) <> SCon{c, t} <> r) == Sa.read.then(Sa.opt.value(k, SlashArgs.sa_flag_name(k), SCon{c, t}), Sa.options(r)) : Sa.Read}:
  match p:
    case True{}:
      match k:
        case 0n:
          sao.sp.case(sao.spw(True{}, 0n), 0n, "max-continuations", c, t, r, sv, {==}, {==})
        case 1n:
          sao.sp.case(sao.spw(True{}, 1n), 1n, "max-turns", c, t, r, sv, {==}, {==})
        case 2n:
          sao.sp.case(sao.spw(True{}, 2n), 2n, "max-tokens", c, t, r, sv, {==}, {==})
        case 3n:
          sao.sp.case(sao.spw(True{}, 3n), 3n, "timeout-ms", c, t, r, sv, {==}, {==})
        case 4n:
          sao.sp.case(sao.spw(True{}, 4n), 4n, "gate", c, t, r, sv, {==}, {==})
        case 5n:
          sao.sp.case(sao.spw(True{}, 5n), 5n, "gate-retries", c, t, r, sv, {==}, {==})
        case 6n:
          sao.sp.case(sao.spw(True{}, 6n), 6n, "gate-timeout-ms", c, t, r, sv, {==}, {==})
        case 7n+u:
          sao.sp.case(sao.spw(True{}, 7n), 7n, "subagent-keep-alive-ms", c, t, r, sv, {==}, {==})
    case False{}:
      match k:
        case 0n:
          sao.sp.case(sao.spw(False{}, 0n), 0n, "max-continuations", c, t, r, sv, {==}, {==})
        case 1n:
          sao.sp.case(sao.spw(False{}, 1n), 1n, "max-turns", c, t, r, sv, {==}, {==})
        case 2n:
          sao.sp.case(sao.spw(False{}, 2n), 2n, "max-tokens", c, t, r, sv, {==}, {==})
        case 3n:
          sao.sp.case(sao.spw(False{}, 3n), 3n, "timeout-ms", c, t, r, sv, {==}, {==})
        case 4n:
          sao.sp.case(sao.spw(False{}, 4n), 4n, "gate", c, t, r, sv, {==}, {==})
        case 5n:
          sao.sp.case(sao.spw(False{}, 5n), 5n, "gate-retries", c, t, r, sv, {==}, {==})
        case 6n:
          sao.sp.case(sao.spw(False{}, 6n), 6n, "gate-timeout-ms", c, t, r, sv, {==}, {==})
        case 7n+u:
          sao.sp.case(sao.spw(False{}, 7n), 7n, "subagent-keep-alive-ms", c, t, r, sv, {==}, {==})

# an option whose value is given, then r: its value read, then the
# options of r
def sao.one(o: SlashArgs.SaOpt, +r: List<&2, String>, g: {SlashArgs.sa_opt_given(o) == True{} : Bool}) -> {Sa.options(List.append(&2, String, SlashArgs.sa_opt_words(o), r)) == sao.at(o, Sa.options(r)) : Sa.Read}:
  match o:
    case SlashArgs.SaOpt{p, k, e, v}:
      match e:
        case True{}:
          match v:
            case SNil{}:
              LStg.stg.absurdF({Sa.options(List.append(&2, String, SlashArgs.sa_opt_words(SlashArgs.SaOpt{p, k, True{}, SNil{}}), r)) == sao.at(SlashArgs.SaOpt{p, k, True{}, SNil{}}, Sa.options(r)) : Sa.Read}, g)
            case SCon{+c, +t}:
              sao.one.eq(p, k, c, t, r)
        case False{}:
          match v:
            case SNil{}:
              LStg.stg.absurdF({Sa.options(List.append(&2, String, SlashArgs.sa_opt_words(SlashArgs.SaOpt{p, k, False{}, SNil{}}), r)) == sao.at(SlashArgs.SaOpt{p, k, False{}, SNil{}}, Sa.options(r)) : Sa.Read}, g)
            case SCon{+c, +t}:
              sao.one.sp(p, k, c, t, r, LA.sab.not_t(String.starts_with(SCon{c, t}, "--"), g))

# The options an option names, by R9's helpers
# --------------------------------------------

def sao.lims(m: Maybe<&2, String>) -> Maybe<&2, Sa.Lim>:
  match m:
    case Some{v}:
      Some{SlashArgs.sa_lim(v)}
    case None{}:
      None{}

def sao.spec.of(m0: Maybe<&2, String>, m1: Maybe<&2, String>, m2: Maybe<&2, String>, m3: Maybe<&2, String>, cm: List<&2, String>, +m5: Maybe<&2, String>, +m6: Maybe<&2, String>, m7: Maybe<&2, String>) -> Sa.Opts:
  Sa.Opts{sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6), SlashArgs.sa_digits_of(m7)}

# the options os name: each flag's last value, the gate commands
def sao.spec(+os: List<&2, SlashArgs.SaOpt>) -> Sa.Opts:
  sao.spec.of(SlashArgs.sa_last(os, 0n), SlashArgs.sa_last(os, 1n), SlashArgs.sa_last(os, 2n), SlashArgs.sa_last(os, 3n), SlashArgs.sa_cmds(os), SlashArgs.sa_last(os, 5n), SlashArgs.sa_last(os, 6n), SlashArgs.sa_last(os, 7n))

# a limit's value R8 takes
def sao.w.num(c: Bool, +d: String, +k: Nat, +nm: String, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(Sa.opt.lim(nm, Sa.lim.num(c, d), k), PSO.sop.none()))) == True{} : Bool}) -> {Sa.opt.lim(nm, Sa.lim.num(c, d), k) == Sa.opt.lim(nm, Some{Sa.LNum{d}}, k) : Sa.Read}:
  match c:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({Sa.opt.lim(nm, Sa.lim.num(False{}, d), k) == Sa.opt.lim(nm, Some{Sa.LNum{d}}, k) : Sa.Read}, h)

def sao.w.lim(b: Bool, +k: Nat, +nm: String, +v: String, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(Sa.opt.lim(nm, Sa.lim.of(b, v), k), PSO.sop.none()))) == True{} : Bool}) -> {Sa.opt.lim(nm, Sa.lim.of(b, v), k) == Sa.opt.lim(nm, Some{SlashArgs.sa_lim.at(b, v)}, k) : Sa.Read}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Sa.Read, Sa.opt.lim(nm, Sa.lim.num(Sa.u64(Sa.ungroup(v)), Sa.ungroup(v)), k), Sa.opt.lim(nm, Some{Sa.LNum{Sa.ungroup(v)}}, k), Sa.opt.lim(nm, Some{Sa.LNum{SlashArgs.sa_ungroup(v)}}, k), sao.w.num(Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), k, nm, h), Equal.cong(String, Sa.Read, z => Sa.opt.lim(nm, Some{Sa.LNum{z}}, k), Sa.ungroup(v), SlashArgs.sa_ungroup(v), LAA.saa.ungroup(v)))

# a gate number R8 takes
def sao.w.gate(c: Bool, +d: String, +nm: String, +rt: Bool, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(Sa.opt.gate(nm, c, d, rt), PSO.sop.none()))) == True{} : Bool}) -> {Sa.opt.gate(nm, c, d, rt) == Sa.opt.gate(nm, True{}, d, rt) : Sa.Read}:
  match c:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({Sa.opt.gate(nm, False{}, d, rt) == Sa.opt.gate(nm, True{}, d, rt) : Sa.Read}, h)

# a keep-alive R8 takes
def sao.w.keep(c: Bool, +d: String, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(Sa.opt.keep(c, d), PSO.sop.none()))) == True{} : Bool}) -> {Sa.opt.keep(c, d) == Sa.opt.keep(True{}, d) : Sa.Read}:
  match c:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({Sa.opt.keep(False{}, d) == Sa.opt.keep(True{}, d) : Sa.Read}, h)

# the value v of the flag k, taken by R8: the options it names
def sao.val_k(p: Bool, e: Bool, k: Nat, +v: String, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(Sa.opt.value(k, SlashArgs.sa_flag_name(k), v), PSO.sop.none()))) == True{} : Bool}) -> {Sa.opt.value(k, SlashArgs.sa_flag_name(k), v) == Sa.ROk{sao.spec(SlashArgs.SaOpt{p, k, e, v} <> Nil{})} : Sa.Read}:
  match k:
    case 0n:
      sao.w.lim(String.eq(String.to_lower(v), "unlimited"), 0n, "max-continuations", v, h)
    case 1n:
      sao.w.lim(String.eq(String.to_lower(v), "unlimited"), 1n, "max-turns", v, h)
    case 2n:
      sao.w.lim(String.eq(String.to_lower(v), "unlimited"), 2n, "max-tokens", v, h)
    case 3n:
      sao.w.lim(String.eq(String.to_lower(v), "unlimited"), 3n, "timeout-ms", v, h)
    case 4n:
      {==}
    case 5n:
      Equal.trans(Sa.Read, Sa.opt.gate("gate-retries", Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), True{}), Sa.opt.gate("gate-retries", True{}, Sa.ungroup(v), True{}), Sa.opt.gate("gate-retries", True{}, SlashArgs.sa_ungroup(v), True{}), sao.w.gate(Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), "gate-retries", True{}, h), Equal.cong(String, Sa.Read, z => Sa.opt.gate("gate-retries", True{}, z, True{}), Sa.ungroup(v), SlashArgs.sa_ungroup(v), LAA.saa.ungroup(v)))
    case 6n:
      Equal.trans(Sa.Read, Sa.opt.gate("gate-timeout-ms", Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), False{}), Sa.opt.gate("gate-timeout-ms", True{}, Sa.ungroup(v), False{}), Sa.opt.gate("gate-timeout-ms", True{}, SlashArgs.sa_ungroup(v), False{}), sao.w.gate(Sa.u64(Sa.ungroup(v)), Sa.ungroup(v), "gate-timeout-ms", False{}, h), Equal.cong(String, Sa.Read, z => Sa.opt.gate("gate-timeout-ms", True{}, z, False{}), Sa.ungroup(v), SlashArgs.sa_ungroup(v), LAA.saa.ungroup(v)))
    case 7n+u:
      Equal.trans(Sa.Read, Sa.opt.keep(Sa.keep_ok(Sa.ungroup(v)), Sa.ungroup(v)), Sa.opt.keep(True{}, Sa.ungroup(v)), Sa.opt.keep(True{}, SlashArgs.sa_ungroup(v)), sao.w.keep(Sa.keep_ok(Sa.ungroup(v)), Sa.ungroup(v), h), Equal.cong(String, Sa.Read, z => Sa.opt.keep(True{}, z), Sa.ungroup(v), SlashArgs.sa_ungroup(v), LAA.saa.ungroup(v)))

# an option read without an error: the options it names
def sao.val_ok(o: SlashArgs.SaOpt, h: {SlashArgs.sa_is_on(SlashArgs.sa_opt_read(o)) == True{} : Bool}) -> {sao.val(o) == Sa.ROk{sao.spec(o <> Nil{})} : Sa.Read}:
  match o:
    case SlashArgs.SaOpt{p, +k, e, +v}:
      +a = Sa.auto.on(Sa.read.then(Sa.opt.value(k, SlashArgs.sa_flag_name(k), v), PSO.sop.none()))
      sao.val_k(p, e, k, v, Equal.trans(Bool, SlashArgs.sa_is_on(a), SlashArgs.sa_is_on(SlashArgs.sa_option(k, v)), True{}, Equal.cong(Sa.Auto, Bool, z => SlashArgs.sa_is_on(z), a, SlashArgs.sa_option(k, v), PSO.sop.v(k, v)), h))

# Reading options in turn
# -----------------------

def sao.fl(n: Maybe<&2, String>, m: Maybe<&2, String>) -> {Sa.later(Sa.Lim, sao.lims(n), sao.lims(m)) == sao.lims(SlashArgs.sa_pick(m, n)) : Maybe<&2, Sa.Lim>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def sao.fd(n: Maybe<&2, String>, m: Maybe<&2, String>) -> {Sa.later(String, SlashArgs.sa_digits_of(n), SlashArgs.sa_digits_of(m)) == SlashArgs.sa_digits_of(SlashArgs.sa_pick(m, n)) : Maybe<&2, String>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def sao.fc(n: Maybe<&2, String>, cm: List<&2, String>) -> {List.append(&2, String, SlashArgs.sa_cmds.at(n, Nil{}), cm) == SlashArgs.sa_cmds.at(n, cm) : List<&2, String>}:
  match n:
    case Some{x}:
      {==}
    case None{}:
      {==}

def sao.fg(n5: Maybe<&2, String>, n6: Maybe<&2, String>, m5: Maybe<&2, String>, m6: Maybe<&2, String>) -> {Bool.or(Bool.or(SlashArgs.sa_is_some(n5), SlashArgs.sa_is_some(n6)), Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6))) == Bool.or(SlashArgs.sa_is_some(SlashArgs.sa_pick(m5, n5)), SlashArgs.sa_is_some(SlashArgs.sa_pick(m6, n6))) : Bool}:
  match n5:
    case Some{x0}:
      match n6:
        case Some{x1}:
          match m5:
            case Some{x2}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
        case None{}:
          match m5:
            case Some{x2}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
    case None{}:
      match n6:
        case Some{x1}:
          match m5:
            case Some{x2}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
        case None{}:
          match m5:
            case Some{x2}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m6:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}

# the options of equal fields are equal
def sao.ok9(+a0: Maybe<&2, Sa.Lim>, +b0: Maybe<&2, Sa.Lim>, e0: {a0 == b0 : Maybe<&2, Sa.Lim>}, +a1: Maybe<&2, Sa.Lim>, +b1: Maybe<&2, Sa.Lim>, e1: {a1 == b1 : Maybe<&2, Sa.Lim>}, +a2: Maybe<&2, Sa.Lim>, +b2: Maybe<&2, Sa.Lim>, e2: {a2 == b2 : Maybe<&2, Sa.Lim>}, +a3: Maybe<&2, Sa.Lim>, +b3: Maybe<&2, Sa.Lim>, e3: {a3 == b3 : Maybe<&2, Sa.Lim>}, +a4: List<&2, String>, +b4: List<&2, String>, e4: {a4 == b4 : List<&2, String>}, +a5: Bool, +b5: Bool, e5: {a5 == b5 : Bool}, +a6: Maybe<&2, String>, +b6: Maybe<&2, String>, e6: {a6 == b6 : Maybe<&2, String>}, +a7: Maybe<&2, String>, +b7: Maybe<&2, String>, e7: {a7 == b7 : Maybe<&2, String>}, +a8: Maybe<&2, String>, +b8: Maybe<&2, String>, e8: {a8 == b8 : Maybe<&2, String>}) -> {Sa.Opts{a0, a1, a2, a3, a4, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}:
  %Equal.sym(Maybe<&2, Sa.Lim>, a0, b0, e0) : {Sa.Opts{_, a1, a2, a3, a4, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, Sa.Lim>, a1, b1, e1) : {Sa.Opts{b0, _, a2, a3, a4, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, Sa.Lim>, a2, b2, e2) : {Sa.Opts{b0, b1, _, a3, a4, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, Sa.Lim>, a3, b3, e3) : {Sa.Opts{b0, b1, b2, _, a4, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(List<&2, String>, a4, b4, e4) : {Sa.Opts{b0, b1, b2, b3, _, a5, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Bool, a5, b5, e5) : {Sa.Opts{b0, b1, b2, b3, b4, _, a6, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, String>, a6, b6, e6) : {Sa.Opts{b0, b1, b2, b3, b4, b5, _, a7, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, String>, a7, b7, e7) : {Sa.Opts{b0, b1, b2, b3, b4, b5, b6, _, a8} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  %Equal.sym(Maybe<&2, String>, a8, b8, e8) : {Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, _} == Sa.Opts{b0, b1, b2, b3, b4, b5, b6, b7, b8} : Sa.Opts}
  {==}

# an option's options n, then the options m read after it: each flag's
# later value, the gate commands in order
def sao.merge(+n0: Maybe<&2, String>, +n1: Maybe<&2, String>, +n2: Maybe<&2, String>, +n3: Maybe<&2, String>, +n4: Maybe<&2, String>, +n5: Maybe<&2, String>, +n6: Maybe<&2, String>, +n7: Maybe<&2, String>, +m0: Maybe<&2, String>, +m1: Maybe<&2, String>, +m2: Maybe<&2, String>, +m3: Maybe<&2, String>, +cm: List<&2, String>, +m5: Maybe<&2, String>, +m6: Maybe<&2, String>, +m7: Maybe<&2, String>) -> {Sa.opts.then(sao.spec.of(n0, n1, n2, n3, SlashArgs.sa_cmds.at(n4, Nil{}), n5, n6, n7), sao.spec.of(m0, m1, m2, m3, cm, m5, m6, m7)) == sao.spec.of(SlashArgs.sa_pick(m0, n0), SlashArgs.sa_pick(m1, n1), SlashArgs.sa_pick(m2, n2), SlashArgs.sa_pick(m3, n3), SlashArgs.sa_cmds.at(n4, cm), SlashArgs.sa_pick(m5, n5), SlashArgs.sa_pick(m6, n6), SlashArgs.sa_pick(m7, n7)) : Sa.Opts}:
  sao.ok9(Sa.later(Sa.Lim, sao.lims(n0), sao.lims(m0)), sao.lims(SlashArgs.sa_pick(m0, n0)), sao.fl(n0, m0), Sa.later(Sa.Lim, sao.lims(n1), sao.lims(m1)), sao.lims(SlashArgs.sa_pick(m1, n1)), sao.fl(n1, m1), Sa.later(Sa.Lim, sao.lims(n2), sao.lims(m2)), sao.lims(SlashArgs.sa_pick(m2, n2)), sao.fl(n2, m2), Sa.later(Sa.Lim, sao.lims(n3), sao.lims(m3)), sao.lims(SlashArgs.sa_pick(m3, n3)), sao.fl(n3, m3), List.append(&2, String, SlashArgs.sa_cmds.at(n4, Nil{}), cm), SlashArgs.sa_cmds.at(n4, cm), sao.fc(n4, cm), Bool.or(Bool.or(SlashArgs.sa_is_some(n5), SlashArgs.sa_is_some(n6)), Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6))), Bool.or(SlashArgs.sa_is_some(SlashArgs.sa_pick(m5, n5)), SlashArgs.sa_is_some(SlashArgs.sa_pick(m6, n6))), sao.fg(n5, n6, m5, m6), Sa.later(String, SlashArgs.sa_digits_of(n5), SlashArgs.sa_digits_of(m5)), SlashArgs.sa_digits_of(SlashArgs.sa_pick(m5, n5)), sao.fd(n5, m5), Sa.later(String, SlashArgs.sa_digits_of(n6), SlashArgs.sa_digits_of(m6)), SlashArgs.sa_digits_of(SlashArgs.sa_pick(m6, n6)), sao.fd(n6, m6), Sa.later(String, SlashArgs.sa_digits_of(n7), SlashArgs.sa_digits_of(m7)), SlashArgs.sa_digits_of(SlashArgs.sa_pick(m7, n7)), sao.fd(n7, m7))

# options read without an error, in turn: the options they name
def sao.fold_ok(os: List<&2, SlashArgs.SaOpt>, +ok: {SlashArgs.sa_opts_ok(os) == True{} : Bool}) -> {sao.fold(os, Sa.ROk{Sa.opts.none()}) == Sa.ROk{sao.spec(os)} : Sa.Read}:
  match os:
    case Nil{}:
      {==}
    case +o <> +t:
      +ok1 = sao.and_l(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok)
      +h = sao.and_r(SlashArgs.sa_opt_given(o), SlashArgs.sa_is_on(SlashArgs.sa_opt_read(o)), ok1)
      +st = sao.spec(t)
      +so = sao.spec(o <> Nil{})
      Equal.trans(Sa.Read, Sa.read.then(sao.val(o), sao.fold(t, Sa.ROk{Sa.opts.none()})), Sa.read.then(sao.val(o), Sa.ROk{st}), Sa.ROk{sao.spec(o <> t)}, Equal.cong(Sa.Read, Sa.Read, z => Sa.read.then(sao.val(o), z), sao.fold(t, Sa.ROk{Sa.opts.none()}), Sa.ROk{st}, sao.fold_ok(t, sao.and_r(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok))), Equal.trans(Sa.Read, Sa.read.then(sao.val(o), Sa.ROk{st}), Sa.read.then(Sa.ROk{so}, Sa.ROk{st}), Sa.ROk{sao.spec(o <> t)}, Equal.cong(Sa.Read, Sa.Read, z => Sa.read.then(z, Sa.ROk{st}), sao.val(o), Sa.ROk{so}, sao.val_ok(o, h)), Equal.cong(Sa.Opts, Sa.Read, z => Sa.ROk{z}, Sa.opts.then(so, st), sao.spec(o <> t), sao.merge(SlashArgs.sa_named(o, 0n), SlashArgs.sa_named(o, 1n), SlashArgs.sa_named(o, 2n), SlashArgs.sa_named(o, 3n), SlashArgs.sa_named(o, 4n), SlashArgs.sa_named(o, 5n), SlashArgs.sa_named(o, 6n), SlashArgs.sa_named(o, 7n), SlashArgs.sa_last(t, 0n), SlashArgs.sa_last(t, 1n), SlashArgs.sa_last(t, 2n), SlashArgs.sa_last(t, 3n), SlashArgs.sa_cmds(t), SlashArgs.sa_last(t, 5n), SlashArgs.sa_last(t, 6n), SlashArgs.sa_last(t, 7n)))))

# options read without an error, in turn, before an error: the error
def sao.fold_err(os: List<&2, SlashArgs.SaOpt>, +e: String, +ok: {SlashArgs.sa_opts_ok(os) == True{} : Bool}) -> {sao.fold(os, Sa.RErr{e}) == Sa.RErr{e} : Sa.Read}:
  match os:
    case Nil{}:
      {==}
    case +o <> +t:
      +ok1 = sao.and_l(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok)
      +h = sao.and_r(SlashArgs.sa_opt_given(o), SlashArgs.sa_is_on(SlashArgs.sa_opt_read(o)), ok1)
      Equal.trans(Sa.Read, Sa.read.then(sao.val(o), sao.fold(t, Sa.RErr{e})), Sa.read.then(sao.val(o), Sa.RErr{e}), Sa.RErr{e}, Equal.cong(Sa.Read, Sa.Read, z => Sa.read.then(sao.val(o), z), sao.fold(t, Sa.RErr{e}), Sa.RErr{e}, sao.fold_err(t, e, sao.and_r(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok))), Equal.cong(Sa.Read, Sa.Read, z => Sa.read.then(z, Sa.RErr{e}), sao.val(o), Sa.ROk{sao.spec(o <> Nil{})}, sao.val_ok(o, h)))

# the words of options whose values are given, then r: the options read
# in turn, then those of r
def sao.words(os: List<&2, SlashArgs.SaOpt>, +r: List<&2, String>, +ok: {SlashArgs.sa_opts_ok(os) == True{} : Bool}) -> {Sa.options(List.append(&2, String, SlashArgs.sa_opts_words(os), r)) == sao.fold(os, Sa.options(r)) : Sa.Read}:
  match os:
    case Nil{}:
      {==}
    case +o <> +t:
      +ok1 = sao.and_l(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok)
      +g = sao.and_l(SlashArgs.sa_opt_given(o), SlashArgs.sa_is_on(SlashArgs.sa_opt_read(o)), ok1)
      +wo = SlashArgs.sa_opt_words(o)
      +wt = SlashArgs.sa_opts_words(t)
      +x = List.append(&2, String, wt, r)
      Equal.trans(Sa.Read, Sa.options(List.append(&2, String, List.append(&2, String, wo, wt), r)), Sa.options(List.append(&2, String, wo, x)), sao.at(o, sao.fold(t, Sa.options(r))), Equal.cong(List<&2, String>, Sa.Read, z => Sa.options(z), List.append(&2, String, List.append(&2, String, wo, wt), r), List.append(&2, String, wo, x), LA.sab.lapp_assoc(wo, wt, r)), Equal.trans(Sa.Read, Sa.options(List.append(&2, String, wo, x)), sao.at(o, Sa.options(x)), sao.at(o, sao.fold(t, Sa.options(r))), sao.one(o, x, g), Equal.cong(Sa.Read, Sa.Read, z => sao.at(o, z), Sa.options(x), sao.fold(t, Sa.options(r)), sao.words(t, r, sao.and_r(SlashArgs.sa_opt_ok(o), SlashArgs.sa_opts_ok(t), ok)))))

# `/autonomous on` takes the options
# ---------------------------------

def sao.some(m: Maybe<&2, String>) -> {Sa.some(Sa.Lim, sao.lims(m)) == SlashArgs.sa_is_some(m) : Bool}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def sao.lim_t(m: Maybe<&2, String>) -> {Sa.unl(sao.lims(m)) == SlashArgs.sa_limit(m, True{}) : Maybe<&2, Sa.Lim>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def sao.lim_f(m: Maybe<&2, String>) -> {sao.lims(m) == SlashArgs.sa_limit(m, False{}) : Maybe<&2, Sa.Lim>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

# the confs of equal fields are equal
def sao.cf6(+a0: Maybe<&2, Sa.Lim>, +b0: Maybe<&2, Sa.Lim>, e0: {a0 == b0 : Maybe<&2, Sa.Lim>}, +a1: Maybe<&2, Sa.Lim>, +b1: Maybe<&2, Sa.Lim>, e1: {a1 == b1 : Maybe<&2, Sa.Lim>}, +a2: Maybe<&2, Sa.Lim>, +b2: Maybe<&2, Sa.Lim>, e2: {a2 == b2 : Maybe<&2, Sa.Lim>}, +a3: Maybe<&2, Sa.Lim>, +b3: Maybe<&2, Sa.Lim>, e3: {a3 == b3 : Maybe<&2, Sa.Lim>}, +a4: Maybe<&2, Sa.Gates>, +b4: Maybe<&2, Sa.Gates>, e4: {a4 == b4 : Maybe<&2, Sa.Gates>}, +a5: Maybe<&2, String>, +b5: Maybe<&2, String>, e5: {a5 == b5 : Maybe<&2, String>}) -> {Sa.Conf{a0, a1, a2, a3, a4, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}:
  %Equal.sym(Maybe<&2, Sa.Lim>, a0, b0, e0) : {Sa.Conf{_, a1, a2, a3, a4, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  %Equal.sym(Maybe<&2, Sa.Lim>, a1, b1, e1) : {Sa.Conf{b0, _, a2, a3, a4, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  %Equal.sym(Maybe<&2, Sa.Lim>, a2, b2, e2) : {Sa.Conf{b0, b1, _, a3, a4, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  %Equal.sym(Maybe<&2, Sa.Lim>, a3, b3, e3) : {Sa.Conf{b0, b1, b2, _, a4, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  %Equal.sym(Maybe<&2, Sa.Gates>, a4, b4, e4) : {Sa.Conf{b0, b1, b2, b3, _, a5} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  %Equal.sym(Maybe<&2, String>, a5, b5, e5) : {Sa.Conf{b0, b1, b2, b3, b4, _} == Sa.Conf{b0, b1, b2, b3, b4, b5} : Sa.Conf}
  {==}

# the limits, n when a limit is named
def sao.limits(n: Bool, +m0: Maybe<&2, String>, +m1: Maybe<&2, String>, +m2: Maybe<&2, String>, +m3: Maybe<&2, String>, +g: Maybe<&2, Sa.Gates>, +q: Maybe<&2, String>) -> {Sa.conf.limits(n, sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), g, q) == Sa.Conf{SlashArgs.sa_limit(m0, n), SlashArgs.sa_limit(m1, n), SlashArgs.sa_limit(m2, n), SlashArgs.sa_limit(m3, n), g, q} : Sa.Conf}:
  match n:
    case True{}:
      sao.cf6(Sa.unl(sao.lims(m0)), SlashArgs.sa_limit(m0, True{}), sao.lim_t(m0), Sa.unl(sao.lims(m1)), SlashArgs.sa_limit(m1, True{}), sao.lim_t(m1), Sa.unl(sao.lims(m2)), SlashArgs.sa_limit(m2, True{}), sao.lim_t(m2), Sa.unl(sao.lims(m3)), SlashArgs.sa_limit(m3, True{}), sao.lim_t(m3), g, g, {==}, q, q, {==})
    case False{}:
      sao.cf6(sao.lims(m0), SlashArgs.sa_limit(m0, False{}), sao.lim_f(m0), sao.lims(m1), SlashArgs.sa_limit(m1, False{}), sao.lim_f(m1), sao.lims(m2), SlashArgs.sa_limit(m2, False{}), sao.lim_f(m2), sao.lims(m3), SlashArgs.sa_limit(m3, False{}), sao.lim_f(m3), g, g, {==}, q, q, {==})

# a limit is named
def sao.named(m0: Maybe<&2, String>, m1: Maybe<&2, String>, m2: Maybe<&2, String>, m3: Maybe<&2, String>) -> {Bool.or(Bool.or(Sa.some(Sa.Lim, sao.lims(m0)), Sa.some(Sa.Lim, sao.lims(m1))), Bool.or(Sa.some(Sa.Lim, sao.lims(m2)), Sa.some(Sa.Lim, sao.lims(m3)))) == Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))) : Bool}:
  match m0:
    case Some{x0}:
      match m1:
        case Some{x1}:
          match m2:
            case Some{x2}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
        case None{}:
          match m2:
            case Some{x2}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
    case None{}:
      match m1:
        case Some{x1}:
          match m2:
            case Some{x2}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
        case None{}:
          match m2:
            case Some{x2}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}
            case None{}:
              match m3:
                case Some{x3}:
                  {==}
                case None{}:
                  {==}

# the gates, named when a command, a retry or a timeout was
def sao.gates(cm: List<&2, String>, m5: Maybe<&2, String>, m6: Maybe<&2, String>) -> {Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)) == SlashArgs.sa_gates(cm, SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)) : Maybe<&2, Sa.Gates>}:
  match cm:
    case c <> u:
      {==}
    case Nil{}:
      match m5:
        case Some{x0}:
          match m6:
            case Some{x1}:
              {==}
            case None{}:
              {==}
        case None{}:
          match m6:
            case Some{x1}:
              {==}
            case None{}:
              {==}

# `/autonomous on` takes the options named as R9 says
def sao.conf(+m0: Maybe<&2, String>, +m1: Maybe<&2, String>, +m2: Maybe<&2, String>, +m3: Maybe<&2, String>, +cm: List<&2, String>, +m5: Maybe<&2, String>, +m6: Maybe<&2, String>, +m7: Maybe<&2, String>) -> {Sa.conf(sao.spec.of(m0, m1, m2, m3, cm, m5, m6, m7)) == SlashArgs.sa_conf_of(m0, m1, m2, m3, cm, m5, m6, m7) : Sa.Conf}:
  +dm7 = SlashArgs.sa_digits_of(m7)
  Equal.trans(Sa.Conf, Sa.conf.limits(Bool.or(Bool.or(Sa.some(Sa.Lim, sao.lims(m0)), Sa.some(Sa.Lim, sao.lims(m1))), Bool.or(Sa.some(Sa.Lim, sao.lims(m2)), Sa.some(Sa.Lim, sao.lims(m3)))), sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7), Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7), SlashArgs.sa_conf_of(m0, m1, m2, m3, cm, m5, m6, m7), Equal.cong(Bool, Sa.Conf, z => Sa.conf.limits(z, sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7), Bool.or(Bool.or(Sa.some(Sa.Lim, sao.lims(m0)), Sa.some(Sa.Lim, sao.lims(m1))), Bool.or(Sa.some(Sa.Lim, sao.lims(m2)), Sa.some(Sa.Lim, sao.lims(m3)))), Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), sao.named(m0, m1, m2, m3)), Equal.trans(Sa.Conf, Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7), Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), SlashArgs.sa_gates(cm, SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7), SlashArgs.sa_conf_of(m0, m1, m2, m3, cm, m5, m6, m7), Equal.cong(Maybe<&2, Sa.Gates>, Sa.Conf, z => Sa.conf.limits(Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), sao.lims(m0), sao.lims(m1), sao.lims(m2), sao.lims(m3), z, dm7), Sa.conf.gates(cm, Bool.or(SlashArgs.sa_is_some(m5), SlashArgs.sa_is_some(m6)), SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), SlashArgs.sa_gates(cm, SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), sao.gates(cm, m5, m6)), sao.limits(Bool.or(Bool.or(SlashArgs.sa_is_some(m0), SlashArgs.sa_is_some(m1)), Bool.or(SlashArgs.sa_is_some(m2), SlashArgs.sa_is_some(m3))), m0, m1, m2, m3, SlashArgs.sa_gates(cm, SlashArgs.sa_digits_of(m5), SlashArgs.sa_digits_of(m6)), dm7)))

# Errors
# ------

# an answer that is an error is the error read
def sao.keep_err(r: Sa.Read, os: List<&2, SlashArgs.SaOpt>, ok: {SlashArgs.sa_opts_ok(os) == True{} : Bool}, h: {SlashArgs.sa_is_err(Sa.auto.on(r)) == True{} : Bool}) -> {Sa.auto.on(sao.fold(os, r)) == Sa.auto.on(r) : Sa.Auto}:
  match r:
    case Sa.ROk{x}:
      LStg.stg.absurdF({Sa.auto.on(sao.fold(os, Sa.ROk{x})) == Sa.auto.on(Sa.ROk{x}) : Sa.Auto}, h)
    case Sa.RErr{+e}:
      Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), sao.fold(os, Sa.RErr{e}), Sa.RErr{e}, sao.fold_err(os, e, ok))

def sao.bad.go(a: Sa.Read, x: Sa.Read, h: {SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(a, PSO.sop.none()))) == False{} : Bool}) -> {Sa.auto.on(Sa.read.then(a, x)) == Sa.auto.on(Sa.read.then(a, PSO.sop.none())) : Sa.Auto}:
  match a:
    case Sa.ROk{y}:
      LStg.stg.absurd({Sa.auto.on(Sa.read.then(Sa.ROk{y}, x)) == Sa.auto.on(Sa.read.then(Sa.ROk{y}, PSO.sop.none())) : Sa.Auto}, h)
    case Sa.RErr{e}:
      {==}

# an option whose value R8 refuses, then x: R8's error for it
def sao.bad(o: SlashArgs.SaOpt, x: Sa.Read, b: {SlashArgs.sa_is_on(SlashArgs.sa_opt_read(o)) == False{} : Bool}) -> {Sa.auto.on(sao.at(o, x)) == SlashArgs.sa_opt_read(o) : Sa.Auto}:
  match o:
    case SlashArgs.SaOpt{p, +k, e, +v}:
      +a = Sa.opt.value(k, SlashArgs.sa_flag_name(k), v)
      +sv = PSO.sop.v(k, v)
      Equal.trans(Sa.Auto, Sa.auto.on(Sa.read.then(a, x)), Sa.auto.on(Sa.read.then(a, PSO.sop.none())), SlashArgs.sa_option(k, v), sao.bad.go(a, x, Equal.trans(Bool, SlashArgs.sa_is_on(Sa.auto.on(Sa.read.then(a, PSO.sop.none()))), SlashArgs.sa_is_on(SlashArgs.sa_option(k, v)), False{}, Equal.cong(Sa.Auto, Bool, z => SlashArgs.sa_is_on(z), Sa.auto.on(Sa.read.then(a, PSO.sop.none())), SlashArgs.sa_option(k, v), sv), b)), sv)
