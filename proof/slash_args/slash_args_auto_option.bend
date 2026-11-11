# eukhe: the proof of LAW slash_args_auto_option
#
# PROOF: by the flag (and its prefix): the one option word's flag, name,
# index and value compute through its text up to the `=` (LAA.saa.opts);
# the value v is read as R8 says for that flag (sop.v: LAA.saa.ungroup,
# then the cases of its tests), or is missing when empty.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./base/auto.bend as LAA

def sop.none() -> Sa.Read:
  Sa.ROk{Sa.opts.none()}

def sop.lim2(b2: Bool, k: Nat, d: String) -> {Sa.auto.on(Sa.read.then(Sa.opt.lim(SlashArgs.sa_flag_name(k), Sa.lim.num(b2, d), k), sop.none())) == SlashArgs.sa_option.lim(k, SlashArgs.sa_flag_name(k), False{}, b2, d) : Sa.Auto}:
  match b2:
    case True{}:
      match k:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case False{}:
      {==}

def sop.lim(b: Bool, k: Nat, +v: String) -> {Sa.auto.on(Sa.read.then(Sa.opt.lim(SlashArgs.sa_flag_name(k), Sa.lim.of(b, v), k), sop.none())) == SlashArgs.sa_option.lim(k, SlashArgs.sa_flag_name(k), b, Sa.u64(Sa.ungroup(v)), Sa.ungroup(v)) : Sa.Auto}:
  match b:
    case True{}:
      match k:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case False{}:
      sop.lim2(Sa.u64(Sa.ungroup(v)), k, Sa.ungroup(v))

def sop.gopts(d: String, r: Bool) -> Sa.Opts:
  match r:
    case True{}:
      Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, Some{d}, None{}, None{}}
    case False{}:
      Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, None{}, Some{d}, None{}}

def sop.gate(b2: Bool, +n: String, d: String, r: Bool) -> {Sa.auto.on(Sa.read.then(Sa.opt.gate(n, b2, d, r), sop.none())) == SlashArgs.sa_option.num(b2, n, Sa.conf(Sa.opts.then(sop.gopts(d, r), Sa.opts.none()))) : Sa.Auto}:
  match b2:
    case True{}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def sop.keep(b: Bool, d: String) -> {Sa.auto.on(Sa.read.then(Sa.opt.keep(b, d), sop.none())) == SlashArgs.sa_option.keep(b, d) : Sa.Auto}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# R8's reading of a non-empty value for the flag k
def sop.v(k: Nat, +v: String) -> {Sa.auto.on(Sa.read.then(Sa.opt.value(k, SlashArgs.sa_flag_name(k), v), sop.none())) == SlashArgs.sa_option(k, v) : Sa.Auto}:
  match k:
    case 0n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(0n, "max-continuations", v), sop.none())) == SlashArgs.sa_option.lim(0n, "max-continuations", String.eq(String.to_lower(v), "unlimited"), Sa.u64(_), _) : Sa.Auto}
      sop.lim(String.eq(String.to_lower(v), "unlimited"), 0n, v)
    case 1n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(1n, "max-turns", v), sop.none())) == SlashArgs.sa_option.lim(1n, "max-turns", String.eq(String.to_lower(v), "unlimited"), Sa.u64(_), _) : Sa.Auto}
      sop.lim(String.eq(String.to_lower(v), "unlimited"), 1n, v)
    case 2n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(2n, "max-tokens", v), sop.none())) == SlashArgs.sa_option.lim(2n, "max-tokens", String.eq(String.to_lower(v), "unlimited"), Sa.u64(_), _) : Sa.Auto}
      sop.lim(String.eq(String.to_lower(v), "unlimited"), 2n, v)
    case 3n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(3n, "timeout-ms", v), sop.none())) == SlashArgs.sa_option.lim(3n, "timeout-ms", String.eq(String.to_lower(v), "unlimited"), Sa.u64(_), _) : Sa.Auto}
      sop.lim(String.eq(String.to_lower(v), "unlimited"), 3n, v)
    case 4n:
      {==}
    case 5n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(5n, "gate-retries", v), sop.none())) == SlashArgs.sa_option.num(Sa.u64(_), "gate-retries", Sa.Conf{None{}, None{}, None{}, None{}, Some{Sa.Gates{None{}, Some{_}, None{}}}, None{}}) : Sa.Auto}
      sop.gate(Sa.u64(Sa.ungroup(v)), "gate-retries", Sa.ungroup(v), True{})
    case 6n:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(6n, "gate-timeout-ms", v), sop.none())) == SlashArgs.sa_option.num(Sa.u64(_), "gate-timeout-ms", Sa.Conf{None{}, None{}, None{}, None{}, Some{Sa.Gates{None{}, None{}, Some{_}}}, None{}}) : Sa.Auto}
      sop.gate(Sa.u64(Sa.ungroup(v)), "gate-timeout-ms", Sa.ungroup(v), False{})
    case 7n+u:
      %LAA.saa.ungroup(v) : {Sa.auto.on(Sa.read.then(Sa.opt.value(7n+u, "subagent-keep-alive-ms", v), sop.none())) == SlashArgs.sa_option.keep(Sa.keep_ok(_), _) : Sa.Auto}
      sop.keep(Sa.keep_ok(Sa.ungroup(v)), Sa.ungroup(v))

# the one option's value, by v: missing when empty, else R8's reading
def sop.took(v: String, +raw: String, k: Nat) -> {Sa.auto.on(Sa.step.took(String.is_empty(v), False{}, raw, k, SlashArgs.sa_flag_name(k), v, sop.none(), sop.none())) == SlashArgs.sa_option_or_missing(k, raw, v) : Sa.Auto}:
  match v:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      sop.v(k, SCon{c, t})

def sop.k7(v: String, +raw: String, u: Nat) -> {SlashArgs.sa_option_or_missing(7n, raw, v) == SlashArgs.sa_option_or_missing(7n+u, raw, v) : Sa.Auto}:
  match v:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# the law at one prefix and flag (their text computes)
def sop.case(+s: String, +w: String, +p: Bool, +k: Nat, +v: String, ws: {Sa.words(s) == [w, String.append(SlashArgs.sa_prefix(p), String.append(SlashArgs.sa_flag_name(k), SCon{'=', v}))] : List<&2, String>}, on: {SlashArgs.sa_on(String.to_lower(w)) == True{} : Bool}, eb: {String.starts_with(String.append(SlashArgs.sa_prefix(p), String.append(SlashArgs.sa_flag_name(k), SCon{'=', v})), "--") == True{} : Bool}, ec: {Sa.auto.on(Sa.step(True{}, String.append(SlashArgs.sa_prefix(p), String.append(SlashArgs.sa_flag_name(k), SCon{'=', v})), Nil{}, Sa.options(Nil{}), LA.sab.snd(Sa.reads(Nil{})))) == Sa.auto.on(Sa.step.took(String.is_empty(v), False{}, String.append(SlashArgs.sa_prefix(p), SlashArgs.sa_flag_name(k)), k, SlashArgs.sa_flag_name(k), v, sop.none(), sop.none())) : Sa.Auto}) -> {Sa.auto(s) == SlashArgs.sa_option_or_missing(k, String.append(SlashArgs.sa_prefix(p), SlashArgs.sa_flag_name(k)), v) : Sa.Auto}:
  +x = String.append(SlashArgs.sa_prefix(p), String.append(SlashArgs.sa_flag_name(k), SCon{'=', v}))
  +raw = String.append(SlashArgs.sa_prefix(p), SlashArgs.sa_flag_name(k))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.step(True{}, x, Nil{}, Sa.options(Nil{}), LA.sab.snd(Sa.reads(Nil{})))), SlashArgs.sa_option_or_missing(k, raw, v), LAA.saa.opts(s, w, x, Nil{}, ws, on, True{}, eb), Equal.trans(Sa.Auto, Sa.auto.on(Sa.step(True{}, x, Nil{}, Sa.options(Nil{}), LA.sab.snd(Sa.reads(Nil{})))), Sa.auto.on(Sa.step.took(String.is_empty(v), False{}, raw, k, SlashArgs.sa_flag_name(k), v, sop.none(), sop.none())), SlashArgs.sa_option_or_missing(k, raw, v), ec, sop.took(v, raw, k)))

def SlashArgs.slash_args_auto_option(s, w, p, k, v, ws, on):
  match p:
    case True{}:
      match k:
        case 0n:
          sop.case(s, w, True{}, 0n, v, ws, on, {==}, {==})
        case 1n:
          sop.case(s, w, True{}, 1n, v, ws, on, {==}, {==})
        case 2n:
          sop.case(s, w, True{}, 2n, v, ws, on, {==}, {==})
        case 3n:
          sop.case(s, w, True{}, 3n, v, ws, on, {==}, {==})
        case 4n:
          sop.case(s, w, True{}, 4n, v, ws, on, {==}, {==})
        case 5n:
          sop.case(s, w, True{}, 5n, v, ws, on, {==}, {==})
        case 6n:
          sop.case(s, w, True{}, 6n, v, ws, on, {==}, {==})
        case 7n+u:
          Equal.trans(Sa.Auto, Sa.auto(s), SlashArgs.sa_option_or_missing(7n, "--autonomous-subagent-keep-alive-ms", v), SlashArgs.sa_option_or_missing(7n+u, "--autonomous-subagent-keep-alive-ms", v), sop.case(s, w, True{}, 7n, v, ws, on, {==}, {==}), sop.k7(v, "--autonomous-subagent-keep-alive-ms", u))
    case False{}:
      match k:
        case 0n:
          sop.case(s, w, False{}, 0n, v, ws, on, {==}, {==})
        case 1n:
          sop.case(s, w, False{}, 1n, v, ws, on, {==}, {==})
        case 2n:
          sop.case(s, w, False{}, 2n, v, ws, on, {==}, {==})
        case 3n:
          sop.case(s, w, False{}, 3n, v, ws, on, {==}, {==})
        case 4n:
          sop.case(s, w, False{}, 4n, v, ws, on, {==}, {==})
        case 5n:
          sop.case(s, w, False{}, 5n, v, ws, on, {==}, {==})
        case 6n:
          sop.case(s, w, False{}, 6n, v, ws, on, {==}, {==})
        case 7n+u:
          Equal.trans(Sa.Auto, Sa.auto(s), SlashArgs.sa_option_or_missing(7n, "--subagent-keep-alive-ms", v), SlashArgs.sa_option_or_missing(7n+u, "--subagent-keep-alive-ms", v), sop.case(s, w, False{}, 7n, v, ws, on, {==}, {==}), sop.k7(v, "--subagent-keep-alive-ms", u))
