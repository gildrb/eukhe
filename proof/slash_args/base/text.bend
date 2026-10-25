# eukhe: lemmas of area slash_args: the text helpers, the words and the
# `/goal` answer of bend/slash_args.bend are the spec helpers of
# laws/slash_args/model.bend (by induction on the text, case by case on
# the Bool or constructor each helper matches)

import Base
import ../../../bend/slash_args.bend as Sa
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/gateway_answer.bend as GatewayAnswer
import ../../../laws/slash_args/model.bend as SlashArgs
import ../../gateway_answer/base.bend as LGa

# Text
# ----

def sab.trim_start.at(b: Bool, c: Char, t: String, r: String) -> {Sa.trim_start.at(b, c, t, r) == SlashArgs.sa_trim_start.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.trim_start(s: String) -> {Sa.trim_start(s) == SlashArgs.sa_trim_start(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.trim_start(t), SlashArgs.sa_trim_start(t), sab.trim_start(t)) : {Sa.trim_start.at(Ga.space(c), c, t, _) == SlashArgs.sa_trim_start.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_trim_start(t)) : String}
      %Equal.sym(Bool, Ga.space(c), GatewayAnswer.ga_white(c), LGa.gab.space(c)) : {Sa.trim_start.at(_, c, t, SlashArgs.sa_trim_start(t)) == SlashArgs.sa_trim_start.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_trim_start(t)) : String}
      sab.trim_start.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_trim_start(t))

def sab.trim_end.at(b: Bool, c: Char, r: String) -> {Sa.trim_end.at(b, c, r) == SlashArgs.sa_trim_end.at(b, c, r) : String}:
  match b:
    case True{}:
      match r:
        case SNil{}:
          {==}
        case SCon{x, u}:
          {==}
    case False{}:
      {==}

def sab.trim_end(s: String) -> {Sa.trim_end(s) == SlashArgs.sa_trim_end(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.trim_end(t), SlashArgs.sa_trim_end(t), sab.trim_end(t)) : {Sa.trim_end.at(Ga.space(c), c, _) == SlashArgs.sa_trim_end.at(GatewayAnswer.ga_white(c), c, SlashArgs.sa_trim_end(t)) : String}
      %Equal.sym(Bool, Ga.space(c), GatewayAnswer.ga_white(c), LGa.gab.space(c)) : {Sa.trim_end.at(_, c, SlashArgs.sa_trim_end(t)) == SlashArgs.sa_trim_end.at(GatewayAnswer.ga_white(c), c, SlashArgs.sa_trim_end(t)) : String}
      sab.trim_end.at(GatewayAnswer.ga_white(c), c, SlashArgs.sa_trim_end(t))

def sab.trim(+s: String) -> {Sa.trim(s) == SlashArgs.sa_trim(s) : String}:
  %Equal.sym(String, Sa.trim_start(s), SlashArgs.sa_trim_start(s), sab.trim_start(s)) : {Sa.trim_end(_) == SlashArgs.sa_trim(s) : String}
  sab.trim_end(SlashArgs.sa_trim_start(s))

def sab.cut.at(b: Bool, c: Char, t: String, r: Sa.Cut) -> {Sa.cut.at(b, c, t, r) == SlashArgs.sa_cut.at(b, c, t, r) : Sa.Cut}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case Sa.Cut{h, u}:
          {==}

def sab.cut(s: String) -> {Sa.cut(s) == SlashArgs.sa_cut(s) : Sa.Cut}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Sa.Cut, Sa.cut(t), SlashArgs.sa_cut(t), sab.cut(t)) : {Sa.cut.at(Ga.space(c), c, t, _) == SlashArgs.sa_cut.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_cut(t)) : Sa.Cut}
      %Equal.sym(Bool, Ga.space(c), GatewayAnswer.ga_white(c), LGa.gab.space(c)) : {Sa.cut.at(_, c, t, SlashArgs.sa_cut(t)) == SlashArgs.sa_cut.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_cut(t)) : Sa.Cut}
      sab.cut.at(GatewayAnswer.ga_white(c), c, t, SlashArgs.sa_cut(t))

def sab.after_eq.at(b: Bool, t: String, r: String) -> {Sa.after_eq.at(b, t, r) == SlashArgs.sa_after_eq.at(b, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.after_eq(s: String) -> {Sa.after_eq(s) == SlashArgs.sa_after_eq(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.after_eq(t), SlashArgs.sa_after_eq(t), sab.after_eq(t)) : {Sa.after_eq.at(Char.is_eq(c, '='), t, _) == SlashArgs.sa_after_eq.at(Char.is_eq(c, '='), t, SlashArgs.sa_after_eq(t)) : String}
      sab.after_eq.at(Char.is_eq(c, '='), t, SlashArgs.sa_after_eq(t))

def sab.all_digits(s: String) -> {Sa.all_digits(s) == SlashArgs.sa_all_digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Sa.all_digits(t), SlashArgs.sa_all_digits(t), sab.all_digits(t)) : {Bool.and(Char.is_digit(c), _) == Bool.and(Char.is_digit(c), SlashArgs.sa_all_digits(t)) : Bool}
      {==}

def sab.positive(s: String) -> {Sa.positive(s) == SlashArgs.sa_positive(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Sa.all_digits(t), SlashArgs.sa_all_digits(t), sab.all_digits(t)) : {Bool.and(Bool.not(Char.is_eq(c, '0')), Bool.and(Char.is_digit(c), _)) == SlashArgs.sa_positive(SCon{c, t}) : Bool}
      {==}

def sab.u64(+s: String) -> {Sa.u64(s) == SlashArgs.sa_u64(s) : Bool}:
  %Equal.sym(Bool, Sa.positive(s), SlashArgs.sa_positive(s), sab.positive(s)) : {Bool.and(_, Bool.or(Nat.is_lt(String.length(s), 20n), Bool.and(Nat.is_eq(String.length(s), 20n), String.is_le(s, "18446744073709551615")))) == SlashArgs.sa_u64(s) : Bool}
  {==}

def sab.ungroup.at(b: Bool, c: Char, r: String) -> {Sa.ungroup.at(b, c, r) == SlashArgs.sa_ungroup.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.ungroup(s: String) -> {Sa.ungroup(s) == SlashArgs.sa_ungroup(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.ungroup(t), SlashArgs.sa_ungroup(t), sab.ungroup(t)) : {Sa.ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, _) == SlashArgs.sa_ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, SlashArgs.sa_ungroup(t)) : String}
      sab.ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, SlashArgs.sa_ungroup(t))

# Words
# -----

def sab.push(cur: String, quoted: Bool, done: List<&2, String>) -> {Sa.tok.push(cur, quoted, done) == SlashArgs.sa_tok.push(cur, quoted, done) : List<&2, String>}:
  match cur:
    case SNil{}:
      match quoted:
        case True{}:
          {==}
        case False{}:
          {==}
    case SCon{c, t}:
      {==}

def sab.in_quote(same: Bool, q: Char, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> {Sa.tok.in_quote(same, q, c, cur, quoted, done) == SlashArgs.sa_tok.in_quote(same, q, c, cur, quoted, done) : Sa.Tok}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def sab.out(opens: Bool, white: Bool, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> {Sa.tok.out(opens, white, c, cur, quoted, done) == SlashArgs.sa_tok.out(opens, white, c, cur, quoted, done) : Sa.Tok}:
  match opens:
    case True{}:
      {==}
    case False{}:
      match white:
        case True{}:
          %Equal.sym(List<&2, String>, Sa.tok.push(cur, quoted, done), SlashArgs.sa_tok.push(cur, quoted, done), sab.push(cur, quoted, done)) : {Sa.Tok{None{}, SNil{}, False{}, _} == Sa.Tok{None{}, SNil{}, False{}, SlashArgs.sa_tok.push(cur, quoted, done)} : Sa.Tok}
          {==}
        case False{}:
          {==}

def sab.step(+c: Char, st: Sa.Tok) -> {Sa.tok.step(c, st) == SlashArgs.sa_tok.step(c, st) : Sa.Tok}:
  match st:
    case Sa.Tok{q, cur, quoted, done}:
      match q:
        case Some{+x}:
          sab.in_quote(Char.is_eq(c, x), x, c, cur, quoted, done)
        case None{}:
          %Equal.sym(Bool, Ga.space(c), GatewayAnswer.ga_white(c), LGa.gab.space(c)) : {Sa.tok.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), _, c, cur, quoted, done) == SlashArgs.sa_tok.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), GatewayAnswer.ga_white(c), c, cur, quoted, done) : Sa.Tok}
          sab.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), GatewayAnswer.ga_white(c), c, cur, quoted, done)

def sab.fin(st: Sa.Tok) -> {Sa.tok.fin(st) == SlashArgs.sa_tok.fin(st) : List<&2, String>}:
  match st:
    case Sa.Tok{q, +cur, +quoted, +done}:
      %Equal.sym(List<&2, String>, Sa.tok.push(cur, quoted, done), SlashArgs.sa_tok.push(cur, quoted, done), sab.push(cur, quoted, done)) : {List.reverse(&2, String, _) == List.reverse(&2, String, SlashArgs.sa_tok.push(cur, quoted, done)) : List<&2, String>}
      {==}

def sab.go(s: String, +st: Sa.Tok) -> {Sa.tok.go(s, st) == SlashArgs.sa_tok.go(s, st) : List<&2, String>}:
  match s:
    case SNil{}:
      sab.fin(st)
    case SCon{+c, t}:
      %Equal.sym(Sa.Tok, Sa.tok.step(c, st), SlashArgs.sa_tok.step(c, st), sab.step(c, st)) : {Sa.tok.go(t, _) == SlashArgs.sa_tok.go(t, SlashArgs.sa_tok.step(c, st)) : List<&2, String>}
      sab.go(t, SlashArgs.sa_tok.step(c, st))

def sab.words(s: String) -> {Sa.words(s) == SlashArgs.sa_words(s) : List<&2, String>}:
  sab.go(s, Sa.Tok{None{}, SNil{}, False{}, Nil{}})

# /goal
# -----

def sab.objective.at(empty: Bool, long: Bool, o: String, b: Maybe<&2, String>) -> {Sa.goal.objective.at(empty, long, o, b) == SlashArgs.sa_goal.objective.at(empty, long, o, b) : Sa.Goal}:
  match empty:
    case True{}:
      {==}
    case False{}:
      match long:
        case True{}:
          {==}
        case False{}:
          {==}

def sab.objective(+o: String, +b: Maybe<&2, String>) -> {Sa.goal.objective(o, b) == SlashArgs.sa_goal.objective(o, b) : Sa.Goal}:
  %Equal.sym(String, Sa.trim(o), SlashArgs.sa_trim(o), sab.trim(o)) : {Sa.goal.objective.at(String.is_empty(_), Bool.not(Nat.is_le(String.length(_), 4000n)), _, b) == SlashArgs.sa_goal.objective(o, b) : Sa.Goal}
  +t = SlashArgs.sa_trim(o)
  sab.objective.at(String.is_empty(t), Bool.not(Nat.is_le(String.length(t), 4000n)), t, b)

def sab.budget(ok: Bool, +v: String, +o: String) -> {Sa.goal.budget(ok, v, o) == SlashArgs.sa_goal.budget(ok, v, o) : Sa.Goal}:
  match ok:
    case True{}:
      sab.objective(o, Some{v})
    case False{}:
      {==}

def sab.spaced(c: Sa.Cut) -> {Sa.goal.spaced(c) == SlashArgs.sa_goal.spaced(c) : Sa.Goal}:
  match c:
    case Sa.Cut{+v, u}:
      match u:
        case SNil{}:
          {==}
        case SCon{w, +o}:
          %Equal.sym(Bool, Sa.u64(v), SlashArgs.sa_u64(v), sab.u64(v)) : {Sa.goal.budget(_, v, o) == SlashArgs.sa_goal.budget(SlashArgs.sa_u64(v), v, o) : Sa.Goal}
          sab.budget(SlashArgs.sa_u64(v), v, o)

def sab.flag(bare: Bool, eq: Bool, +first: String, +tail: String, +rest: String) -> {Sa.goal.flag(bare, eq, first, tail, rest) == SlashArgs.sa_goal.flag(bare, eq, first, tail, rest) : Sa.Goal}:
  match bare:
    case True{}:
      %Equal.sym(String, Sa.trim_start(tail), SlashArgs.sa_trim_start(tail), sab.trim_start(tail)) : {Sa.goal.spaced(Sa.cut(_)) == SlashArgs.sa_goal.spaced(SlashArgs.sa_cut(SlashArgs.sa_trim_start(tail))) : Sa.Goal}
      %Equal.sym(Sa.Cut, Sa.cut(SlashArgs.sa_trim_start(tail)), SlashArgs.sa_cut(SlashArgs.sa_trim_start(tail)), sab.cut(SlashArgs.sa_trim_start(tail))) : {Sa.goal.spaced(_) == SlashArgs.sa_goal.spaced(SlashArgs.sa_cut(SlashArgs.sa_trim_start(tail))) : Sa.Goal}
      sab.spaced(SlashArgs.sa_cut(SlashArgs.sa_trim_start(tail)))
    case False{}:
      match eq:
        case True{}:
          %Equal.sym(String, Sa.after_eq(first), SlashArgs.sa_after_eq(first), sab.after_eq(first)) : {Sa.goal.budget(Sa.u64(_), _, tail) == SlashArgs.sa_goal.budget(SlashArgs.sa_u64(SlashArgs.sa_after_eq(first)), SlashArgs.sa_after_eq(first), tail) : Sa.Goal}
          %Equal.sym(Bool, Sa.u64(SlashArgs.sa_after_eq(first)), SlashArgs.sa_u64(SlashArgs.sa_after_eq(first)), sab.u64(SlashArgs.sa_after_eq(first))) : {Sa.goal.budget(_, SlashArgs.sa_after_eq(first), tail) == SlashArgs.sa_goal.budget(SlashArgs.sa_u64(SlashArgs.sa_after_eq(first)), SlashArgs.sa_after_eq(first), tail) : Sa.Goal}
          sab.budget(SlashArgs.sa_u64(SlashArgs.sa_after_eq(first)), SlashArgs.sa_after_eq(first), tail)
        case False{}:
          sab.objective(rest, None{})

def sab.start(c: Sa.Cut, +rest: String) -> {Sa.goal.start(c, rest) == SlashArgs.sa_goal.start(c, rest) : Sa.Goal}:
  match c:
    case Sa.Cut{+first, +tail}:
      sab.flag(Bool.or(String.eq(first, "--budget"), String.eq(first, "--token-budget")), Bool.or(String.starts_with(first, "--budget="), String.starts_with(first, "--token-budget=")), first, tail, rest)

def sab.kw(status: Bool, clear: Bool, pause: Bool, resume: Bool, +rest: String) -> {Sa.goal.kw(status, clear, pause, resume, rest) == SlashArgs.sa_goal.kw(status, clear, pause, resume, rest) : Sa.Goal}:
  match status:
    case True{}:
      {==}
    case False{}:
      match clear:
        case True{}:
          {==}
        case False{}:
          match pause:
            case True{}:
              {==}
            case False{}:
              match resume:
                case True{}:
                  {==}
                case False{}:
                  %Equal.sym(Sa.Cut, Sa.cut(rest), SlashArgs.sa_cut(rest), sab.cut(rest)) : {Sa.goal.start(_, rest) == SlashArgs.sa_goal.start(SlashArgs.sa_cut(rest), rest) : Sa.Goal}
                  sab.start(SlashArgs.sa_cut(rest), rest)

def sab.goal(+args: String) -> {Sa.goal(args) == SlashArgs.sa_goal(args) : Sa.Goal}:
  %Equal.sym(String, Sa.trim(args), SlashArgs.sa_trim(args), sab.trim(args)) : {Sa.goal.of(_, String.to_lower(_)) == SlashArgs.sa_goal(args) : Sa.Goal}
  +rest = SlashArgs.sa_trim(args)
  +l = String.to_lower(rest)
  sab.kw(Bool.or(String.is_empty(l), String.eq(l, "status")), Bool.or(String.eq(l, "clear"), String.eq(l, "stop")), String.eq(l, "pause"), String.eq(l, "resume"), rest)
