# eukhe: lemmas of the model_name proofs about M.dash (R8): the code's
# separator test is the PropList one (mnz.sep); a text with no separator
# is kept (mnz.plain); a text a ++ t dashes as a, then t from the state a
# leaves (mnz.app, mnz.last); a run of separators after a separator adds
# nothing (mnz.run_skip); a text that starts with no separator dashes the
# same after a separator or not (mnz.start_free).

import Base
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA

# the code's separator test is the spec's
def mnz.sep(c: Char) -> {M.is_sep(c) == ModelName.sp_sep(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def mnz.sep_f(+c: Char, h: {Bool.not(ModelName.sp_sep(c)) == True{} : Bool}) -> {M.is_sep(c) == False{} : Bool}:
  Equal.trans(Bool, M.is_sep(c), ModelName.sp_sep(c), False{}, mnz.sep(c), LA.mnb.not_t(ModelName.sp_sep(c), h))

# a text with no separator is kept, after a separator or not
def mnz.plain(s: String, run: Bool, h: {ModelName.sp_no_sep(s) == True{} : Bool}) -> {M.dash.go(s, run) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +hh = h
      %Equal.sym(Bool, M.is_sep(x), False{}, mnz.sep_f(x, LA.mnb.and_l(Bool.not(ModelName.sp_sep(x)), ModelName.sp_no_sep(t), hh))) : {M.dash.at(_, run, x, q => M.dash.go(t, q)) == SCon{x, t} : String}
      LA.mnb.cons_eq(x, M.dash.go(t, False{}), t, mnz.plain(t, False{}, LA.mnb.and_r(Bool.not(ModelName.sp_sep(x)), ModelName.sp_no_sep(t), hh)))

# whether the char before the text after a is a separator (run: before a)
def mnz.last(a: String, run: Bool) -> Bool:
  match a:
    case SNil{}:
      run
    case SCon{x, t}:
      mnz.last(t, M.is_sep(x))

def mnz.app_at(b: Bool, run: Bool, +x: Char, -u: String, -t: String, ihT: {M.dash.go(String.append(u, t), True{}) == String.append(M.dash.go(u, True{}), M.dash.go(t, mnz.last(u, True{}))) : String}, ihF: {M.dash.go(String.append(u, t), False{}) == String.append(M.dash.go(u, False{}), M.dash.go(t, mnz.last(u, False{}))) : String}) -> {M.dash.at(b, run, x, q => M.dash.go(String.append(u, t), q)) == String.append(M.dash.at(b, run, x, q => M.dash.go(u, q)), M.dash.go(t, mnz.last(u, b))) : String}:
  match b:
    case True{}:
      match run:
        case True{}:
          ihT
        case False{}:
          LA.mnb.cons_eq('-', M.dash.go(String.append(u, t), True{}), String.append(M.dash.go(u, True{}), M.dash.go(t, mnz.last(u, True{}))), ihT)
    case False{}:
      LA.mnb.cons_eq(x, M.dash.go(String.append(u, t), False{}), String.append(M.dash.go(u, False{}), M.dash.go(t, mnz.last(u, False{}))), ihF)

# a ++ t dashes as a, then t from the state a leaves
def mnz.app(a: String, -t: String, run: Bool) -> {M.dash.go(String.append(a, t), run) == String.append(M.dash.go(a, run), M.dash.go(t, mnz.last(a, run))) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +u}:
      mnz.app_at(M.is_sep(x), run, x, u, t, mnz.app(u, t, True{}), mnz.app(u, t, False{}))

def mnz.last_free(u: String, +x: Char, -run: Bool, h: {ModelName.sp_ends_free(SCon{x, u}) == True{} : Bool}) -> {mnz.last(SCon{x, u}, run) == False{} : Bool}:
  match u:
    case SNil{}:
      mnz.sep_f(x, h)
    case SCon{+y, +w}:
      mnz.last_free(w, y, M.is_sep(x), h)

# a text that ends with no separator leaves no separator before what follows
def mnz.last_f(a: String, h: {ModelName.sp_ends_free(a) == True{} : Bool}) -> {mnz.last(a, False{}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, u}:
      mnz.last_free(u, x, False{}, h)

# after a separator, a run of separators adds nothing
def mnz.run_skip(r: String, -b: String, h: {ModelName.sp_all_sep(r) == True{} : Bool}) -> {M.dash.go(String.append(r, b), True{}) == M.dash.go(b, True{}) : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      +hh = h
      %Equal.sym(Bool, M.is_sep(x), True{}, Equal.trans(Bool, M.is_sep(x), ModelName.sp_sep(x), True{}, mnz.sep(x), LA.mnb.and_l(ModelName.sp_sep(x), ModelName.sp_all_sep(t), hh))) : {M.dash.at(_, True{}, x, q => M.dash.go(String.append(t, b), q)) == M.dash.go(b, True{}) : String}
      mnz.run_skip(t, b, LA.mnb.and_r(ModelName.sp_sep(x), ModelName.sp_all_sep(t), hh))

def mnz.free_at(sx: Bool, +x: Char, -t: String, he: {sx == False{} : Bool}) -> {M.dash.at(sx, True{}, x, q => M.dash.go(t, q)) == M.dash.at(sx, False{}, x, q => M.dash.go(t, q)) : String}:
  match sx:
    case True{}:
      LA.mnb.absurd({M.dash.at(True{}, True{}, x, q => M.dash.go(t, q)) == M.dash.at(True{}, False{}, x, q => M.dash.go(t, q)) : String}, he)
    case False{}:
      {==}

# a text that starts with no separator dashes the same after a separator
def mnz.start_free(b: String, h: {ModelName.sp_starts_free(b) == True{} : Bool}) -> {M.dash.go(b, True{}) == M.dash.go(b, False{}) : String}:
  match b:
    case SNil{}:
      {==}
    case SCon{+x, t}:
      mnz.free_at(M.is_sep(x), x, t, mnz.sep_f(x, h))
