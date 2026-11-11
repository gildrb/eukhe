# eukhe: lemmas the proofs of area skill_load share: the code's char and
# text tests answer the laws' White_Space, name and hyphen rules; its
# messages are the laws' rules in order; its trim (two reversals) drops
# what the laws' drop at the start and at the end drop; its first line is
# the laws' first line that is not blank; a string that may be missing
# reads back.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ../../laws/wire.bend as Wire

# UTF-8 lengths
# -------------

def sl.u8code(a: Bool, b: Bool, c: Bool) -> {Sk.utf8.code(a, b, c) == SkillLoad.sl_utf8.pick(a, 1n, SkillLoad.sl_utf8.pick(b, 2n, SkillLoad.sl_utf8.pick(c, 3n, 4n))) : Nat}:
  match a b c:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the code's length of a char is the laws'
def sl.u8len(c: Char) -> {Sk.utf8(c) == SkillLoad.sl_utf8(c) : Nat}:
  match c:
    case Chr{+x}:
      sl.u8code(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

def sl.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, sl.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

def sl.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), sl.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# b + (u + n) == (u + b) + n
def sl.swap(b: Nat, +u: Nat, +n: Nat) -> {Nat.add(b, Nat.add(u, n)) == Nat.add(Nat.add(u, b), n) : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(u, 0n), u, sl.add_zero(u)) : {Nat.add(u, n) == Nat.add(_, n) : Nat}
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.add(u, 1n+p), 1n+Nat.add(u, p), sl.add_succ(u, p)) : {1n+Nat.add(p, Nat.add(u, n)) == Nat.add(_, n) : Nat}
      %Equal.sym(Nat, Nat.add(p, Nat.add(u, n)), Nat.add(Nat.add(u, p), n), sl.swap(p, u, n)) : {1n+_ == 1n+Nat.add(Nat.add(u, p), n) : Nat}
      {==}

# the code's byte count after n is n plus the laws'
def sl.bytes(s: String, +n: Nat) -> {Sk.bytes(s, n) == Nat.add(SkillLoad.sl_bytes(s), n) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Nat, Sk.bytes(t, Nat.add(Sk.utf8(c), n)), Nat.add(SkillLoad.sl_bytes(t), Nat.add(Sk.utf8(c), n)), sl.bytes(t, Nat.add(Sk.utf8(c), n))) : {_ == Nat.add(Nat.add(SkillLoad.sl_utf8(c), SkillLoad.sl_bytes(t)), n) : Nat}
      %Equal.sym(Nat, Sk.utf8(c), SkillLoad.sl_utf8(c), sl.u8len(c)) : {Nat.add(SkillLoad.sl_bytes(t), Nat.add(_, n)) == Nat.add(Nat.add(SkillLoad.sl_utf8(c), SkillLoad.sl_bytes(t)), n) : Nat}
      sl.swap(SkillLoad.sl_bytes(t), SkillLoad.sl_utf8(c), n)

# the code's byte count of s is the laws'
def sl.bytes0(+s: String) -> {Sk.bytes(s, 0n) == SkillLoad.sl_bytes(s) : Nat}:
  Equal.trans(Nat, Sk.bytes(s, 0n), Nat.add(SkillLoad.sl_bytes(s), 0n), SkillLoad.sl_bytes(s), sl.bytes(s, 0n), sl.add_zero(SkillLoad.sl_bytes(s)))

# Chars and texts
# ---------------

def sl.ws(c: Char) -> {Sk.ws(c) == SkillLoad.sl_white(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def sl.blank(s: String) -> {Sk.blank(s) == SkillLoad.sl_blank(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sl.blank(t) : {Bool.and(Sk.ws(c), Sk.blank(t)) == Bool.and(SkillLoad.sl_white(c), _) : Bool}
      %sl.ws(c) : {Bool.and(Sk.ws(c), Sk.blank(t)) == Bool.and(_, Sk.blank(t)) : Bool}
      {==}

def sl.char(c: Char) -> {Sk.name.char(c) == SkillLoad.sl_name_char(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def sl.chars(s: String) -> {Sk.name.chars(s) == SkillLoad.sl_name_chars(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sl.chars(t) : {Bool.and(Sk.name.char(c), Sk.name.chars(t)) == Bool.and(SkillLoad.sl_name_char(c), _) : Bool}
      %sl.char(c) : {Bool.and(Sk.name.char(c), Sk.name.chars(t)) == Bool.and(_, Sk.name.chars(t)) : Bool}
      {==}

def sl.invalid.at(a: Bool, b: Bool) -> {Bool.or(Bool.not(Bool.and(a, b)), False{}) == Bool.not(Bool.and(a, b)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# R8c: the code's invalid-name test is the laws'
def sl.invalid(+s: String) -> {Bool.or(Bool.not(Sk.name.chars(s)), String.is_empty(s)) == Bool.not(SkillLoad.sl_name_ok(s)) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %sl.char(c) : {Bool.or(Bool.not(Sk.name.chars(SCon{c, t})), False{}) == Bool.not(Bool.and(_, SkillLoad.sl_name_chars(t))) : Bool}
      %sl.chars(t) : {Bool.or(Bool.not(Sk.name.chars(SCon{c, t})), False{}) == Bool.not(Bool.and(Sk.name.char(c), _)) : Bool}
      sl.invalid.at(Sk.name.char(c), Sk.name.chars(t))

def sl.sw.if(t: String, b: Bool) -> {String.starts_with.go.if(SNil{}, t, b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# R8d: s starts with "-" when its first char is '-'
def sl.sw(s: String) -> {String.starts_with(s, "-") == SkillLoad.sl_dash_first(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      sl.sw.if(t, Char.is_eq(c, '-'))

# R8d: the code's hyphen-at-an-end test is the laws'
def sl.edge(+s: String) -> {Bool.or(String.starts_with(s, "-"), String.ends_with(s, "-")) == SkillLoad.sl_edge(s) : Bool}:
  %sl.sw(s) : {Bool.or(String.starts_with(s, "-"), String.ends_with(s, "-")) == Bool.or(_, SkillLoad.sl_dash_first(String.reverse(s))) : Bool}
  %sl.sw(String.reverse(s)) : {Bool.or(String.starts_with(s, "-"), String.ends_with(s, "-")) == Bool.or(String.starts_with(s, "-"), _) : Bool}
  {==}

def sl.cif(u: String, b: Bool) -> {Bool.or(b, String.contains(u, "--")) == String.contains.if(u, "--", b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def sl.pair.step(d: Bool, +u: String) -> {Bool.or(Bool.and(d, SkillLoad.sl_dash_first(u)), String.contains(u, "--")) == String.contains.if(u, "--", String.starts_with.go.if("-", u, d)) : Bool}:
  match d:
    case False{}:
      {==}
    case True{}:
      %sl.sw(u) : {Bool.or(_, String.contains(u, "--")) == String.contains.if(u, "--", String.starts_with(u, "-")) : Bool}
      sl.cif(u, String.starts_with(u, "-"))

def sl.pair.nil(prev: Bool) -> {False{} == Bool.or(Bool.and(prev, False{}), False{}) : Bool}:
  match prev:
    case True{}:
      {==}
    case False{}:
      {==}

# a '-' after a '-' in t (prev: the char before t is '-'): the head pair
# or a "--" in t
def sl.pair.go(t: String, prev: Bool) -> {SkillLoad.sl_pair.go(t, prev) == Bool.or(Bool.and(prev, SkillLoad.sl_dash_first(t)), String.contains(t, "--")) : Bool}:
  match t:
    case SNil{}:
      sl.pair.nil(prev)
    case SCon{+c, +u}:
      +d = Char.is_eq(c, '-')
      %Equal.sym(Bool, SkillLoad.sl_pair.go(u, d), Bool.or(Bool.and(d, SkillLoad.sl_dash_first(u)), String.contains(u, "--")), sl.pair.go(u, d)) : {Bool.or(Bool.and(prev, d), _) == Bool.or(Bool.and(prev, d), String.contains(SCon{c, u}, "--")) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.and(d, SkillLoad.sl_dash_first(u)), String.contains(u, "--")), String.contains.if(u, "--", String.starts_with.go.if("-", u, d)), sl.pair.step(d, u)) : {Bool.or(Bool.and(prev, d), _) == Bool.or(Bool.and(prev, d), String.contains(SCon{c, u}, "--")) : Bool}
      {==}

# R8e: the code's consecutive-hyphen test is the laws'
def sl.pair(+s: String) -> {String.contains(s, "--") == SkillLoad.sl_pair(s) : Bool}:
  Equal.sym(Bool, SkillLoad.sl_pair(s), String.contains(s, "--"), sl.pair.go(s, False{}))

# Messages
# --------

def sl.w0(b: Bool, x: String, -xs: List<&2, String>) -> {Sk.when(b, x, xs) == List.append(&2, String, SkillLoad.sl_only(b, x), xs) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a message the code adds when b is the laws' message added when b2
def sl.w(b: Bool, -b2: Bool, x: String, -x2: String, -xs: List<&2, String>, -ys: List<&2, String>, eb: {b == b2 : Bool}, ex: {x == x2 : String}, e: {xs == ys : List<&2, String>}) -> {Sk.when(b, x, xs) == List.append(&2, String, SkillLoad.sl_only(b2, x2), ys) : List<&2, String>}:
  %eb : {Sk.when(b, x, xs) == List.append(&2, String, SkillLoad.sl_only(_, x2), ys) : List<&2, String>}
  %ex : {Sk.when(b, x, xs) == List.append(&2, String, SkillLoad.sl_only(b, _), ys) : List<&2, String>}
  %e : {Sk.when(b, x, xs) == List.append(&2, String, SkillLoad.sl_only(b, x), _) : List<&2, String>}
  sl.w0(b, x, xs)

# R8: the code's name messages are the laws' rules in order
def sl.names(+n: String, +p: String) -> {Sk.name.msgs(n, p) == List.append(&2, String, SkillLoad.sl_only(Bool.not(String.eq(n, p)), String.concat(["name \"", n, "\" does not match parent directory \"", p, "\""])), List.append(&2, String, SkillLoad.sl_only(Nat.is_lt(64n, SkillLoad.sl_bytes(n)), String.concat(["name exceeds 64 characters (", Nat.show(SkillLoad.sl_bytes(n)), ")"])), List.append(&2, String, SkillLoad.sl_only(Bool.not(SkillLoad.sl_name_ok(n)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)"), List.append(&2, String, SkillLoad.sl_only(SkillLoad.sl_edge(n), "name must not start or end with a hyphen"), List.append(&2, String, SkillLoad.sl_only(SkillLoad.sl_pair(n), "name must not contain consecutive hyphens"), Nil{}))))) : List<&2, String>}:
  +k = Sk.bytes(n, 0n)
  +u = SkillLoad.sl_bytes(n)
  +ek = sl.bytes0(n)
  +m1 = String.concat(["name \"", n, "\" does not match parent directory \"", p, "\""])
  +m3 = {"name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)" : String}
  +m4 = {"name must not start or end with a hyphen" : String}
  +m5 = {"name must not contain consecutive hyphens" : String}
  +o3 = Bool.or(Bool.not(Sk.name.chars(n)), String.is_empty(n))
  +o4 = Bool.or(String.starts_with(n, "-"), String.ends_with(n, "-"))
  +o5 = String.contains(n, "--")
  +c5 = Sk.when(o5, m5, {[] : List<&2, String>})
  +s5 = List.append(&2, String, SkillLoad.sl_only(SkillLoad.sl_pair(n), m5), Nil{})
  +c4 = Sk.when(o4, m4, c5)
  +s4 = List.append(&2, String, SkillLoad.sl_only(SkillLoad.sl_edge(n), m4), s5)
  +c3 = Sk.when(o3, m3, c4)
  +s3 = List.append(&2, String, SkillLoad.sl_only(Bool.not(SkillLoad.sl_name_ok(n)), m3), s4)
  +c2 = Sk.when(Nat.is_lt(64n, k), String.concat(["name exceeds 64 characters (", Nat.show(k), ")"]), c3)
  +s2 = List.append(&2, String, SkillLoad.sl_only(Nat.is_lt(64n, u), String.concat(["name exceeds 64 characters (", Nat.show(u), ")"])), s3)
  +e5 = sl.w(o5, SkillLoad.sl_pair(n), m5, m5, {[] : List<&2, String>}, {Nil{} : List<&2, String>}, sl.pair(n), {==}, {==})
  +e4 = sl.w(o4, SkillLoad.sl_edge(n), m4, m4, c5, s5, sl.edge(n), {==}, e5)
  +e3 = sl.w(o3, Bool.not(SkillLoad.sl_name_ok(n)), m3, m3, c4, s4, sl.invalid(n), {==}, e4)
  +e2 = sl.w(Nat.is_lt(64n, k), Nat.is_lt(64n, u), String.concat(["name exceeds 64 characters (", Nat.show(k), ")"]), String.concat(["name exceeds 64 characters (", Nat.show(u), ")"]), c3, s3, Equal.cong(Nat, Bool, z => Nat.is_lt(64n, z), k, u, ek), Equal.cong(Nat, String, z => String.concat(["name exceeds 64 characters (", Nat.show(z), ")"]), k, u, ek), e3)
  sl.w(Bool.not(String.eq(n, p)), Bool.not(String.eq(n, p)), m1, m1, c2, s2, {==}, {==}, e2)

def sl.d1(c: Bool, x: String, -xs: List<&2, String>) -> {List.append(&2, String, Sk.when(c, x, []), xs) == List.append(&2, String, SkillLoad.sl_only(c, x), xs) : List<&2, String>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.d0(b: Bool, +n: Nat, -xs: List<&2, String>) -> {List.append(&2, String, Sk.desc.msgs.go(b, n), xs) == List.append(&2, String, SkillLoad.sl_only(b, "description is required"), List.append(&2, String, SkillLoad.sl_only(Bool.and(Bool.not(b), Nat.is_lt(1024n, n)), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"])), xs)) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      sl.d1(Nat.is_lt(1024n, n), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"]), xs)

# R6, R8: the code's messages are the laws'
def sl.messages(+n: String, +p: String, +d: String) -> {List.append(&2, String, Sk.desc.msgs(d), Sk.name.msgs(n, p)) == SkillLoad.sl_messages(n, p, d) : List<&2, String>}:
  %sl.names(n, p) : {List.append(&2, String, Sk.desc.msgs(d), Sk.name.msgs(n, p)) == List.append(&2, String, SkillLoad.sl_only(SkillLoad.sl_blank(d), "description is required"), List.append(&2, String, SkillLoad.sl_only(Bool.and(Bool.not(SkillLoad.sl_blank(d)), Nat.is_lt(1024n, SkillLoad.sl_bytes(d))), String.concat(["description exceeds 1024 characters (", Nat.show(SkillLoad.sl_bytes(d)), ")"])), _)) : List<&2, String>}
  %sl.blank(d) : {List.append(&2, String, Sk.desc.msgs(d), Sk.name.msgs(n, p)) == List.append(&2, String, SkillLoad.sl_only(_, "description is required"), List.append(&2, String, SkillLoad.sl_only(Bool.and(Bool.not(_), Nat.is_lt(1024n, SkillLoad.sl_bytes(d))), String.concat(["description exceeds 1024 characters (", Nat.show(SkillLoad.sl_bytes(d)), ")"])), Sk.name.msgs(n, p))) : List<&2, String>}
  %sl.bytes0(d) : {List.append(&2, String, Sk.desc.msgs(d), Sk.name.msgs(n, p)) == List.append(&2, String, SkillLoad.sl_only(Sk.blank(d), "description is required"), List.append(&2, String, SkillLoad.sl_only(Bool.and(Bool.not(Sk.blank(d)), Nat.is_lt(1024n, _)), String.concat(["description exceeds 1024 characters (", Nat.show(_), ")"])), Sk.name.msgs(n, p))) : List<&2, String>}
  sl.d0(Sk.blank(d), Sk.bytes(d, 0n), Sk.name.msgs(n, p))

# Trim, the first line
# --------------------

def sl.tgo(t: String, b: Bool, +c: Char) -> {Sk.trim.go(t, b, c) == SkillLoad.sl_drop_start.at(b, c, t, SkillLoad.sl_drop_start(t)) : String}:
  match t:
    case SNil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case SCon{+d, +r}:
      match b:
        case True{}:
          %sl.ws(d) : {Sk.trim.go(r, Sk.ws(d), d) == SkillLoad.sl_drop_start.at(_, d, r, SkillLoad.sl_drop_start(r)) : String}
          sl.tgo(r, Sk.ws(d), d)
        case False{}:
          {==}

# the code's drop at the start is the laws'
def sl.tstart(s: String) -> {Sk.trim.start(s) == SkillLoad.sl_drop_start(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %sl.ws(c) : {Sk.trim.go(t, Sk.ws(c), c) == SkillLoad.sl_drop_start.at(_, c, t, SkillLoad.sl_drop_start(t)) : String}
      sl.tgo(t, Sk.ws(c), c)

# what the drop at the start leaves of s turned around onto acc, by what
# the drop at the end leaves of s (r)
def sl.pick(r: String, acc: String) -> String:
  match r:
    case SNil{}:
      SkillLoad.sl_drop_start(acc)
    case SCon{d, u}:
      String.reverse.go(SCon{d, u}, acc)

def sl.rev.nil(w: Bool, +c: Char, +acc: String) -> {SkillLoad.sl_drop_start.at(w, c, acc, SkillLoad.sl_drop_start(acc)) == sl.pick(SkillLoad.sl_drop_end.at(w, c, SNil{}), acc) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.rev.cons(w: Bool, +c: Char, +d: Char, +u: String, +acc: String) -> {String.reverse.go(SCon{d, u}, SCon{c, acc}) == sl.pick(SkillLoad.sl_drop_end.at(w, c, SCon{d, u}), acc) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.rev.step(+c: Char, r: String, +acc: String) -> {sl.pick(r, SCon{c, acc}) == sl.pick(SkillLoad.sl_drop_end.at(SkillLoad.sl_white(c), c, r), acc) : String}:
  match r:
    case SNil{}:
      sl.rev.nil(SkillLoad.sl_white(c), c, acc)
    case SCon{+d, +u}:
      sl.rev.cons(SkillLoad.sl_white(c), c, d, u, acc)

# x turned around onto acc, dropped at the start
def sl.rev(x: String, +acc: String) -> {SkillLoad.sl_drop_start(String.reverse.go(x, acc)) == sl.pick(SkillLoad.sl_drop_end(x), acc) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(String, SkillLoad.sl_drop_start(String.reverse.go(t, SCon{c, acc})), sl.pick(SkillLoad.sl_drop_end(t), SCon{c, acc}), sl.pick(SkillLoad.sl_drop_end(SCon{c, t}), acc), sl.rev(t, SCon{c, acc}), sl.rev.step(c, SkillLoad.sl_drop_end(t), acc))

# a turned around onto acc, turned around again: acc turned around onto a
def sl.rr(a: String, -acc: String) -> {String.reverse.go(String.reverse.go(a, acc), SNil{}) == String.reverse.go(acc, a) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      sl.rr(t, SCon{c, acc})

def sl.rev_end(r: String) -> {String.reverse(sl.pick(r, SNil{})) == r : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+d, +u}:
      sl.rr(SCon{d, u}, SNil{})

# dropping at the start of x turned around, turned back: the drop at the end
def sl.end(+x: String) -> {String.reverse(SkillLoad.sl_drop_start(String.reverse(x))) == SkillLoad.sl_drop_end(x) : String}:
  %Equal.sym(String, SkillLoad.sl_drop_start(String.reverse(x)), sl.pick(SkillLoad.sl_drop_end(x), SNil{}), sl.rev(x, SNil{})) : {String.reverse(_) == SkillLoad.sl_drop_end(x) : String}
  sl.rev_end(SkillLoad.sl_drop_end(x))

# the code's trim is the laws'
def sl.trim(+s: String) -> {Sk.trim(s) == SkillLoad.sl_trim(s) : String}:
  %Equal.sym(String, Sk.trim.start(s), SkillLoad.sl_drop_start(s), sl.tstart(s)) : {String.reverse(Sk.trim.start(String.reverse(_))) == SkillLoad.sl_trim(s) : String}
  %Equal.sym(String, Sk.trim.start(String.reverse(SkillLoad.sl_drop_start(s))), SkillLoad.sl_drop_start(String.reverse(SkillLoad.sl_drop_start(s))), sl.tstart(String.reverse(SkillLoad.sl_drop_start(s)))) : {String.reverse(_) == SkillLoad.sl_trim(s) : String}
  sl.end(SkillLoad.sl_drop_start(s))

def sl.line.go(ls: List<&2, String>, b: Bool, +l: String) -> {Sk.first.go(ls, b, l) == SkillLoad.sl_trim(SkillLoad.sl_head(List.filter.put(String, l, List.filter(~String, ~SkillLoad.sl_dark, ls), Bool.not(b)))) : String}:
  match ls:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          sl.trim(l)
    case +m <> +rest:
      match b:
        case True{}:
          %sl.blank(m) : {Sk.first.go(rest, Sk.blank(m), m) == SkillLoad.sl_trim(SkillLoad.sl_head(List.filter.put(String, m, List.filter(~String, ~SkillLoad.sl_dark, rest), Bool.not(_)))) : String}
          sl.line.go(rest, Sk.blank(m), m)
        case False{}:
          sl.trim(l)

# the code's first line is the laws'
def sl.line(ls: List<&2, String>) -> {Sk.first(ls) == SkillLoad.sl_line(ls) : String}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +rest:
      %sl.blank(l) : {Sk.first.go(rest, Sk.blank(l), l) == SkillLoad.sl_trim(SkillLoad.sl_head(List.filter.put(String, l, List.filter(~String, ~SkillLoad.sl_dark, rest), Bool.not(_)))) : String}
      sl.line.go(rest, Sk.blank(l), l)

# The entry
# ---------

def sl.items(xs: List<&2, String>, -rest: String) -> {FSk.put_strs.items(xs, rest) == LawsBase.wire_spell_strs.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %sl.items(t, rest) : {Wr.put_str(x, FSk.put_strs.items(t, rest)) == Wr.put_str(x, _) : String}
      {==}

# the entry's reply to a check is the laws' spelling of it
def sl.checked(c: Sk.Checked) -> {FSk.put_checked(c) == SkillLoad.spell_checked(c) : String}:
  match c:
    case Sk.Checked{+l, +n, +ms}:
      %sl.items(ms, "") : {Wr.put_bool(l, Wr.put_str(n, Wr.put_nat(List.length(&2, String, ms), FSk.put_strs.items(ms, "")))) == Wr.put_bool(l, Wr.put_str(n, Wr.put_nat(List.length(&2, String, ms), _))) : String}
      {==}

# a string that may be missing reads back, whatever follows it
def sl.text_rt(m: Maybe<&2, String>, +rest: String, h: {SkillLoad.text_fits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FSk.get_text(SkillLoad.spell_text(m, rest)) : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {Wr.Got{Some{x}, rest} == FSk.get_text.some(_) : Wr.Dec<Maybe<&2, String>>}
      {==}
