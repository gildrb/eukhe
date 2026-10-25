# eukhe: the laws of area glob

import Base
import ../bend/glob.bend as G
import ../bend/ffi_glob.bend as FG
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (G1) Glob patterns
# ------------------
# bend/glob.bend: the glob patterns eukhe matches paths and model names
# with, in place of the Rust `globset` crate 0.4.20 (GlobBuilder with
# backslash_escape on, empty_alternates and allow_unclosed_class off;
# literal_separator and case_insensitive per caller). Every pattern,
# text, option and list is free.
#
# R1 (parse): a pattern parses as globset's parser reads it: `?` any,
#     `*` zero or more, `**` per globset's rules (a recursive prefix
#     first in a branch before `/` or the end, a recursive suffix after
#     `/` at the end or before a group's `,` or `}`, a `/**/` between
#     separators, two stars elsewhere), `[..]` a class (`!`/`^` negates,
#     `]` and `-` first are chars, `a-z` a range, a trailing `-` a char,
#     `\` no escape inside), `{a,b}` alternates (nested; `,` outside a
#     group is a char), `\c` the char c, any other char itself. Errors:
#     `[` with no `]` (unclosed class), a range whose end is below its
#     start (invalid range, the start then the end), `}` outside a group
#     (unopened), a group open at the end (unclosed), `\` at the end
#     (dangling); the first error met reading left to right, the unclosed
#     group last. A group branch whose regex is empty is dropped; a group
#     with no branch left matches the empty text. Pinned by
#     glob_parse_plain and glob_parse_example, and by a differential run
#     against globset (bend/glob.bend header); the rest of R1 is trusted.
# R2 (regex): the pattern means globset's regex of its tokens: a char its
#     UTF-8 bytes; `?` one byte (not `/` with literal_separator), `*` any
#     run of such bytes; a recursive prefix the empty text, `/`, or any
#     bytes then `/`; a recursive suffix `/` then any bytes; `/**/` `/` or
#     `/` any bytes `/`; a class one byte of the bytes regex-syntax reads
#     from its `\xNN` escapes (a range lo..hi: lo's bytes, then lo's last
#     byte to hi's first, then hi's other bytes), negated over bytes; an
#     alternate group any of its branches; the lone token `**` any text.
#     With case_insensitive an ASCII letter of a char or class matches
#     either case (folded before negation).
# R3 (class): a byte is of a class exactly as R2 says.
# R4 (match): a list of byte items matches a byte text when the text
#     splits into one part per item, in order: one byte of the class for
#     `One`, any run of bytes of the class (the empty run too) for `Star`.
#     A parsed pattern matches a text when one of its alternatives matches
#     the text's UTF-8 bytes whole.
# R5 (groups): a group query answers, for each group of texts (the texts
#     in order, each group as many as its size; a group past the texts
#     takes those left), whether a pattern globset accepts matches one of
#     its texts; a refused pattern matches nothing.
# R6 (allowlist): a model allowlist allows a selector when one of its
#     patterns does: the pattern trimmed of Unicode White_Space; a blank
#     one never; one with `*`, `?` or `[` as a glob (no option set) of the
#     selector or of its bare id (the text after the selector's first
#     `/`, the selector itself with none); any other when it equals one of
#     them. An empty list allows nothing.
# R7 (entry): bend/ffi_glob.bend reads the request its header spells and
#     answers R1's error, R5's, R5b's or R5c's answers or R6's answer, spelled per
#     WIRE.md; any other input answers `E glob: malformed request`.

# Spec helpers
# ------------

# R3: byte x is in one of the ranges
def sp_in(rs: List<&2, G.BR>, +x: U32) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case G.BR{lo, hi}:
          Bool.or(Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)), sp_in(t, x))

def sp_is_upper(+x: U32) -> Bool:
  Bool.and(U32.is_le(65, x), U32.is_le(x, 90))

def sp_is_lower(+x: U32) -> Bool:
  Bool.and(U32.is_le(97, x), U32.is_le(x, 122))

def sp_other_case.lo(+x: U32, lo: Bool) -> U32:
  match lo:
    case True{}:
      U32.sub(x, 32)
    case False{}:
      x

def sp_other_case.up(+x: U32, up: Bool) -> U32:
  match up:
    case True{}:
      U32.add(x, 32)
    case False{}:
      sp_other_case.lo(x, sp_is_lower(x))

# R3: the other case of an ASCII letter, any other byte itself
def sp_other_case(+x: U32) -> U32:
  sp_other_case.up(x, sp_is_upper(x))

def sp_set(+rs: List<&2, G.BR>, +x: U32, fold: Bool) -> Bool:
  match fold:
    case True{}:
      Bool.or(sp_in(rs, x), sp_in(rs, sp_other_case(x)))
    case False{}:
      sp_in(rs, x)

# R3: byte x is of the class k
def sp_bc(k: G.BC, +x: U32) -> Bool:
  match k:
    case G.BAny{}:
      True{}
    case G.BNotSl{}:
      Bool.not(U32.is_eq(x, 47))
    case G.BSet{neg, fold, rs}:
      match neg:
        case True{}:
          Bool.not(sp_set(rs, x, fold))
        case False{}:
          sp_set(rs, x, fold)

# R4: the byte text, whole, matches the items its
def sp_lang(bs: List<&2, U32>, its: List<&2, G.It>) -> Bool:
  match bs:
    case Nil{}:
      match its:
        case Nil{}:
          True{}
        case i <> k:
          match i:
            case G.One{c}:
              False{}
            case G.Star{c}:
              sp_lang(Nil{}, k)
    case +x <> +t:
      match its:
        case Nil{}:
          False{}
        case i <> +k:
          match i:
            case G.One{c}:
              Bool.and(sp_bc(c, x), sp_lang(t, k))
            case G.Star{+c}:
              Bool.or(sp_lang(x <> t, k), Bool.and(sp_bc(c, x), sp_lang(t, G.Star{c} <> k)))

# R4: one of the alternatives matches the byte text whole
def sp_any(+bs: List<&2, U32>, xs: List<&2, List<&2, G.It>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      Bool.or(sp_lang(bs, a), sp_any(bs, r))

# R2: one byte of the set rs (ASCII case folded with fold)
def sp_one(neg: Bool, fold: Bool, rs: List<&2, G.BR>) -> G.It:
  G.One{G.BSet{neg, fold, rs}}

def sp_slash() -> G.It:
  sp_one(False{}, False{}, [G.BR{47, 47}])

# R2: a char: one item per UTF-8 byte
def sp_lit(bs: List<&2, U32>, +fold: Bool) -> List<&2, G.It>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      sp_one(False{}, fold, [G.BR{b, b}]) <> sp_lit(r, fold)

# R2: each byte as a range of itself, then rest
def sp_each(bs: List<&2, U32>, rest: List<&2, G.BR>) -> List<&2, G.BR>:
  match bs:
    case Nil{}:
      rest
    case +b <> r:
      G.BR{b, b} <> sp_each(r, rest)

# R2: the bytes of a range lo..hi whose lo has the bytes b <> r (lo's
# last byte to hi's first byte hb <> ht), then rest
def sp_span(r: List<&2, U32>, +b: U32, hb: List<&2, U32>, rest: List<&2, G.BR>) -> List<&2, G.BR>:
  match r:
    case Nil{}:
      match hb:
        case Nil{}:
          G.BR{b, b} <> rest
        case h <> t:
          G.BR{b, h} <> sp_each(t, rest)
    case c <> t:
      G.BR{b, b} <> sp_span(t, c, hb, rest)

def sp_range.k(lo: List<&2, U32>, hi: List<&2, U32>, rest: List<&2, G.BR>) -> List<&2, G.BR>:
  match lo:
    case Nil{}:
      rest
    case b <> r:
      sp_span(r, b, hi, rest)

def sp_range.same(same: Bool, +lo: U32, +hi: U32, rest: List<&2, G.BR>) -> List<&2, G.BR>:
  match same:
    case True{}:
      sp_each(G.utf8(lo, Nil{}), rest)
    case False{}:
      sp_range.k(G.utf8(lo, Nil{}), G.utf8(hi, Nil{}), rest)

# R2: a class's ranges as bytes
def sp_ranges(rs: List<&2, G.Rg>) -> List<&2, G.BR>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case G.Rg{lo, hi}:
          +l = G.code(lo)
          +h = G.code(hi)
          sp_range.same(U32.is_eq(l, h), l, h, sp_ranges(t))

# R2: the class of `?` and `*`: every byte but `/` with literal_separator
def sp_byte(sep: Bool) -> G.BC:
  match sep:
    case True{}:
      G.BNotSl{}
    case False{}:
      G.BAny{}

# R2: the alternatives of one token
def sp_tok(o: G.Opts, t: G.Tok) -> List<&2, List<&2, G.It>>:
  match o:
    case G.Opts{sep, +fold}:
      match t:
        case G.TLit{c}:
          [sp_lit(G.utf8(G.code(c), Nil{}), fold)]
        case G.TAny{}:
          [[G.One{sp_byte(sep)}]]
        case G.TZom{}:
          [[G.Star{sp_byte(sep)}]]
        case G.TRPre{}:
          [Nil{}, [sp_slash()], [G.Star{G.BAny{}}, sp_slash()]]
        case G.TRSuf{}:
          [[sp_slash(), G.Star{G.BAny{}}]]
        case G.TRZom{}:
          [[sp_slash()], [sp_slash(), G.Star{G.BAny{}}, sp_slash()]]
        case G.TCls{neg, rs}:
          [[sp_one(neg, fold, sp_ranges(rs))]]

# R2: each alternative a after each alternative of the rest bs
def sp_then(+a: List<&2, G.It>, bs: List<&2, List<&2, G.It>>) -> List<&2, List<&2, G.It>>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      List.append(&2, G.It, a, b) <> sp_then(a, r)

def sp_prod(as: List<&2, List<&2, G.It>>, +bs: List<&2, List<&2, G.It>>) -> List<&2, List<&2, G.It>>:
  match as:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, List<&2, G.It>, sp_then(a, bs), sp_prod(r, bs))

# R2: the alternatives of a token list
def sp_seq(+o: G.Opts, ts: List<&2, G.Tok>) -> List<&2, List<&2, G.It>>:
  match ts:
    case Nil{}:
      [Nil{}]
    case t <> r:
      sp_prod(sp_tok(o, t), sp_seq(o, r))

def sp_alts(+o: G.Opts, xs: List<&2, List<&2, G.Tok>>) -> List<&2, List<&2, G.It>>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> r:
      List.append(&2, List<&2, G.It>, sp_seq(o, a), sp_alts(o, r))

# R2: the alternatives of a parsed pattern
def sp_items(o: G.Opts, g: G.Glob) -> List<&2, List<&2, G.It>>:
  match g:
    case G.Glob{xs, solo}:
      match solo:
        case True{}:
          [[G.Star{G.BAny{}}]]
        case False{}:
          sp_alts(o, xs)

# R5: the alternatives of the patterns globset accepts
def sp_compile.r(+o: G.Opts, r: Result<&2, &2, G.Err, G.Glob>, rest: List<&2, List<&2, G.It>>) -> List<&2, List<&2, G.It>>:
  match r:
    case Fail{e}:
      rest
    case Done{g}:
      List.append(&2, List<&2, G.It>, sp_items(o, g), rest)

def sp_compile(+o: G.Opts, ps: List<&2, String>) -> List<&2, List<&2, G.It>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      sp_compile.r(o, G.parse(p), sp_compile(o, r))

# R5: one of the texts matches one of the alternatives
def sp_hit(ss: List<&2, String>, +xs: List<&2, List<&2, G.It>>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case s <> r:
      Bool.or(sp_any(G.bytes(s), xs), sp_hit(r, xs))

# R5: per group of the sizes ks, one of its texts matches
def sp_groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, G.It>>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      sp_hit(List.take(&2, String, ss, k), xs) <> sp_groups(r, xs, List.drop(&2, String, ss, k))

# R5b: per rule of the sizes ks, one of its patterns matches a text
def sp_rules(ks: List<&2, Nat>, +o: G.Opts, +ps: List<&2, String>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      sp_hit(ss, sp_compile(o, List.take(&2, String, ps, k))) <> sp_rules(r, o, List.drop(&2, String, ps, k), ss)

# R5c: an ignore rule: its text and its code
type SpRule is Data:
  SpRule{p: String, c: Nat}

# R5c: the rules, last first
def sp_pairs(ps: List<&2, String>, cs: List<&2, Nat>, acc: List<&2, SpRule>) -> List<&2, SpRule>:
  match ps cs:
    case Nil{} cs:
      acc
    case p <> pr Nil{}:
      acc
    case p <> pr c <> cr:
      sp_pairs(pr, cr, SpRule{p, c} <> acc)

def sp_suffixes.k(sl: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match sl:
    case True{}:
      t <> rest
    case False{}:
      rest

# R5c: the text after each `/` of s
def sp_suffixes(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, +t}:
      sp_suffixes.k(U32.is_eq(Char.to_u32(c), 47), t, sp_suffixes(t))

def sp_glob_rule.hit(anchored: Bool, +path: String, +xs: List<&2, List<&2, G.It>>) -> Bool:
  match anchored:
    case True{}:
      sp_any(G.bytes(path), xs)
    case False{}:
      sp_hit(path <> sp_suffixes(path), xs)

# R5c: a glob rule decides (Some: ignored or kept) or not
def sp_glob_rule.k(skip: Bool, hit: Bool, negated: Bool) -> Maybe<&2, Bool>:
  match skip:
    case True{}:
      None{}
    case False{}:
      match hit:
        case True{}:
          Some{Bool.not(negated)}
        case False{}:
          None{}

def sp_glob_rule(+c: Nat, +p: String, +path: String, +dir: Bool) -> Maybe<&2, Bool>:
  +xs = sp_compile(G.Opts{True{}, False{}}, [p])
  sp_glob_rule.k(Bool.and(Nat.is_eq(Nat.div(c, 4n), 1n), Bool.not(dir)), sp_glob_rule.hit(Nat.is_eq(Nat.mod(c, 2n), 1n), path, xs), Nat.is_eq(Nat.mod(Nat.div(c, 2n), 2n), 1n))

def sp_prefix_rule(under: Bool) -> Maybe<&2, Bool>:
  match under:
    case True{}:
      Some{True{}}
    case False{}:
      None{}

def sp_rule.k(glob: Bool, all: Bool, +c: Nat, +p: String, +path: String, +dir: Bool) -> Maybe<&2, Bool>:
  match glob:
    case True{}:
      sp_glob_rule(c, p, path, dir)
    case False{}:
      match all:
        case True{}:
          sp_prefix_rule(String.starts_with(path, p))
        case False{}:
          None{}

# R5c: one rule's decision on the path
def sp_rule(+c: Nat, +p: String, +path: String, +dir: Bool) -> Maybe<&2, Bool>:
  sp_rule.k(Nat.is_lt(c, 8n), Nat.is_eq(c, 8n), c, p, path, dir)

def sp_decide.k(m: Maybe<&2, Bool>, rest: Bool) -> Bool:
  match m:
    case None{}:
      rest
    case Some{b}:
      b

# R5c: the first rule (last first) that decides, else not ignored
def sp_decide(rs: List<&2, SpRule>, +path: String, +dir: Bool) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      match r:
        case SpRule{p, c}:
          sp_decide.k(sp_rule(c, p, path, dir), sp_decide(t, path, dir))

# R5c: an entry is a directory when its last char is `/`
def sp_dir(e: String) -> Bool:
  match e:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          U32.is_eq(Char.to_u32(c), 47)
        case SCon{x, u}:
          sp_dir(SCon{x, u})

def sp_path.last(c: Char, sl: Bool) -> String:
  match sl:
    case True{}:
      ""
    case False{}:
      SCon{c, SNil{}}

# R5c: an entry's path: without its last `/`
def sp_path(e: String) -> String:
  match e:
    case SNil{}:
      ""
    case SCon{+c, t}:
      match t:
        case SNil{}:
          sp_path.last(c, U32.is_eq(Char.to_u32(c), 47))
        case SCon{x, u}:
          SCon{c, sp_path(SCon{x, u})}

# R5c: per entry, whether the rules ignore it
def sp_ignored(+ps: List<&2, String>, +cs: List<&2, Nat>, es: List<&2, String>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> r:
      sp_decide(sp_pairs(ps, cs, Nil{}), sp_path(e), sp_dir(e)) <> sp_ignored(ps, cs, r)

# R6: Unicode White_Space
def sp_ws(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def sp_drop_ws.k(w: Bool, c: Char, t: String, rest: String) -> String:
  match w:
    case True{}:
      rest
    case False{}:
      SCon{c, t}

# R6: s without its leading white space
def sp_drop_ws(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sp_drop_ws.k(sp_ws(c), c, t, sp_drop_ws(t))

# R6: s trimmed at both ends
def sp_trim(s: String) -> String:
  String.reverse(sp_drop_ws(String.reverse(sp_drop_ws(s))))

# R6: s holds `*`, `?` or `[`
def sp_wild(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), sp_wild(t))

def sp_bare.k(sl: Bool, t: String, rest: String) -> String:
  match sl:
    case True{}:
      t
    case False{}:
      rest

# R6: the text after the first `/` of s, or whole (orig) with none
def sp_bare.go(s: String, +orig: String) -> String:
  match s:
    case SNil{}:
      orig
    case SCon{c, +t}:
      sp_bare.k(U32.is_eq(Char.to_u32(c), 47), t, sp_bare.go(t, orig))

def sp_bare(+s: String) -> String:
  sp_bare.go(s, s)

def sp_allow.g(r: Result<&2, &2, G.Err, G.Glob>, +sel: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{g}:
      +xs = {sp_items(G.Opts{False{}, False{}}, g) : List<&2, List<&2, G.It>>}
      Bool.or(sp_any(G.bytes(sel), xs), sp_any(G.bytes(sp_bare(sel)), xs))

def sp_allow.w(w: Bool, +sel: String, +p: String) -> Bool:
  match w:
    case True{}:
      sp_allow.g(G.parse(p), sel)
    case False{}:
      Bool.or(String.eq(p, sel), String.eq(p, sp_bare(sel)))

def sp_allow.e(e: Bool, +sel: String, +p: String) -> Bool:
  match e:
    case True{}:
      False{}
    case False{}:
      sp_allow.w(sp_wild(p), sel, p)

# R6: one pattern allows the selector
def sp_allow1(+sel: String, p: String) -> Bool:
  +t = sp_trim(p)
  sp_allow.e(String.is_empty(t), sel, t)

# R6: one pattern of the list allows the selector
def sp_allowed(+sel: String, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> r:
      Bool.or(sp_allow1(sel, p), sp_allowed(sel, r))

# R1: no char of s is special outside a class (`*?[{},\`)
def sp_plain(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      Bool.and(Bool.not(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))), sp_plain(t))

# R1: the literal tokens of s
def sp_lits(s: String) -> List<&2, G.Tok>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      G.TLit{c} <> sp_lits(t)

# R7: the spelling of a request and of its reply

def sp_w_req(q: FG.Req, rest: String) -> String:
  match q:
    case FG.QCheck{p}:
      Wr.put_nat(0n, Wr.put_str(p, rest))
    case FG.QMatch{sep, fold, ps, ss, ks}:
      Wr.put_nat(1n, Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_strs(ss, LawsBase.wire_spell_nats(ks, rest))))))
    case FG.QAllow{sel, ps}:
      Wr.put_nat(2n, Wr.put_str(sel, LawsBase.wire_spell_strs(ps, rest)))
    case FG.QRules{sep, fold, ps, ss, ks}:
      Wr.put_nat(3n, Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_strs(ss, LawsBase.wire_spell_nats(ks, rest))))))
    case FG.QIgnore{ps, cs, es}:
      Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, LawsBase.wire_spell_strs(es, rest))))

def sp_w_err(e: G.Err) -> String:
  match e:
    case G.EClass{}:
      Wr.put_nat(0n, "")
    case G.ERange{lo, hi}:
      Wr.put_nat(1n, Wr.put_nat(U32.to_nat(Char.to_u32(lo)), Wr.put_nat(U32.to_nat(Char.to_u32(hi)), "")))
    case G.EUnopened{}:
      Wr.put_nat(2n, "")
    case G.EUnclosed{}:
      Wr.put_nat(3n, "")
    case G.EEscape{}:
      Wr.put_nat(4n, "")

def sp_w_check(r: Result<&2, &2, G.Err, G.Glob>) -> String:
  match r:
    case Fail{e}:
      Wr.put_nat(1n, sp_w_err(e))
    case Done{g}:
      Wr.put_nat(0n, "")

def sp_w_bools.items(xs: List<&2, Bool>) -> String:
  match xs:
    case Nil{}:
      ""
    case b <> r:
      Wr.put_bool(b, sp_w_bools.items(r))

def sp_w_bools(+xs: List<&2, Bool>) -> String:
  Wr.put_nat(List.length(&2, Bool, xs), sp_w_bools.items(xs))

def sp_w_reply(q: FG.Req) -> String:
  match q:
    case FG.QCheck{p}:
      sp_w_check(G.parse(p))
    case FG.QMatch{sep, fold, ps, ss, ks}:
      sp_w_bools(sp_groups(ks, sp_compile(G.Opts{sep, fold}, ps), ss))
    case FG.QAllow{sel, ps}:
      Wr.put_bool(sp_allowed(sel, ps), "")
    case FG.QRules{sep, fold, ps, ss, ks}:
      sp_w_bools(sp_rules(ks, G.Opts{sep, fold}, ps, ss))
    case FG.QIgnore{ps, cs, es}:
      sp_w_bools(sp_ignored(ps, cs, es))

# every number and length of the request fits the wire
def sp_fit_req(q: FG.Req) -> Bool:
  match q:
    case FG.QCheck{p}:
      LawsBase.wire_fits(String.length(p))
    case FG.QMatch{sep, fold, ps, ss, +ks}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))))
    case FG.QAllow{sel, ps}:
      Bool.and(LawsBase.wire_fits(String.length(sel)), LawsBase.wire_strs_fit(ps))
    case FG.QRules{sep, fold, ps, ss, +ks}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))))
    case FG.QIgnore{ps, +cs, es}:
      Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es)))

# Laws: the matcher
# -----------------

# LAW glob_class (R3): every byte is of every class exactly as R3 says
# EXCLUDES: `[^/]` that takes `/`, a negated class not negated, a fold
#   that folds a byte that is no ASCII letter or misses one case, a range
#   read with its ends excluded
law glob_class:
  for k: G.BC
  for +x: U32
  {G.bc(k, x) == sp_bc(k, x) : Bool}

# LAW glob_full (R4): the table matcher answers, for every byte text and
# list of items, what the split of R4 answers
# EXCLUDES: a run that stops too early or too late, a one-byte item that
#   takes none or two, an item skipped, a prefix taken for the whole text,
#   a star whose class is not checked
law glob_full:
  for +bs: List<&2, U32>
  for +its: List<&2, G.It>
  {G.full(bs, its) == sp_lang(bs, its) : Bool}

# LAW glob_items (R2): every parsed pattern, under every option, means
# globset's regex of its tokens
# EXCLUDES: `*` or `?` that crosses `/` with literal_separator (or not
#   without it), a recursive token read as another, a class range read
#   per char instead of per byte, a fold applied when not asked, the lone
#   `**` read as a recursive prefix
law glob_items:
  for o: G.Opts
  for g: G.Glob
  {G.items(o, g) == sp_items(o, g) : List<&2, List<&2, G.It>>}

# LAW glob_matches (R2, R4): every parsed pattern matches every text
# exactly when one of its regex alternatives matches the text's bytes
# EXCLUDES: an alternative skipped, a text matched by chars instead of
#   bytes
law glob_matches:
  for +o: G.Opts
  for +g: G.Glob
  for +s: String
  {G.matches(o, g, s) == sp_any(G.bytes(s), sp_items(o, g)) : Bool}

# LAW glob_groups (R5): every group query answers R5
# EXCLUDES: a refused pattern that matches, a group that takes another
#   group's texts, a group answered by its first text only, a missing or
#   extra answer
law glob_groups:
  for +o: G.Opts
  for +ps: List<&2, String>
  for +ss: List<&2, String>
  for +ks: List<&2, Nat>
  {G.match_groups(o, ps, ss, ks) == sp_groups(ks, sp_compile(o, ps), ss) : List<&2, Bool>}

# LAW glob_rules (R5b): every rules query answers R5b
# EXCLUDES: a rule that takes another rule's patterns, a refused pattern
#   that matches, a missing or extra answer
law glob_rules:
  for +ks: List<&2, Nat>
  for +o: G.Opts
  for +ps: List<&2, String>
  for +ss: List<&2, String>
  {G.rules(ks, o, ps, ss) == sp_rules(ks, o, ps, ss) : List<&2, Bool>}

# LAW glob_ignored (R5c): every ignore query answers R5c
# EXCLUDES: the first rule deciding instead of the last, a negated rule
#   that ignores, a directory-only rule applied to a file, an anchored rule
#   matched at any depth or an unanchored one only whole, a prefix rule
#   that misses a path under it, a code read as another, an entry's
#   trailing `/` kept in its path
law glob_ignored:
  for +ps: List<&2, String>
  for +cs: List<&2, Nat>
  for +es: List<&2, String>
  {G.ignored(ps, cs, es) == sp_ignored(ps, cs, es) : List<&2, Bool>}

# LAW glob_ignore_example (R5c): anchor: an unanchored name at any depth,
# an anchored glob, a directory-only rule, a negated rule, a prefix rule
# EXCLUDES: an ignore matcher that drifts from the Rust one it replaced
law glob_ignore_example:
  {G.ignored(["venv", "a/*.md", "x", "keep.md", "sub/"], [0n, 1n, 4n, 2n, 8n], ["venv/", "x/venv", "a/b.md", "a/c/b.md", "keep.md", "venv", "sub/z", "x/", "x"]) == [True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}] : List<&2, Bool>}

# LAW glob_allowed (R6): every allowlist decides every selector as R6
# says
# EXCLUDES: an untrimmed pattern, a blank pattern that matches, a glob
#   matched only against the selector or only the bare id, a bare id cut
#   at the last `/`, a plain pattern globbed, a glob with options set, an
#   empty list that allows
law glob_allowed:
  for +sel: String
  for +ps: List<&2, String>
  {G.allowed(sel, ps) == sp_allowed(sel, ps) : Bool}

# LAW glob_parse_plain (R1): a pattern with no special char parses to its
# chars as literals, one alternative
# EXCLUDES: an ordinary char read as special, a char lost or doubled, the
#   chars reordered
law glob_parse_plain:
  for +s: String
  for h: {sp_plain(s) == True{} : Bool}
  {G.parse(s) == Done{G.Glob{[sp_lits(s)], False{}}} : Result<&2, &2, G.Err, G.Glob>}

# LAW glob_parse_example (R1): anchor: each construct and each error
# EXCLUDES: a parser that drifts from globset
law glob_parse_example:
  {[G.parse("a?*"), G.parse("**/a"), G.parse("a/**"), G.parse("a/**/b"), G.parse("**"), G.parse("a**"), G.parse("[!]a-]"), G.parse("[a-]"), G.parse("\\*,"), G.parse("{a,}b"), G.parse("{,}"), G.parse("{a,b/**}")] == [Done{G.Glob{[[G.TLit{'a'}, G.TAny{}, G.TZom{}]], False{}}}, Done{G.Glob{[[G.TRPre{}, G.TLit{'a'}]], False{}}}, Done{G.Glob{[[G.TLit{'a'}, G.TRSuf{}]], False{}}}, Done{G.Glob{[[G.TLit{'a'}, G.TRZom{}, G.TLit{'b'}]], False{}}}, Done{G.Glob{[[G.TRPre{}]], True{}}}, Done{G.Glob{[[G.TLit{'a'}, G.TZom{}, G.TZom{}]], False{}}}, Done{G.Glob{[[G.TCls{True{}, [G.Rg{']', ']'}, G.Rg{'a', 'a'}, G.Rg{'-', '-'}]}]], False{}}}, Done{G.Glob{[[G.TCls{False{}, [G.Rg{'a', 'a'}, G.Rg{'-', '-'}]}]], False{}}}, Done{G.Glob{[[G.TLit{'*'}, G.TLit{','}]], False{}}}, Done{G.Glob{[[G.TLit{'a'}, G.TLit{'b'}]], False{}}}, Done{G.Glob{[Nil{}], False{}}}, Done{G.Glob{[[G.TLit{'a'}], [G.TLit{'b'}, G.TRSuf{}]], False{}}}] : List<&2, Result<&2, &2, G.Err, G.Glob>>}

# LAW glob_parse_error_example (R1): anchor: each error, the first met
# EXCLUDES: an error read as another, a refused pattern accepted
law glob_parse_error_example:
  {[G.check("a["), G.check("[z-a]"), G.check("a}"), G.check("{a"), G.check("a\\"), G.check("[b-a]}")] == [Some{G.EClass{}}, Some{G.ERange{'z', 'a'}}, Some{G.EUnopened{}}, Some{G.EUnclosed{}}, Some{G.EEscape{}}, Some{G.ERange{'b', 'a'}}] : List<&2, Maybe<&2, G.Err>>}

# LAW glob_utf8_example (R2): anchor: the UTF-8 bytes of a char of one,
# two, three and four bytes
# EXCLUDES: a text matched by code points, a wrong byte split
law glob_utf8_example:
  {[G.utf8(97, Nil{}), G.utf8(233, Nil{}), G.utf8(8364, Nil{}), G.utf8(128512, Nil{})] == [[97], [195, 169], [226, 130, 172], [240, 159, 152, 128]] : List<&2, List<&2, U32>>}

# LAW glob_match_example (R1-R4): anchor: the cases of the Rust tests
# EXCLUDES: a matcher that drifts from globset
law glob_match_example:
  {[G.match_groups(G.Opts{True{}, False{}}, ["*.rs", "**/*.md", "??", "[a"], ["src/main.rs", "main.rs", "a/b/c.md", "é", "README.MD", "x"], [1n, 1n, 1n, 1n, 2n]), G.match_groups(G.Opts{True{}, True{}}, ["*.md"], ["README.MD"], [1n]), G.match_groups(G.Opts{False{}, False{}}, ["{,a}b", "a/**"], ["b", "a"], [1n, 1n])] == [[False{}, True{}, True{}, True{}, False{}], [True{}], [False{}, False{}]] : List<&2, List<&2, Bool>>}

# LAW glob_allow_example (R6): anchor: the cases of the Rust tests
# EXCLUDES: an allowlist that drifts from the Rust one it replaced
law glob_allow_example:
  {[G.allowed("p/i/g", ["p/i/g"]), G.allowed("p/i/g", ["i/g"]), G.allowed("p/i/g", ["g"]), G.allowed("p/i/g", ["p/*"]), G.allowed("p/i/g", [" i/* "]), G.allowed("z/g", ["p/*"]), G.allowed("z/g5", ["z/g?"]), G.allowed("p/i/g", []), G.allowed("p/i/g", ["  "]), G.allowed("p/i/g", ["["])] == [True{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}

# Laws: the entry (R7)
# --------------------

# LAW glob_entry_answers (R7): the entry answers every request Rust
# spells, every number and length within the wire, with the spelled answer
# of the spec
# EXCLUDES: the fields read in another order, a request read as another,
#   an error spelled with another tag, a default
law glob_entry_answers:
  for +q: FG.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FG.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW glob_entry_reads (R7): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law glob_entry_reads:
  for +q: FG.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FG.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FG.Req>}

# LAW glob_entry_exact (R7): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown question, a
#   malformed field or list, input left over)
law glob_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FG.ffi(s)) == False{} : Bool}
  exs r: FG.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW glob_entry_refuses (R7): every error the entry answers is exactly
# `E glob: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law glob_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FG.ffi(s)) == True{} : Bool}
  {FG.ffi(s) == Wr.err("glob: malformed request") : String}

# LAW glob_entry_example (R7): anchor: the wire strings Rust sends and the
# replies it reads; an unknown question, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law glob_entry_example:
  {[FG.ffi("0,4,a{b,"), FG.ffi("0,5,[z-a]"), FG.ffi("0,4,*.rs"), FG.ffi("1,TF2,4,*.rs7,**/*.md3,4,a.rs3,b/c4,x.md2,1,2,"), FG.ffi("2,3,z/g1,3,z/*"), FG.ffi("3,TT2,5,gpt-*1,x2,5,GPT-51,b1,2,"), FG.ffi("4,2,4,venv1,x2,0,4,3,4,venv2,x/5,x/abc"), FG.ffi("5,"), FG.ffi("0,1,ax")] == ["1,3,", "1,1,122,97,", "0,", "2,TT", "T", "1,T", "3,TTF", Wr.err("glob: malformed request"), Wr.err("glob: malformed request")] : List<&2, String>}
