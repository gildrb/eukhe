# eukhe: the laws of area glob

import Base
import ../bend/glob/parse.bend as GParse
import ../bend/glob/items.bend as GItems
import ../bend/glob/match.bend as GMatch
import ../bend/glob/queries.bend as GQuery

# (G1) Glob patterns
# ------------------
# bend/glob/: the glob patterns eukhe matches paths and model names
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
#     against globset 0.4.20 (commit 539e4f490); the rest of R1 is trusted.
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
# R5b (rules): a rules query answers, for each rule (the patterns in
#     order, each rule as many as its size; a rule past the patterns takes
#     those left), whether one of its patterns globset accepts matches one
#     of the texts; a refused pattern matches nothing.
# R5c (ignore): an ignore query holds rules (a text and a code each, in
#     the order the ignore files give them; a text past the codes or a
#     code past the texts is dropped) and entries (a path; a trailing `/`
#     marks a directory and is not part of the path). Code below 8: a glob
#     (literal_separator on, no fold), bit 1 anchored (matched against the
#     whole path) else matched against the whole path or any text after a
#     `/` of it, bit 2 negated, bit 4 directories only (a file skips it);
#     a matching glob decides: ignored, kept when negated. Code 8: the
#     text is a prefix; it decides, ignored, every path that starts with
#     it (char by char, not by path component). Any other code decides
#     nothing. The last rule that decides wins; none deciding: not
#     ignored. The answer has one entry per entry, in order.
# R6 (allowlist): a model allowlist allows a selector when one of its
#     patterns does: the pattern trimmed of Unicode White_Space; a blank
#     one never; one with `*`, `?` or `[` as a glob (no option set) of the
#     selector or of its bare id (the text after the selector's first
#     `/`, the selector itself with none); any other when it equals one of
#     them. An empty list allows nothing.
# R7 (entry): bend/ffi_glob.bend reads the request its header comment
#     spells (tags, field order, error tags 0-4, a range error's two chars
#     as code points) and answers R1's error, R5's, R5b's or R5c's answers
#     or R6's answer, spelled in the wire format of WIRE.md; any other
#     input answers `E glob: malformed request`. Its laws are in
#     laws/glob/entry.bend.

# Spec helpers
# ------------
# They call bend/glob/'s class test GMatch.bc (pinned by the glob_class_*
# laws), its byte form of a text GItems.bytes and of a char GItems.utf8
# (glob_bytes_append, glob_utf8_layout, glob_utf8_ascii), its byte ranges
# of a class GItems.rgs (glob_class_range_bytes), its matcher
# GMatch.any_full / GMatch.matches (glob_full, glob_match_*,
# glob_token_*), the bare id GQuery.bare (glob_allow_bare) and the parser
# GParse.parse, trusted beyond the laws R1 names (an independent globset
# parser is not written here).

# R3: x is an ASCII letter: A-Z (65-90) or a-z (97-122)
def sp_letter(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(65, x), U32.is_le(x, 90)), Bool.and(U32.is_le(97, x), U32.is_le(x, 122)))

# R3: an ASCII letter pair: the upper case u, the lower case l
type SpCase is Data:
  SpCase{u: U32, l: U32}

# R3: two answers, one per letter of a pair
type SpTwo is Data:
  SpTwo{a: Bool, b: Bool}

# R3: the ASCII letters, each upper-case letter with its lower case
# (US-ASCII, RFC 20: a lower-case letter is its upper case + 32), the
# pairs regex-syntax's ASCII case folding `(?-u)(?i)` joins
def sp_case_pairs() -> List<&2, SpCase>:
  [SpCase{65, 97}, SpCase{66, 98}, SpCase{67, 99}, SpCase{68, 100}, SpCase{69, 101}, SpCase{70, 102}, SpCase{71, 103}, SpCase{72, 104}, SpCase{73, 105}, SpCase{74, 106}, SpCase{75, 107}, SpCase{76, 108}, SpCase{77, 109}, SpCase{78, 110}, SpCase{79, 111}, SpCase{80, 112}, SpCase{81, 113}, SpCase{82, 114}, SpCase{83, 115}, SpCase{84, 116}, SpCase{85, 117}, SpCase{86, 118}, SpCase{87, 119}, SpCase{88, 120}, SpCase{89, 121}, SpCase{90, 122}]

# R3: x is of the class of the ranges rs, unfolded and not negated
def sp_unfolded(+rs: List<&2, GItems.BR>, +x: U32) -> Bool:
  GMatch.bc(GItems.BSet{False{}, False{}, rs}, x)

# R3: per letter pair, whether each letter is of the folded class of rs
def sp_folded(+rs: List<&2, GItems.BR>, ps: List<&2, SpCase>) -> List<&2, SpTwo>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case SpCase{u, l}:
          SpTwo{GMatch.bc(GItems.BSet{False{}, True{}, rs}, u), GMatch.bc(GItems.BSet{False{}, True{}, rs}, l)} <> sp_folded(rs, t)

# R3: per letter pair, whether the letter or its other case is of the
# unfolded class of rs
def sp_either(+rs: List<&2, GItems.BR>, ps: List<&2, SpCase>) -> List<&2, SpTwo>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case SpCase{+u, +l}:
          SpTwo{Bool.or(sp_unfolded(rs, u), sp_unfolded(rs, l)), Bool.or(sp_unfolded(rs, l), sp_unfolded(rs, u))} <> sp_either(rs, t)

# R4: the byte text, whole, matches the items its
def sp_lang(bs: List<&2, U32>, its: List<&2, GItems.It>) -> Bool:
  match bs:
    case Nil{}:
      match its:
        case Nil{}:
          True{}
        case i <> k:
          match i:
            case GItems.One{c}:
              False{}
            case GItems.Star{c}:
              sp_lang(Nil{}, k)
    case +x <> +t:
      match its:
        case Nil{}:
          False{}
        case i <> +k:
          match i:
            case GItems.One{c}:
              Bool.and(GMatch.bc(c, x), sp_lang(t, k))
            case GItems.Star{+c}:
              Bool.or(sp_lang(x <> t, k), Bool.and(GMatch.bc(c, x), sp_lang(t, GItems.Star{c} <> k)))

# R2: each byte b as the range b..b
def sp_ones(bs: List<&2, U32>) -> List<&2, GItems.BR>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> t:
      GItems.BR{b, b} <> sp_ones(t)

# R2: the first byte of bs (0 for none)
def sp_head(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case b <> t:
      b

# R2: the last byte of bs (d for none)
def sp_last(bs: List<&2, U32>, d: U32) -> U32:
  match bs:
    case Nil{}:
      d
    case b <> t:
      sp_last(t, b)

# R2: the byte ranges regex-syntax reads from a class range lo..hi
# written as `\xNN` escapes (the bytes bl of lo, bh of hi): a range of
# one char is its bytes; else lo's bytes but the last, then lo's last byte
# to hi's first byte, then hi's bytes but the first
def sp_rg(same: Bool, +bl: List<&2, U32>, +bh: List<&2, U32>) -> List<&2, GItems.BR>:
  match same:
    case True{}:
      sp_ones(bl)
    case False{}:
      List.append(&2, GItems.BR, sp_ones(List.take(&2, U32, bl, Nat.sub(List.length(&2, U32, bl), 1n))), GItems.BR{sp_last(bl, 0), sp_head(bh)} <> sp_ones(List.drop(&2, U32, bh, 1n)))

# R2: the byte ranges of a class's char ranges, in order
def sp_rgs(rs: List<&2, GParse.Rg>) -> List<&2, GItems.BR>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case GParse.Rg{lo, hi}:
          +l = Char.to_u32(lo)
          +h = Char.to_u32(hi)
          List.append(&2, GItems.BR, sp_rg(U32.is_eq(l, h), GItems.utf8(l, Nil{}), GItems.utf8(h, Nil{})), sp_rgs(t))

# R2: the RFC 3629 length (section 3) of the UTF-8 form of a code below
# 0x80 (one), 0x800 (two), 0x10000 (three), any other (four)
def sp_utf8_len(one: Bool, two: Bool, three: Bool) -> Nat:
  match one:
    case True{}:
      1n
    case False{}:
      match two:
        case True{}:
          2n
        case False{}:
          match three:
            case True{}:
              3n
            case False{}:
              4n

# R2: whether the token list ts, one branch of a pattern under o, matches
# the byte text bs (the shipped matcher's answer)
def sp_m(+o: GItems.Opts, ts: List<&2, GParse.Tok>, +bs: List<&2, U32>) -> Bool:
  GMatch.any_full(bs, GItems.items(o, GParse.Glob{[ts], False{}}))

# R2: whether one of the branches xs matches bs
def sp_branches(+o: GItems.Opts, xs: List<&2, List<&2, GParse.Tok>>, +bs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case ts <> r:
      Bool.or(sp_m(o, ts, bs), sp_branches(o, r, bs))

# R2: bs split after its first i bytes, or after fewer: the token t alone
# matches the bytes before the split and ts the bytes after it
def sp_split(+o: GItems.Opts, +t: GParse.Tok, +ts: List<&2, GParse.Tok>, +bs: List<&2, U32>, i: Nat) -> Bool:
  match i:
    case 0n:
      Bool.and(sp_m(o, [t], Nil{}), sp_m(o, ts, bs))
    case 1n++j:
      Bool.or(Bool.and(sp_m(o, [t], List.take(&2, U32, bs, 1n+j)), sp_m(o, ts, List.drop(&2, U32, bs, 1n+j))), sp_split(o, t, ts, bs, j))

# R2: the byte x may stand for `?` or for a byte of `*`: any byte, `/`
# (47) excepted with literal_separator (sep)
def sp_free(sep: Bool, +x: U32) -> Bool:
  Bool.or(Bool.not(sep), Bool.not(U32.is_eq(x, 47)))

# R2: bs is one byte that sp_free lets through
def sp_one_free(+sep: Bool, bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.and(sp_free(sep, x), List.is_empty(&2, U32, t))

# R2: every byte of bs is one sp_free lets through
def sp_all_free(+sep: Bool, bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(sp_free(sep, x), sp_all_free(sep, t))

# R2: bs starts with `/`
def sp_slash_first(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case x <> t:
      U32.is_eq(x, 47)

# R2: bs ends with `/`
def sp_slash_last(bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case x <> t:
      match t:
        case Nil{}:
          U32.is_eq(x, 47)
        case y <> u:
          sp_slash_last(y <> u)

# R2: bs is one byte, of the class k
def sp_one_of(k: GItems.BC, bs: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.and(GMatch.bc(k, x), List.is_empty(&2, U32, t))

# R2: bs is exactly the bytes cs
def sp_same(cs: List<&2, U32>, bs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      List.is_empty(&2, U32, bs)
    case b <> r:
      match bs:
        case Nil{}:
          False{}
        case x <> t:
          Bool.and(U32.is_eq(x, b), sp_same(r, t))

# R2: bs is as many bytes as cs, each of the folded class of its byte of
# cs (glob_class_fold_*: that byte, or its other case for an ASCII letter)
def sp_same_fold(cs: List<&2, U32>, bs: List<&2, U32>) -> Bool:
  match cs:
    case Nil{}:
      List.is_empty(&2, U32, bs)
    case +b <> r:
      match bs:
        case Nil{}:
          False{}
        case x <> t:
          Bool.and(GMatch.bc(GItems.BSet{False{}, True{}, [GItems.BR{b, b}]}, x), sp_same_fold(r, t))

# R5: a parsed pattern matches the text s under o; a refused one nothing
def sp_parsed_hit(+o: GItems.Opts, r: Result<&2, &2, GParse.Err, GParse.Glob>, +s: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{g}:
      GMatch.matches(o, g, s)

# R5: a pattern of ps that globset accepts matches s
def sp_pat_hit(+o: GItems.Opts, ps: List<&2, String>, +s: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> r:
      Bool.or(sp_parsed_hit(o, GParse.parse(p), s), sp_pat_hit(o, r, s))

# R5: a pattern of ps that globset accepts matches a text of ss
def sp_texts_hit(+o: GItems.Opts, +ps: List<&2, String>, ss: List<&2, String>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case s <> r:
      Bool.or(sp_pat_hit(o, ps, s), sp_texts_hit(o, ps, r))

def sp_sum(ks: List<&2, Nat>) -> Nat:
  match ks:
    case Nil{}:
      0n
    case k <> r:
      Nat.add(k, sp_sum(r))

# R5, R5b: the j-th group of xs by the sizes ks: ks[j] items (or those
# left) after the first ks[0] + ... + ks[j - 1]
def sp_group(xs: List<&2, String>, +ks: List<&2, Nat>, +j: Nat) -> List<&2, String>:
  List.take(&2, String, List.drop(&2, String, xs, sp_sum(List.take(&2, Nat, ks, j))), Maybe.default(&2, Nat, List.get(&2, Nat, ks, j), 0n))

# R5c: an entry as Rust spells it: its path, a directory's followed by `/`
def sp_entry(+path: String, dir: Bool) -> String:
  match dir:
    case True{}:
      String.append(path, "/")
    case False{}:
      path

# R5c: an entry: its path, and whether it is a directory
type SpEnt is Data:
  SpEnt{path: String, dir: Bool}

def sp_entries(es: List<&2, SpEnt>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> r:
      match e:
        case SpEnt{path, dir}:
          sp_entry(path, dir) <> sp_entries(r)

# R5c: s ends with `/`
def sp_ends_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          U32.is_eq(Char.to_u32(c), 47)
        case SCon{d, u}:
          sp_ends_slash(SCon{d, u})

# R5c: every entry is spelled as Rust spells it: a file's path does not
# end with `/`
def sp_entries_ok(es: List<&2, SpEnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> r:
      match e:
        case SpEnt{path, dir}:
          Bool.and(Bool.or(dir, Bool.not(sp_ends_slash(path))), sp_entries_ok(r))

# R5c: the glob p (literal_separator on, no fold) matches s
def sp_ig_hit(+p: String, +s: String) -> Bool:
  sp_parsed_hit(GItems.Opts{True{}, False{}}, GParse.parse(p), s)

# R5c: the glob p matches the text after some `/` of s
def sp_ig_after(+p: String, s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, +t}:
      Bool.or(Bool.and(U32.is_eq(Char.to_u32(c), 47), sp_ig_hit(p, t)), sp_ig_after(p, t))

def sp_ig_some(b: Bool, v: Bool) -> Maybe<&2, Bool>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

# R5c: what a glob rule of code c (below 8: bit 1 anchored, bit 2
# negated, bit 4 directories only) decides of the path: a directory-only
# rule skips a file; it decides when p matches the whole path or, not
# anchored, the text after a `/`; ignored, kept when negated
def sp_ig_glob(+p: String, +c: Nat, +path: String, dir: Bool) -> Maybe<&2, Bool>:
  +skip = Bool.and(Nat.is_le(4n, c), Bool.not(dir))
  +hit = Bool.or(sp_ig_hit(p, path), Bool.and(Bool.not(Nat.is_eq(Nat.mod(c, 2n), 1n)), sp_ig_after(p, path)))
  sp_ig_some(Bool.and(Bool.not(skip), hit), Bool.not(Nat.is_eq(Nat.mod(Nat.div(c, 2n), 2n), 1n)))

def sp_ig_rule.k(glob: Bool, all: Bool, +p: String, +c: Nat, +path: String, dir: Bool) -> Maybe<&2, Bool>:
  match glob:
    case True{}:
      sp_ig_glob(p, c, path, dir)
    case False{}:
      sp_ig_some(Bool.and(all, String.starts_with(path, p)), True{})

# R5c: what the rule of text p and code c decides of the path: a glob
# below 8; 8: ignored when the path starts with p; any other nothing
def sp_ig_rule(+p: String, +c: Nat, +path: String, dir: Bool) -> Maybe<&2, Bool>:
  sp_ig_rule.k(Nat.is_lt(c, 8n), Nat.is_eq(c, 8n), p, c, path, dir)

def sp_ig_pick(m: Maybe<&2, Bool>, b: Bool) -> Bool:
  match m:
    case None{}:
      b
    case Some{v}:
      v

# R5c: per entry, the rule (p, c)'s decision, else the answer before it
def sp_ig_merge(+p: String, +c: Nat, es: List<&2, SpEnt>, bs: List<&2, Bool>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> r:
      match e:
        case SpEnt{path, dir}:
          match bs:
            case Nil{}:
              Nil{}
            case b <> t:
              sp_ig_pick(sp_ig_rule(p, c, path, dir), b) <> sp_ig_merge(p, c, r, t)

def sp_falses(es: List<&2, String>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> r:
      False{} <> sp_falses(r)

# R6: Unicode White_Space (Unicode PropList.txt; Rust char::is_whitespace,
# str::trim): U+0009-000D, U+0020, U+0085, U+00A0, U+1680,
# U+2000-200A, U+2028, U+2029, U+202F, U+205F, U+3000
def sp_ws(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

# R6: every char of s is White_Space
def sp_all_ws(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sp_ws(c), sp_all_ws(t))

# R6: the last char of c <> t (t first) is not White_Space
def sp_last_kept(t: String, c: Char) -> Bool:
  match t:
    case SNil{}:
      Bool.not(sp_ws(c))
    case SCon{d, u}:
      sp_last_kept(u, d)

# R6: s neither starts nor ends with White_Space (the empty text too)
def sp_trimmed(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.and(Bool.not(sp_ws(c)), sp_last_kept(t, c))

# R6: s holds `*`, `?` or `[`
def sp_wild(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), sp_wild(t))

# R6: no char of s is `/`
def sp_no_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(U32.is_eq(Char.to_u32(c), 47)), sp_no_slash(t))

def sp_allow.k(blank: Bool, wild: Bool, +sel: String, +p: String) -> Bool:
  match blank:
    case True{}:
      False{}
    case False{}:
      match wild:
        case True{}:
          +o = {GItems.Opts{False{}, False{}} : GItems.Opts}
          Bool.or(sp_parsed_hit(o, GParse.parse(p), sel), sp_parsed_hit(o, GParse.parse(p), GQuery.bare(sel)))
        case False{}:
          Bool.or(String.eq(p, sel), String.eq(p, GQuery.bare(sel)))

# R6: what the trimmed pattern p decides of the selector: blank never;
# with `*`, `?` or `[` a glob (no option set) of the selector or of its
# bare id; else equal to one of them
def sp_allow(+sel: String, +p: String) -> Bool:
  sp_allow.k(String.is_empty(p), sp_wild(p), sel, p)

# R1: no char of s is special outside a class (`*?[{},\`)
def sp_plain(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      Bool.and(Bool.not(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))), sp_plain(t))

# R1: the literal tokens of s
def sp_lits(s: String) -> List<&2, GParse.Tok>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      GParse.TLit{c} <> sp_lits(t)

# Laws: the matcher
# -----------------

# LAW glob_class_in_range (R3): a byte within one of an unfolded,
# unnegated class's ranges (lo <= x <= hi) is of the class, wherever that
# range sits in the list
# EXCLUDES: a range read with an end excluded, a range past the first
#   skipped
law glob_class_in_range:
  for +pre: List<&2, GItems.BR>
  for +lo: U32
  for +hi: U32
  for +post: List<&2, GItems.BR>
  for +x: U32
  for h: {Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)) == True{} : Bool}
  {GMatch.bc(GItems.BSet{False{}, False{}, List.append(&2, GItems.BR, pre, GItems.BR{lo, hi} <> post)}, x) == True{} : Bool}

# LAW glob_class_in_range_exact (R3): a byte of an unfolded, unnegated
# class is within one of its ranges (with glob_class_in_range: the class
# holds exactly the bytes of its ranges)
# EXCLUDES: a class that takes a byte outside every range (a constant True
#   passes glob_class_in_range), a range read with its ends swapped
law glob_class_in_range_exact:
  for +rs: List<&2, GItems.BR>
  for +x: U32
  for h: {GMatch.bc(GItems.BSet{False{}, False{}, rs}, x) == True{} : Bool}
  exs pre: List<&2, GItems.BR>
  exs lo: U32
  exs hi: U32
  exs post: List<&2, GItems.BR>
  {rs == List.append(&2, GItems.BR, pre, GItems.BR{lo, hi} <> post) : List<&2, GItems.BR>} & {Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)) == True{} : Bool}

# LAW glob_class_negated (R3): a negated class, folded or not, holds
# exactly the bytes the class does not; `.` (BAny) is the negated empty
# class, `[^/]` (BNotSl) the negated class of `/` alone
# EXCLUDES: a negated class not negated, a fold lost under negation, `[^/]`
#   that takes `/` or refuses another byte, `.` that refuses a byte
law glob_class_negated:
  for +fold: Bool
  for +rs: List<&2, GItems.BR>
  for +x: U32
  {GMatch.bc(GItems.BSet{True{}, fold, rs}, x) == Bool.not(GMatch.bc(GItems.BSet{False{}, fold, rs}, x)) : Bool} & {(GMatch.bc(GItems.BAny{}, x), GMatch.bc(GItems.BNotSl{}, x)) == (GMatch.bc(GItems.BSet{True{}, False{}, Nil{}}, x), GMatch.bc(GItems.BSet{True{}, False{}, [GItems.BR{47, 47}]}, x)) : Bool & Bool}

# LAW glob_class_fold_letters (R2, R3): with case folding, an ASCII letter
# of either case is of a class exactly when it or its other case is of
# the unfolded class, for every list of ranges (all 26 pairs)
# EXCLUDES: a fold that misses a case or a letter, or maps a letter to
#   another letter
law glob_class_fold_letters:
  for +rs: List<&2, GItems.BR>
  {sp_folded(rs, sp_case_pairs()) == sp_either(rs, sp_case_pairs()) : List<&2, SpTwo>}

# LAW glob_class_fold_other (R2, R3): with case folding, a byte that is no
# ASCII letter is of a class, negated or not, exactly as without folding
# EXCLUDES: a fold of a byte next to the letter ranges (`@`, `[`, `` ` ``,
#   `{`) or of a non-ASCII byte
law glob_class_fold_other:
  for +neg: Bool
  for +rs: List<&2, GItems.BR>
  for +x: U32
  for h: {sp_letter(x) == False{} : Bool}
  {GMatch.bc(GItems.BSet{neg, True{}, rs}, x) == GMatch.bc(GItems.BSet{neg, False{}, rs}, x) : Bool}

# LAW glob_class_range_bytes (R2): a class's byte ranges are, per char
# range in order, the ranges regex-syntax reads from its `\xNN` escapes
# (sp_rg: one char its bytes; else lo's bytes but the last, lo's last
# byte to hi's first, hi's bytes but the first; an ASCII range lo..hi is
# then the one byte range lo..hi)
# EXCLUDES: a class range read per char instead of per byte, a range
#   dropped or reordered, the middle range built from other bytes
law glob_class_range_bytes:
  for +rs: List<&2, GParse.Rg>
  {GItems.rgs(rs) == sp_rgs(rs) : List<&2, GItems.BR>}

# LAW glob_full (R4): the table matcher answers, for every byte text and
# list of items, what the split of R4 answers
# EXCLUDES: a run that stops too early or too late, a one-byte item that
#   takes none or two, an item skipped, a prefix taken for the whole text,
#   a star whose class is not checked
law glob_full:
  for +bs: List<&2, U32>
  for +its: List<&2, GItems.It>
  {GMatch.full(bs, its) == sp_lang(bs, its) : Bool}

# LAW glob_match_branches (R2, R4): a pattern matches a text exactly when
# one of its branches matches the text's UTF-8 bytes; the lone `**`
# matches every text
# EXCLUDES: a branch skipped or made up, a text matched by chars instead
#   of bytes, the lone `**` read as a recursive prefix
law glob_match_branches:
  for +o: GItems.Opts
  for +xs: List<&2, List<&2, GParse.Tok>>
  for +s: String
  {GMatch.matches(o, GParse.Glob{xs, False{}}, s) == sp_branches(o, xs, GItems.bytes(s)) : Bool} & {GMatch.matches(o, GParse.Glob{xs, True{}}, s) == True{} : Bool}

# LAW glob_match_sequence (R2): the empty branch matches only the empty
# text; a branch t ts matches bytes exactly when they split in two, t
# alone matching the bytes before the split and ts the bytes after it
# EXCLUDES: tokens matched out of order, a token dropped or repeated, a
#   split that loses or doubles a byte
law glob_match_sequence:
  for +o: GItems.Opts
  for +t: GParse.Tok
  for +ts: List<&2, GParse.Tok>
  for +bs: List<&2, U32>
  {(sp_m(o, Nil{}, bs), sp_m(o, t <> ts, bs)) == (List.is_empty(&2, U32, bs), sp_split(o, t, ts, bs, List.length(&2, U32, bs))) : Bool & Bool}

# LAW glob_token_literal (R2): a char alone matches exactly its UTF-8
# bytes (GItems.utf8); with case folding, as many bytes, each of the
# folded class of the char's byte
# EXCLUDES: a char matched by code point, a byte dropped, added or
#   reordered, a fold applied when not asked
law glob_token_literal:
  for +sep: Bool
  for +c: Char
  for +bs: List<&2, U32>
  {(sp_m(GItems.Opts{sep, False{}}, [GParse.TLit{c}], bs), sp_m(GItems.Opts{sep, True{}}, [GParse.TLit{c}], bs)) == (sp_same(GItems.utf8(Char.to_u32(c), Nil{}), bs), sp_same_fold(GItems.utf8(Char.to_u32(c), Nil{}), bs)) : Bool & Bool}

# LAW glob_token_wild (R2): `?` alone matches exactly one byte and `*`
# alone any run of bytes (the empty one too), `/` excepted with
# literal_separator, whatever the fold
# EXCLUDES: `*` or `?` that crosses `/` with literal_separator, or not
#   without it; `?` that takes a char of several bytes or none
law glob_token_wild:
  for +sep: Bool
  for +fold: Bool
  for +bs: List<&2, U32>
  {(sp_m(GItems.Opts{sep, fold}, [GParse.TAny{}], bs), sp_m(GItems.Opts{sep, fold}, [GParse.TZom{}], bs)) == (sp_one_free(sep, bs), sp_all_free(sep, bs)) : Bool & Bool}

# LAW glob_token_recursive (R2): whatever the options, a recursive prefix
# `**/` (TRPre) matches the empty text or any bytes that end with `/`; a
# recursive suffix `/**` (TRSuf) any bytes that start with `/`; `/**/`
# (TRZom) any bytes that start and end with `/` (`/` alone too)
# EXCLUDES: a recursive token read as another, or as two stars (stopped
#   at `/`), a prefix that refuses the empty text
law glob_token_recursive:
  for +o: GItems.Opts
  for +bs: List<&2, U32>
  {(sp_m(o, [GParse.TRPre{}], bs), sp_m(o, [GParse.TRSuf{}], bs), sp_m(o, [GParse.TRZom{}], bs)) == (Bool.or(List.is_empty(&2, U32, bs), sp_slash_last(bs)), sp_slash_first(bs), Bool.and(sp_slash_first(bs), sp_slash_last(bs))) : Bool & Bool & Bool}

# LAW glob_token_class (R2): a class alone matches exactly one byte, of
# the byte class of its ranges' bytes (glob_class_range_bytes), negated
# as the class is, folded with the fold option, whatever
# literal_separator
# EXCLUDES: a class that takes no byte or several, a negation or fold
#   dropped
law glob_token_class:
  for +sep: Bool
  for +fold: Bool
  for +neg: Bool
  for +rs: List<&2, GParse.Rg>
  for +bs: List<&2, U32>
  {sp_m(GItems.Opts{sep, fold}, [GParse.TCls{neg, rs}], bs) == sp_one_of(GItems.BSet{neg, fold, GItems.rgs(rs)}, bs) : Bool}

# LAW glob_queries_count (R5, R5b): a group query answers once per group
# and a rules query once per rule
# EXCLUDES: a missing or extra answer
law glob_queries_count:
  for +o: GItems.Opts
  for +ps: List<&2, String>
  for +ss: List<&2, String>
  for +ks: List<&2, Nat>
  {(List.length(&2, Bool, GQuery.match_groups(o, ps, ss, ks)), List.length(&2, Bool, GQuery.rules(ks, o, ps, ss))) == (List.length(&2, Nat, ks), List.length(&2, Nat, ks)) : Nat & Nat}

# LAW glob_groups_each (R5): the j-th answer of a group query is whether a
# pattern globset accepts matches a text of the j-th group: ks[j] texts
# (or those left) after the first ks[0] + ... + ks[j - 1]
# EXCLUDES: a refused pattern that matches, a group that takes another
#   group's texts, a group answered by its first text only
law glob_groups_each:
  for +o: GItems.Opts
  for +ps: List<&2, String>
  for +ss: List<&2, String>
  for +ks: List<&2, Nat>
  for +j: Nat
  for h: {Nat.is_lt(j, List.length(&2, Nat, ks)) == True{} : Bool}
  {List.get(&2, Bool, GQuery.match_groups(o, ps, ss, ks), j) == Some{sp_texts_hit(o, ps, sp_group(ss, ks, j))} : Maybe<&2, Bool>}

# LAW glob_rules_each (R5b): the j-th answer of a rules query is whether a
# pattern of the j-th rule (ks[j] patterns, or those left, after the first
# ks[0] + ... + ks[j - 1]) that globset accepts matches one of the texts
# EXCLUDES: a rule that takes another rule's patterns, a refused pattern
#   that matches, a text skipped
law glob_rules_each:
  for +ks: List<&2, Nat>
  for +o: GItems.Opts
  for +ps: List<&2, String>
  for +ss: List<&2, String>
  for +j: Nat
  for h: {Nat.is_lt(j, List.length(&2, Nat, ks)) == True{} : Bool}
  {List.get(&2, Bool, GQuery.rules(ks, o, ps, ss), j) == Some{sp_texts_hit(o, sp_group(ps, ks, j), ss)} : Maybe<&2, Bool>}

# LAW glob_ignore_last_wins (R5c): with as many codes as texts, a rule
# (p, c) added last decides each entry it decides (sp_ig_rule: a glob of
# code below 8 by its bits, a prefix of code 8, nothing else), the rules
# before it decide the others; no rule ignores nothing. Entries are
# spelled as Rust spells them (a directory's path then `/`, a file's path
# not ending with `/`)
# EXCLUDES: the first rule deciding instead of the last, a negated rule
#   that ignores, a directory-only rule applied to a file, an anchored rule
#   matched at any depth or an unanchored one only whole, a prefix rule
#   that misses a path under it, a code read as another, an entry's
#   trailing `/` kept in its path, an answer that depends on other entries
law glob_ignore_last_wins:
  for +ps: List<&2, String>
  for +cs: List<&2, Nat>
  for +p: String
  for +c: Nat
  for +es: List<&2, SpEnt>
  for h: {Bool.and(Nat.is_eq(List.length(&2, String, ps), List.length(&2, Nat, cs)), sp_entries_ok(es)) == True{} : Bool}
  {(GQuery.ignored(List.append(&2, String, ps, [p]), List.append(&2, Nat, cs, [c]), sp_entries(es)), GQuery.ignored(Nil{}, Nil{}, sp_entries(es))) == (sp_ig_merge(p, c, es, GQuery.ignored(ps, cs, sp_entries(es))), sp_falses(sp_entries(es))) : List<&2, Bool> & List<&2, Bool>}

# LAW glob_ignore_pairs (R5c): texts and codes pair in order; a text past
# the codes, or a code past the texts, adds no rule
# EXCLUDES: an unpaired text or code read as a rule, pairs shifted
law glob_ignore_pairs:
  for +ps: List<&2, String>
  for +cs: List<&2, Nat>
  for +es: List<&2, String>
  {GQuery.ignored(ps, cs, es) == GQuery.ignored(List.take(&2, String, ps, List.length(&2, Nat, cs)), List.take(&2, Nat, cs, List.length(&2, String, ps)), es) : List<&2, Bool>}

# LAW glob_ignore_example (R5c): anchor: an unanchored name at any depth,
# an anchored glob, a directory-only rule, a negated rule, a prefix rule;
# then the Rust test's rules and entries (crates/eukhe-bend/src/rules/
# glob.rs the_core_decides_rules_and_ignore_rules: venv, build directory
# only, keep negated, prefix sub/; answer true, false, true, false, true)
# EXCLUDES: an ignore matcher that drifts from that Rust test
law glob_ignore_example:
  {(GQuery.ignored(["venv", "a/*.md", "x", "keep.md", "sub/"], [0n, 1n, 4n, 2n, 8n], ["venv/", "x/venv", "a/b.md", "a/c/b.md", "keep.md", "venv", "sub/z", "x/", "x"]), GQuery.ignored(["venv", "build", "keep", "sub/"], [0n, 4n, 2n, 8n], ["a/venv/", "build", "build/", "keep", "sub/x"])) == ([True{}, True{}, True{}, False{}, False{}, True{}, True{}, True{}, False{}], [True{}, False{}, True{}, False{}, True{}]) : List<&2, Bool> & List<&2, Bool>}

# LAW glob_allow_list (R6): a list allows a selector when one of its
# patterns does: ps ++ qs allows exactly what ps or qs allows; the empty
# list allows nothing
# EXCLUDES: a pattern past the first ignored, an empty list that allows
law glob_allow_list:
  for +sel: String
  for +ps: List<&2, String>
  for +qs: List<&2, String>
  {(GQuery.allowed(sel, List.append(&2, String, ps, qs)), GQuery.allowed(sel, Nil{})) == (Bool.or(GQuery.allowed(sel, ps), GQuery.allowed(sel, qs)), False{}) : Bool & Bool}

# LAW glob_allow_one (R6): a pattern p with White_Space w1 before it and w2
# after it (and none at p's own ends) allows a selector as sp_allow says
# of p: blank never; with `*`, `?` or `[` as a glob (no option set) of the
# selector or of its bare id; else when equal to one of them
# EXCLUDES: an untrimmed pattern, a blank pattern that matches, a glob
#   matched only against the selector or only the bare id, a plain
#   pattern globbed, a glob with options set
law glob_allow_one:
  for +sel: String
  for +w1: String
  for +p: String
  for +w2: String
  for h: {Bool.and(sp_all_ws(w1), Bool.and(sp_trimmed(p), sp_all_ws(w2))) == True{} : Bool}
  {GQuery.allowed(sel, [String.append(w1, String.append(p, w2))]) == sp_allow(sel, p) : Bool}

# LAW glob_allow_bare (R6): the bare id of a selector a/b, a without `/`,
# is b; a selector without `/` is its own bare id
# EXCLUDES: a bare id cut at the last `/`, a bare id that keeps the `/`
law glob_allow_bare:
  for +a: String
  for +b: String
  for +s: String
  for h: {Bool.and(sp_no_slash(a), sp_no_slash(s)) == True{} : Bool}
  {(GQuery.bare(String.append(a, SCon{Chr{47}, b})), GQuery.bare(s)) == (b, s) : String & String}

# LAW glob_parse_plain (R1): a pattern with no special char parses to its
# chars as literals, one alternative
# EXCLUDES: an ordinary char read as special, a char lost or doubled, the
#   chars reordered
law glob_parse_plain:
  for +s: String
  for h: {sp_plain(s) == True{} : Bool}
  {GParse.parse(s) == Done{GParse.Glob{[sp_lits(s)], False{}}} : Result<&2, &2, GParse.Err, GParse.Glob>}

# LAW glob_parse_example (R1): anchor: each construct and each error
# EXCLUDES: a parser that drifts from globset
law glob_parse_example:
  {[GParse.parse("a?*"), GParse.parse("**/a"), GParse.parse("a/**"), GParse.parse("a/**/b"), GParse.parse("**"), GParse.parse("a**"), GParse.parse("[!]a-]"), GParse.parse("[a-]"), GParse.parse("\\*,"), GParse.parse("{a,}b"), GParse.parse("{,}"), GParse.parse("{a,b/**}")] == [Done{GParse.Glob{[[GParse.TLit{'a'}, GParse.TAny{}, GParse.TZom{}]], False{}}}, Done{GParse.Glob{[[GParse.TRPre{}, GParse.TLit{'a'}]], False{}}}, Done{GParse.Glob{[[GParse.TLit{'a'}, GParse.TRSuf{}]], False{}}}, Done{GParse.Glob{[[GParse.TLit{'a'}, GParse.TRZom{}, GParse.TLit{'b'}]], False{}}}, Done{GParse.Glob{[[GParse.TRPre{}]], True{}}}, Done{GParse.Glob{[[GParse.TLit{'a'}, GParse.TZom{}, GParse.TZom{}]], False{}}}, Done{GParse.Glob{[[GParse.TCls{True{}, [GParse.Rg{']', ']'}, GParse.Rg{'a', 'a'}, GParse.Rg{'-', '-'}]}]], False{}}}, Done{GParse.Glob{[[GParse.TCls{False{}, [GParse.Rg{'a', 'a'}, GParse.Rg{'-', '-'}]}]], False{}}}, Done{GParse.Glob{[[GParse.TLit{'*'}, GParse.TLit{','}]], False{}}}, Done{GParse.Glob{[[GParse.TLit{'a'}, GParse.TLit{'b'}]], False{}}}, Done{GParse.Glob{[Nil{}], False{}}}, Done{GParse.Glob{[[GParse.TLit{'a'}], [GParse.TLit{'b'}, GParse.TRSuf{}]], False{}}}] : List<&2, Result<&2, &2, GParse.Err, GParse.Glob>>}

# LAW glob_parse_error_example (R1): anchor: each error, the first met
# EXCLUDES: an error read as another, a refused pattern accepted
law glob_parse_error_example:
  {[GQuery.check("a["), GQuery.check("[z-a]"), GQuery.check("a}"), GQuery.check("{a"), GQuery.check("a\\"), GQuery.check("[b-a]}")] == [Some{GParse.EClass{}}, Some{GParse.ERange{'z', 'a'}}, Some{GParse.EUnopened{}}, Some{GParse.EUnclosed{}}, Some{GParse.EEscape{}}, Some{GParse.ERange{'b', 'a'}}] : List<&2, Maybe<&2, GParse.Err>>}

# LAW glob_utf8_example (R2): anchor: the UTF-8 bytes of a char of one,
# two, three and four bytes
# EXCLUDES: a text matched by code points, a wrong byte split
law glob_utf8_example:
  {[GItems.utf8(97, Nil{}), GItems.utf8(233, Nil{}), GItems.utf8(8364, Nil{}), GItems.utf8(128512, Nil{})] == [[97], [195, 169], [226, 130, 172], [240, 159, 152, 128]] : List<&2, List<&2, U32>>}

# the group query of one pattern against one text, literal separators,
# no fold (the examples below)
def sp_sep1(p: String, t: String) -> List<&2, Bool>:
  GQuery.match_groups(GItems.Opts{True{}, False{}}, [p], [t], [1n])

# LAW glob_parse_edge_example (R1, R2): anchor: inputs that tell globset's
# parser from near-miss parsers (found by mutation), literal separators
# EXCLUDES: `/**` before a char read as a suffix, a char after a leading
#   `**` skipped, `**` after a group's `,` or `{` read as two stars, `^`
#   not negating, a repeated `/**/` read as a suffix, `*` crossing `/`,
#   a `-` added to a negated class, `]` first read as a close
law glob_parse_edge_example:
  {[sp_sep1("a/**b", "a/x/yb"), sp_sep1("**a", "xb"), sp_sep1("{a,**/b}", "b"), sp_sep1("{**/b}", "b"), sp_sep1("[^a]", "b"), sp_sep1("a/**/**/b", "a/xb"), sp_sep1("*", "/a"), sp_sep1("**/-*{,}**", "}"), sp_sep1("{a,b}**/[!a]*", "a,b"), sp_sep1("*/**a", "/}"), sp_sep1("**,**", "^"), sp_sep1("a[!a]", "a-"), sp_sep1("[]],b]", ","), sp_sep1("a/**b", "a/xb")] == [[False{}], [False{}], [True{}], [True{}], [True{}], [False{}], [False{}], [False{}], [False{}], [False{}], [False{}], [True{}], [False{}], [True{}]] : List<&2, List<&2, Bool>>}

# LAW glob_parse_edge_nosep_example (R1, R2): anchor: the same, without
# literal separators
# EXCLUDES: a char after `**` skipped, a group product lost after `**`
law glob_parse_edge_nosep_example:
  {[GQuery.match_groups(GItems.Opts{False{}, False{}}, ["**[a-c],a{,}**"], ["a/b"], [1n]), GQuery.match_groups(GItems.Opts{False{}, False{}}, ["**/**.**"], ["/a!"], [1n]), GQuery.match_groups(GItems.Opts{False{}, False{}}, ["**^"], ["b"], [1n]), GQuery.match_groups(GItems.Opts{False{}, False{}}, ["[!a]**/"], [","], [1n])] == [[False{}], [False{}], [False{}], [False{}]] : List<&2, List<&2, Bool>>}

# LAW glob_utf8_boundary_example (R2): anchor: the UTF-8 bytes at each
# length's edges (127/128, 2047/2048, 65535/65536, the last char), and
# `?` taking one byte of a three- or four-byte char
# EXCLUDES: an off-by-one at a length boundary
law glob_utf8_boundary_example:
  {([GItems.utf8(127, Nil{}), GItems.utf8(128, Nil{}), GItems.utf8(2047, Nil{}), GItems.utf8(2048, Nil{}), GItems.utf8(65535, Nil{}), GItems.utf8(65536, Nil{}), GItems.utf8(1114111, Nil{})], [sp_sep1("??", SCon{Chr{2048}, SNil{}}), sp_sep1("?", SCon{Chr{128512}, SNil{}}), sp_sep1("??", SCon{Chr{2047}, SNil{}})]) == ([[127], [194, 128], [223, 191], [224, 160, 128], [239, 191, 191], [240, 144, 128, 128], [244, 143, 191, 191]], [[False{}], [False{}], [True{}]]) : List<&2, List<&2, U32>> & List<&2, List<&2, Bool>>}

# LAW glob_bytes_append (R2, R4): the bytes of a text are its chars' UTF-8
# bytes in order: a ++ b gives a's bytes then b's, one char its UTF-8
# form, the empty text none
# EXCLUDES: a text matched by code points, chars reordered or skipped
law glob_bytes_append:
  for +a: String
  for +b: String
  for +c: Char
  {(GItems.bytes(String.append(a, b)), GItems.bytes(SCon{c, SNil{}}), GItems.bytes("")) == (List.append(&2, U32, GItems.bytes(a), GItems.bytes(b)), GItems.utf8(Char.to_u32(c), Nil{}), Nil{}) : List<&2, U32> & List<&2, U32> & List<&2, U32>}

# LAW glob_utf8_layout (R2): a code's UTF-8 form is as long as RFC 3629
# says (section 3: one byte below 0x80, two below 0x800, three below
# 0x10000, else four), and goes before the rest, the rest untouched. The
# bits of each byte are pinned only by glob_utf8_example and
# glob_utf8_boundary_example
# EXCLUDES: a length boundary off by one, the rest lost or changed
law glob_utf8_layout:
  for +x: U32
  for +rest: List<&2, U32>
  {(List.length(&2, U32, GItems.utf8(x, Nil{})), GItems.utf8(x, rest)) == (sp_utf8_len(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536)), List.append(&2, U32, GItems.utf8(x, Nil{}), rest)) : Nat & List<&2, U32>}

# LAW glob_utf8_ascii (R2): a code below 0x80 is its own one byte
# EXCLUDES: an ASCII char given a lead byte or shifted
law glob_utf8_ascii:
  for +x: U32
  for +rest: List<&2, U32>
  for h: {U32.is_lt(x, 128) == True{} : Bool}
  {GItems.utf8(x, rest) == x <> rest : List<&2, U32>}

# LAW glob_star_example (R1, R2): anchor: `**` in a group branch, before a
# group's `,`, not before `/`, after `/` before a char, repeated, and the
# lone `**/` (literal separators)
# EXCLUDES: the `**` rules read for the whole pattern instead of the
#   branch, a suffix only before `}`, a recursive token where globset
#   reads two stars, a lone `**` decided on the expansion
law glob_star_example:
  {[sp_sep1("x{**/a}", "xa"), sp_sep1("x{**/a}", "xb/a"), sp_sep1("{a/**,b}", "a/x/y"), sp_sep1("**a", "x/a"), sp_sep1("a/**b", "a/xb"), sp_sep1("**/**", "a"), sp_sep1("a/**/**", "a/b/c"), sp_sep1("{**/}", "a"), sp_sep1("**/{}", "a"), sp_sep1("**/", "a")] == [[True{}], [True{}], [True{}], [False{}], [True{}], [True{}], [True{}], [False{}], [False{}], [True{}]] : List<&2, List<&2, Bool>>}

# LAW glob_escape_star_example (R1, R2): anchor: `**` in a group after an
# escaped `,` or `{` (globset reads the char before `**`, escaped or not:
# the escaped char goes and `**` is a recursive suffix, `a/.*`), and after
# a group's `-` or `|` (two stars), literal separators
# EXCLUDES: the char before a group's `**` tested for another char than
#   `,` and `{`, or the test inverted (found by mutation: glob mutants
#   0567, 0568, 0569)
law glob_escape_star_example:
  {[sp_sep1("{a\\,**}", "a/b"), sp_sep1("{a\\,**}", "a,b"), sp_sep1("{a\\{**}", "a/b"), sp_sep1("{a\\{**}", "a{b"), sp_sep1("{a-**}", "a-b"), sp_sep1("{a|**}", "a|b")] == [[True{}], [False{}], [True{}], [False{}], [True{}], [True{}]] : List<&2, List<&2, Bool>>}

# LAW glob_group_class_example (R1): anchor: a branch whose regex is an
# empty group, nested groups, `,` after a group, a range chained past
# its end, `-` as a range end, `\` and `]` first in a class
# EXCLUDES: a branch dropped by token count, a nested product lost, `,`
#   read as a branch outside a group, a chained range cut, `\` read as an
#   escape in a class, `]` first only after `!`
law glob_group_class_example:
  {[sp_sep1("{a,{,}}b", "b"), sp_sep1("{a,{b,c}}d", "cd"), sp_sep1("{a,b},c", "a,c"), sp_sep1("{a,b},c", "b,c"), sp_sep1("[a-c-e]", "d"), sp_sep1("[--0]", "/"), sp_sep1("[\\]]", "\\]"), sp_sep1("[]a]", "]")] == [[False{}], [True{}], [True{}], [True{}], [True{}], [True{}], [True{}], [True{}]] : List<&2, List<&2, Bool>>}

# LAW glob_error_order_example (R1): anchor: errors in a class, an escape
# or a class inside an open group, an unopened `}` before a later error
# EXCLUDES: an open group reported before an earlier error, `-` refused
#   as a range end, `\` escaping inside a class
law glob_error_order_example:
  {[GQuery.check("[z--]"), GQuery.check("[]"), GQuery.check("[a\\"), GQuery.check("{a\\"), GQuery.check("{[a"), GQuery.check("a}["), GQuery.check("{a,b}}")] == [Some{GParse.ERange{'z', '-'}}, Some{GParse.EClass{}}, Some{GParse.EClass{}}, Some{GParse.EEscape{}}, Some{GParse.EClass{}}, Some{GParse.EUnopened{}}, Some{GParse.EUnopened{}}] : List<&2, Maybe<&2, GParse.Err>>}

# LAW glob_match_example (R1-R4): anchor: the cases of the Rust tests
# EXCLUDES: a matcher that drifts from globset
law glob_match_example:
  {[GQuery.match_groups(GItems.Opts{True{}, False{}}, ["*.rs", "**/*.md", "??", "[a"], ["src/main.rs", "main.rs", "a/b/c.md", "é", "README.MD", "x"], [1n, 1n, 1n, 1n, 2n]), GQuery.match_groups(GItems.Opts{True{}, True{}}, ["*.md"], ["README.MD"], [1n]), GQuery.match_groups(GItems.Opts{False{}, False{}}, ["{,a}b", "a/**"], ["b", "a"], [1n, 1n])] == [[False{}, True{}, True{}, True{}, False{}], [True{}], [False{}, False{}]] : List<&2, List<&2, Bool>>}

# LAW glob_allow_example (R6): anchor: the cases of the Rust tests
# EXCLUDES: an allowlist that drifts from the Rust one it replaced
law glob_allow_example:
  {[GQuery.allowed("p/i/g", ["p/i/g"]), GQuery.allowed("p/i/g", ["i/g"]), GQuery.allowed("p/i/g", ["g"]), GQuery.allowed("p/i/g", ["p/*"]), GQuery.allowed("p/i/g", [" i/* "]), GQuery.allowed("z/g", ["p/*"]), GQuery.allowed("z/g5", ["z/g?"]), GQuery.allowed("p/i/g", []), GQuery.allowed("p/i/g", ["  "]), GQuery.allowed("p/i/g", ["["])] == [True{}, True{}, False{}, True{}, True{}, False{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}

# the continuation byte 10xxxxxx of the six bits of x above its k lowest
def sp_utf8.cont(+x: U32, k: Nat) -> U32:
  U32.or(128, U32.and(U32.shrn(x, k), 63))

# the n continuation bytes of x, the high bits first, before rest
def sp_utf8.conts(+n: Nat, +x: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+m:
      sp_utf8.cont(x, Nat.mul(6n, m)) <> sp_utf8.conts(m, x, rest)

# the bytes of x when it takes n continuation bytes: the lead byte (n + 1
# high bits set, then a 0, then the code's top bits; x itself for n = 0)
def sp_utf8.at(n: Nat, +x: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      x <> rest
    case 1n:
      U32.or(192, U32.shrn(x, 6n)) <> sp_utf8.conts(1n, x, rest)
    case 2n:
      U32.or(224, U32.shrn(x, 12n)) <> sp_utf8.conts(2n, x, rest)
    case 3n+k:
      U32.or(240, U32.shrn(x, 18n)) <> sp_utf8.conts(3n, x, rest)

# how many continuation bytes a code takes: below 0x80 (one), 0x800
# (two), 0x10000 (three)
def sp_utf8.more(one: Bool, two: Bool, three: Bool) -> Nat:
  match one:
    case True{}:
      0n
    case False{}:
      match two:
        case True{}:
          1n
        case False{}:
          match three:
            case True{}:
              2n
            case False{}:
              3n

def sp_utf8(+x: U32, rest: List<&2, U32>) -> List<&2, U32>:
  sp_utf8.at(sp_utf8.more(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536)), x, rest)

# LAW glob_utf8 (R2, R4): every code's bytes, before every rest, are its
# UTF-8 bytes as RFC 3629 lays them out (sp_utf8); with glob_bytes, the
# bytes of every text are pinned to that spec
# EXCLUDES: a length boundary off by one, a lead byte with another marker,
#   a continuation byte that takes other bits or drops the marker, bytes
#   reordered, the rest lost or changed
law glob_utf8:
  for +x: U32
  for +rest: List<&2, U32>
  {GItems.utf8(x, rest) == sp_utf8(x, rest) : List<&2, U32>}
