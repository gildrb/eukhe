# eukhe: the laws of area aws_text

import Base
import ../bend/aws_text.bend as A
import ../bend/ffi_aws_text.bend as FA
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ./phrase.bend as Phrase
import ./model_name.bend as ModelName

# (AW1) The names and texts the Bedrock client reads
# --------------------------------------------------
# bend/aws_text.bend, run as the compiled core by bend/ffi_aws_text.bend
# (eukhe-bend rules/aws_text.rs; asked by eukhe-ai
# api/bedrock_converse_stream/ in place of its `regex` patterns). Every
# region, name, chunk, host and id is free. "p ++ q" is p then q. A word
# char is A-Z, a-z, 0-9 or `_` (laws/phrase.bend R2; Rust's `\w` takes the
# Unicode word chars: an intended difference); a digit is 0-9; a region
# char is a-z, 0-9 or `-`.
#
# R1: partition(region): the first partition (index 0..7) whose shape the
#     region has: region = P ++ "-" ++ W ++ "-" ++ N, P one of the
#     partition's prefixes, W one or more word chars, N one or more digits.
#     Prefixes: 0 aws: us, eu, ap, sa, ca, me, af, il, mx; 1 aws-cn: cn;
#     2 aws-eusc: eusc-de; 3 aws-iso: us-iso; 4 aws-iso-b: us-isob;
#     5 aws-iso-e: eu-isoe; 6 aws-iso-f: us-isof; 7 aws-us-gov: us-gov.
#     None: no partition. Source of the table and its order: the
#     `regionRegex` of each partition of the AWS SDK's partitions.json
#     (github.com/boto/botocore botocore/data/partitions.json, read
#     2026-11-08), which the SDKs try in the file's order.
# R2: request-id header: a name is one when name = "x-" ++ M ++
#     "-request-id" or "x-" ++ M ++ "-requestid", M one or more chars each
#     a word char or `-`. Answer: the index of the first such name.
# R3: base64 over the text t (the request's chunks read as one): 1
#     (incorrect padding) when t's length in UTF-16 code units (a char past
#     U+FFFF counts 2) is no multiple of 4; else 0 (valid) when t = B ++ E,
#     every char of B in A-Z a-z 0-9 + /, E one of "", "=", "=="; else 2
#     (invalid).
# R4: endpoint region: host = "bedrock-runtime" ++ F ++ "." ++ R ++ "." ++
#     "amazonaws.com" ++ C, F one of "", "-fips", C one of "", ".cn", R one
#     or more region chars: answer R; else none.
# R5: ARN region: id = "arn:" ++ A ++ ":bedrock:" ++ R ++ ":" ++ rest, A =
#     "aws" or "aws-" ++ X (X one or more region chars), R one or more
#     region chars, rest anything: answer R; else none.
# R6: without_fips(region): at the first place where "fips-" or "-fips"
#     begins: there "fips-dkr-" or "fips-prod-" (if it stands there), else
#     "fips-", else "-fips" is cut out; no such place: the region unchanged.
# R7: the entry answers each request Rust writes (bend/ffi_aws_text.bend
#     header: 0 region, 1 names, 2 chunks, 3 host, 4 id, 5 region; every
#     count and length within the wire) with the model's answer (R1-R6)
#     spelled as the header says, reads exactly the request and nothing
#     after it, and answers any other input (a tag past 5 too) with the
#     exact error form `E aws_text: malformed request`.

# Spec helpers
# ------------

def sp_code(x: Char) -> U32:
  Char.to_u32(x)

# R1: one or more word chars
def sp_words0(w: String) -> Bool:
  match w:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Phrase.sp_word(x), sp_words0(t))

def sp_words(w: String) -> Bool:
  match w:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(Phrase.sp_word(x), sp_words0(t))

# R1: one or more digits
def sp_digs(n: String) -> Bool:
  match n:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(ModelName.sp_digit(x), ModelName.sp_digits(t))

# R1: the AWS table, flat: entry k (0..15) is a prefix (sp_aws_prefix) and
# the index of its partition (sp_aws_part), in the order of partitions.json
# (header R1)
def sp_aws_prefix(k: Nat) -> String:
  match k:
    case 0n:
      "us"
    case 1n:
      "eu"
    case 2n:
      "ap"
    case 3n:
      "sa"
    case 4n:
      "ca"
    case 5n:
      "me"
    case 6n:
      "af"
    case 7n:
      "il"
    case 8n:
      "mx"
    case 9n:
      "cn"
    case 10n:
      "eusc-de"
    case 11n:
      "us-iso"
    case 12n:
      "us-isob"
    case 13n:
      "eu-isoe"
    case 14n:
      "us-isof"
    case 15n:
      "us-gov"
    case 16n+j:
      ""

def sp_aws_part(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n:
      0n
    case 2n:
      0n
    case 3n:
      0n
    case 4n:
      0n
    case 5n:
      0n
    case 6n:
      0n
    case 7n:
      0n
    case 8n:
      0n
    case 9n:
      1n
    case 10n:
      2n
    case 11n:
      3n
    case 12n:
      4n
    case 13n:
      5n
    case 14n:
      6n
    case 15n:
      7n
    case 16n+j:
      0n

# R2: a word char or `-`; one or more of them
def sp_wd(+x: Char) -> Bool:
  Bool.or(Phrase.sp_word(x), U32.is_eq(sp_code(x), 45))

def sp_wds0(m: String) -> Bool:
  match m:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_wd(x), sp_wds0(t))

def sp_wds(m: String) -> Bool:
  match m:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(sp_wd(x), sp_wds0(t))

# R2: the tail of a request-id header: `-request-id`, or `-requestid`
def sp_rid_tail(k: Bool) -> String:
  match k:
    case True{}:
      "-request-id"
    case False{}:
      "-requestid"

# R2: the name at index k of names is a request-id header (A.is_rid,
# pinned by aws_rid_complete and aws_rid_sound); no name there: False
def sp_rid_at(names: List<&2, String>, k: Nat) -> Bool:
  match names:
    case Nil{}:
      False{}
    case n <> t:
      match k:
        case 0n:
          A.is_rid(n)
        case 1n+j:
          sp_rid_at(t, j)

# R3: the chunks read as one text
def sp_cat(cs: List<&2, String>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case c <> more:
      String.append(c, sp_cat(more))

def sp_unit.at(wide: Bool) -> Nat:
  match wide:
    case True{}:
      2n
    case False{}:
      1n

# R3: the UTF-16 code units of a char: 2 past U+FFFF (65535), else 1
def sp_unit(x: Char) -> Nat:
  sp_unit.at(U32.is_lt(65535, sp_code(x)))

# R3: the length of t in UTF-16 code units
def sp_units(t: String) -> Nat:
  match t:
    case SNil{}:
      0n
    case SCon{x, rest}:
      Nat.add(sp_unit(x), sp_units(rest))

# R3: n is a multiple of 4
def sp_mult4(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n:
      False{}
    case 2n:
      False{}
    case 3n:
      False{}
    case 4n+k:
      sp_mult4(k)

# R3: a base64 char: A-Z (65-90), a-z (97-122), 0-9 (48-57), `+` (43), `/`
# (47); `=` (61)
def sp_b64c(x: Char) -> Bool:
  +v = sp_code(x)
  Bool.or(Bool.and(U32.is_le(65, v), U32.is_le(v, 90)), Bool.or(Bool.and(U32.is_le(97, v), U32.is_le(v, 122)), Bool.or(Bool.and(U32.is_le(48, v), U32.is_le(v, 57)), Bool.or(U32.is_eq(v, 43), U32.is_eq(v, 47)))))

def sp_eqc(x: Char) -> Bool:
  U32.is_eq(sp_code(x), 61)

# R3: b is all base64 chars
def sp_all_b64(b: String) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_b64c(x), sp_all_b64(t))

# R3: e is "", "=" or "=="
def sp_pad(e: String) -> Bool:
  match e:
    case SNil{}:
      True{}
    case SCon{+x, t}:
      match t:
        case SNil{}:
          sp_eqc(x)
        case SCon{y, u}:
          Bool.and(Bool.and(sp_eqc(x), sp_eqc(y)), String.is_empty(u))

# R3: t is base64 chars, then "", "=" or "=="
def sp_valid(t: String) -> Bool:
  match t:
    case SNil{}:
      True{}
    case SCon{+x, +rest}:
      Bool.or(Bool.and(sp_b64c(x), sp_valid(rest)), Bool.and(Bool.not(sp_b64c(x)), sp_pad(SCon{x, rest})))

def sp_b64_fin(m: Bool, v: Bool) -> Nat:
  match m:
    case True{}:
      match v:
        case True{}:
          0n
        case False{}:
          2n
    case False{}:
      1n

# R3: the verdict over the text t
def sp_base64(+t: String) -> Nat:
  sp_b64_fin(sp_mult4(sp_units(t)), sp_valid(t))

# R4, R5: a region char; one or more
def sp_lc(x: Char) -> Bool:
  +v = sp_code(x)
  Bool.or(Bool.and(U32.is_le(97, v), U32.is_le(v, 122)), Bool.or(Bool.and(U32.is_le(48, v), U32.is_le(v, 57)), U32.is_eq(v, 45)))

def sp_lcs0(r: String) -> Bool:
  match r:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_lc(x), sp_lcs0(t))

def sp_lcs(r: String) -> Bool:
  match r:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.and(sp_lc(x), sp_lcs0(t))

# R4: F and C
def sp_fips(f: Bool) -> String:
  match f:
    case True{}:
      "-fips"
    case False{}:
      ""

def sp_cn(c: Bool) -> String:
  match c:
    case True{}:
      ".cn"
    case False{}:
      ""

# R4: the host of a standard endpoint
def sp_host(f: Bool, r: String, c: Bool) -> String:
  String.append("bedrock-runtime", String.append(sp_fips(f), String.append(".", String.append(r, String.append(".amazonaws.com", sp_cn(c))))))

# R5: A ("aws", or "aws-" ++ X) and whether it is well formed
def sp_acct(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "aws"
    case Some{x}:
      String.append("aws-", x)

def sp_acct_ok(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      sp_lcs(x)

# R5: a Bedrock ARN
def sp_arn(a: Maybe<&2, String>, r: String, rest: String) -> String:
  String.append("arn:", String.append(sp_acct(a), String.append(":bedrock:", String.append(r, String.append(":", rest)))))

# R6: the text cut out at a FIPS place: 0 `fips-dkr-`, 1 `fips-prod-`, 2
# `fips-`, 3 `-fips`
def sp_cut(k: Nat) -> String:
  match k:
    case 0n:
      "fips-dkr-"
    case 1n:
      "fips-prod-"
    case 2n:
      "fips-"
    case 3n+j:
      "-fips"

# R6: the cut k is the longest that stands at its place, r following it
def sp_cut_ok(k: Nat, +r: String) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n:
      True{}
    case 2n:
      Bool.and(Bool.not(ModelName.sp_pre("dkr-", r)), Bool.not(ModelName.sp_pre("prod-", r)))
    case 3n+j:
      True{}

# R6: a FIPS part begins at the start of u
def sp_begins(+u: String) -> Bool:
  Bool.or(ModelName.sp_pre("fips-", u), ModelName.sp_pre("-fips", u))

# R6: no FIPS part begins at a place of a, t following a
def sp_clear(a: String, +t: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{x, +rest}:
      Bool.and(Bool.not(sp_begins(SCon{x, String.append(rest, t)})), sp_clear(rest, t))

# R7: the spelling of a request and of its reply

def sp_w_req(q: FA.Req, rest: String) -> String:
  match q:
    case FA.QPart{r}:
      Wr.put_nat(0n, Wr.put_str(r, rest))
    case FA.QRid{ns}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(ns, rest))
    case FA.QB64{cs}:
      Wr.put_nat(2n, LawsBase.wire_spell_strs(cs, rest))
    case FA.QHost{h}:
      Wr.put_nat(3n, Wr.put_str(h, rest))
    case FA.QArn{i}:
      Wr.put_nat(4n, Wr.put_str(i, rest))
    case FA.QFips{r}:
      Wr.put_nat(5n, Wr.put_str(r, rest))

def sp_w_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, ""))

def sp_w_mstr(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, ""))

def sp_w_reply(q: FA.Req) -> String:
  match q:
    case FA.QPart{r}:
      sp_w_mnat(A.partition(r))
    case FA.QRid{ns}:
      sp_w_mnat(A.request_id(ns))
    case FA.QB64{cs}:
      Wr.put_nat(A.base64(cs), "")
    case FA.QHost{h}:
      sp_w_mstr(A.endpoint(h))
    case FA.QArn{i}:
      sp_w_mstr(A.arn(i))
    case FA.QFips{r}:
      Wr.put_str(A.without_fips(r), "")

# every count and length of a request fits the wire
def sp_fit_req(q: FA.Req) -> Bool:
  match q:
    case FA.QPart{r}:
      LawsBase.wire_fits(String.length(r))
    case FA.QRid{ns}:
      LawsBase.wire_strs_fit(ns)
    case FA.QB64{cs}:
      LawsBase.wire_strs_fit(cs)
    case FA.QHost{h}:
      LawsBase.wire_fits(String.length(h))
    case FA.QArn{i}:
      LawsBase.wire_fits(String.length(i))
    case FA.QFips{r}:
      LawsBase.wire_fits(String.length(r))

# Laws: the rules
# ---------------

# LAW aws_partition_found (R1): a region that answers partition i has the
# shape of a prefix the AWS table (sp_aws_prefix, sp_aws_part) gives
# partition i
# EXCLUDES: a prefix moved to another partition, an index off by one, a
#   partition answered for a region of no prefix's shape (a default)
law aws_partition_found:
  for +r: String
  for +i: Nat
  for h: {A.partition(r) == Some{i} : Maybe<&2, Nat>}
  exs k: Nat
  {Nat.is_lt(k, 16n) == True{} : Bool} & ({A.shape(sp_aws_prefix(k), r) == True{} : Bool} & {sp_aws_part(k) == i : Nat})

# LAW aws_partition_least (R1): a region with the shape of a prefix of the
# AWS table answers a partition, at most that prefix's partition: with
# aws_partition_found, the answer is the least partition one of whose
# prefixes' shape the region has, and none when it has no prefix's shape
# EXCLUDES: a later partition preferred when the region has the shapes of
#   two, a region of a prefix's shape answered none, a prefix dropped from
#   the table
law aws_partition_least:
  for +r: String
  for +k: Nat
  for hk: {Nat.is_lt(k, 16n) == True{} : Bool}
  for hs: {A.shape(sp_aws_prefix(k), r) == True{} : Bool}
  exs i: Nat
  {A.partition(r) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, sp_aws_part(k)) == True{} : Bool}

# LAW aws_shape_complete (R1): p, `-`, one or more word chars, `-`, one or
# more digits has the shape of p
# EXCLUDES: a word char refused (`_`, a digit, a capital), a number of more
#   digits refused
law aws_shape_complete:
  for +p: String
  for +w: String
  for +n: String
  for hw: {sp_words(w) == True{} : Bool}
  for hn: {sp_digs(n) == True{} : Bool}
  {A.shape(p, String.append(p, String.append("-", String.append(w, String.append("-", n))))) == True{} : Bool}

# LAW aws_shape_sound (R1): a region with the shape of p is p, `-`, one or
# more word chars, `-`, one or more digits
# EXCLUDES: an empty W or N, a `-` inside W, a char past the digits, a
#   Unicode letter taken as a word char
law aws_shape_sound:
  for +p: String
  for +r: String
  for h: {A.shape(p, r) == True{} : Bool}
  exs w: String
  exs n: String
  {r == String.append(p, String.append("-", String.append(w, String.append("-", n)))) : String} & ({sp_words(w) == True{} : Bool} & {sp_digs(n) == True{} : Bool})

# LAW aws_request_id_found (R2): a list of names that answers index i holds
# a request-id header at index i
# EXCLUDES: an index off by one, an index past the list, a name answered
#   that is no request-id header (a default)
law aws_request_id_found:
  for +names: List<&2, String>
  for +i: Nat
  for h: {A.request_id(names) == Some{i} : Maybe<&2, Nat>}
  {sp_rid_at(names, i) == True{} : Bool}

# LAW aws_request_id_least (R2): a list of names with a request-id header
# at index k answers an index at most k: with aws_request_id_found, the
# answer is the first request-id header's index, and none when no name is
# one
# EXCLUDES: a later name preferred, a header missed (none answered)
law aws_request_id_least:
  for +names: List<&2, String>
  for +k: Nat
  for h: {sp_rid_at(names, k) == True{} : Bool}
  exs i: Nat
  {A.request_id(names) == Some{i} : Maybe<&2, Nat>} & {Nat.is_le(i, k) == True{} : Bool}

# LAW aws_rid_complete (R2): x-, one or more word chars or `-`, then
# `-request-id` or `-requestid` is a request-id header
# EXCLUDES: the optional `-` required or refused, a `-` in M refused
law aws_rid_complete:
  for +m: String
  for +k: Bool
  for h: {sp_wds(m) == True{} : Bool}
  {A.is_rid(String.append("x-", String.append(m, sp_rid_tail(k)))) == True{} : Bool}

# LAW aws_rid_sound (R2): a request-id header is x-, one or more word chars
# or `-`, then `-request-id` or `-requestid`
# EXCLUDES: an empty M (x-request-id), text after the tail, another prefix
law aws_rid_sound:
  for +name: String
  for h: {A.is_rid(name) == True{} : Bool}
  exs m: String
  exs k: Bool
  {name == String.append("x-", String.append(m, sp_rid_tail(k))) : String} & {sp_wds(m) == True{} : Bool}

# LAW aws_base64_decides (R3): every list of chunks answers the verdict of
# the text they make, as the spec decides it
# EXCLUDES: a length counted in chars or bytes, a chunk read on its own
#   (padding inside a chunk border), `=` in the body, more than two `=`, a
#   char outside the alphabet
law aws_base64_decides:
  for +cs: List<&2, String>
  {A.base64(cs) == sp_base64(sp_cat(cs)) : Nat}

# LAW aws_base64_valid_complete (R3): base64 chars then "", "=" or "==", of
# a length in UTF-16 units that is a multiple of 4, is valid however it is
# cut into chunks
# EXCLUDES: a valid text refused for its chunking or its padding
law aws_base64_valid_complete:
  for +cs: List<&2, String>
  for +b: String
  for +e: String
  for hc: {sp_cat(cs) == String.append(b, e) : String}
  for hb: {sp_all_b64(b) == True{} : Bool}
  for he: {sp_pad(e) == True{} : Bool}
  for hm: {sp_mult4(sp_units(String.append(b, e))) == True{} : Bool}
  {A.base64(cs) == 0n : Nat}

# LAW aws_base64_valid_sound (R3): a valid text is base64 chars then "",
# "=" or "==", of a length in UTF-16 units that is a multiple of 4
# EXCLUDES: a text with a stray char, a third `=` or a bad length called
#   valid
law aws_base64_valid_sound:
  for +cs: List<&2, String>
  for h: {A.base64(cs) == 0n : Nat}
  exs b: String
  exs e: String
  {sp_cat(cs) == String.append(b, e) : String} & ({sp_all_b64(b) == True{} : Bool} & ({sp_pad(e) == True{} : Bool} & {sp_mult4(sp_units(sp_cat(cs))) == True{} : Bool}))

# LAW aws_endpoint_complete (R4): a standard endpoint host answers its
# region
# EXCLUDES: the fips or the .cn form refused, a region cut short
law aws_endpoint_complete:
  for +f: Bool
  for +r: String
  for +c: Bool
  for h: {sp_lcs(r) == True{} : Bool}
  {A.endpoint(sp_host(f, r, c)) == Some{r} : Maybe<&2, String>}

# LAW aws_endpoint_sound (R4): a host that answers a region is the standard
# endpoint host of that region
# EXCLUDES: a region read from another host (bedrock.<r>...), a region with
#   a capital or a dot, text after the suffix
law aws_endpoint_sound:
  for +host: String
  for +r: String
  for h: {A.endpoint(host) == Some{r} : Maybe<&2, String>}
  exs f: Bool
  exs c: Bool
  {host == sp_host(f, r, c) : String} & {sp_lcs(r) == True{} : Bool}

# LAW aws_arn_complete (R5): a Bedrock ARN answers its region, whatever
# follows the `:` after it
# EXCLUDES: an aws-<x> partition refused, a region cut short
law aws_arn_complete:
  for +a: Maybe<&2, String>
  for +r: String
  for +rest: String
  for ha: {sp_acct_ok(a) == True{} : Bool}
  for hr: {sp_lcs(r) == True{} : Bool}
  {A.arn(sp_arn(a, r, rest)) == Some{r} : Maybe<&2, String>}

# LAW aws_arn_sound (R5): an id that answers a region is a Bedrock ARN of
# that region
# EXCLUDES: another service, an empty partition suffix or region, a region
#   with no `:` after it
law aws_arn_sound:
  for +id: String
  for +r: String
  for h: {A.arn(id) == Some{r} : Maybe<&2, String>}
  exs a: Maybe<&2, String>
  exs rest: String
  {id == sp_arn(a, r, rest) : String} & ({sp_acct_ok(a) == True{} : Bool} & {sp_lcs(r) == True{} : Bool})

# LAW aws_fips_first (R6): at the first place where a FIPS part begins, the
# longest cut that stands there is cut out, and nothing else changes
# EXCLUDES: a later place cut, a shorter cut (fips- before fips-dkr-), a
#   second place cut too, text around changed
law aws_fips_first:
  for +a: String
  for +k: Nat
  for +r: String
  for ha: {sp_clear(a, String.append(sp_cut(k), r)) == True{} : Bool}
  for hk: {sp_cut_ok(k, r) == True{} : Bool}
  {A.without_fips(String.append(a, String.append(sp_cut(k), r))) == String.append(a, r) : String}

# LAW aws_fips_none (R6): a region where no FIPS part begins is unchanged
# EXCLUDES: a text changed with no FIPS part, `fips` alone cut
law aws_fips_none:
  for +s: String
  for h: {sp_clear(s, "") == True{} : Bool}
  {A.without_fips(s) == s : String}

# LAW aws_text_example (R1-R6): anchor: the examples of the client's rules
# EXCLUDES: rules that drift from the regexes they replaced
law aws_text_example:
  {([A.partition("us-east-1"), A.partition("us-gov-west-1"), A.partition("eusc-de-east-1"), A.partition("us-east"), A.request_id(["x-request-id", "x-amzn-requestid"])], ([A.base64(["QUJD"]), A.base64(["QUJ"]), A.base64(["Q=Q="]), A.base64([]), A.base64(["QU", "J="]), A.base64([SCon{Chr{128512}, "QQ"}])], ([A.endpoint("bedrock-runtime-fips.us-east-1.amazonaws.com"), A.endpoint("bedrock.us-east-1.amazonaws.com"), A.arn("arn:aws-cn:bedrock:cn-north-1:1"), A.arn("arn:aws:bedrock:us-east-1")], [A.without_fips("fips-dkr-us-east-1"), A.without_fips("us-east-1-fips"), A.without_fips("fips-us-fips"), A.without_fips("us-west-2")]))) == ([Some{0n}, Some{7n}, Some{2n}, None{}, Some{1n}], ([0n, 1n, 2n, 0n, 0n, 2n], ([Some{"us-east-1"}, None{}, Some{"cn-north-1"}, None{}], ["us-east-1", "us-east-1", "us-fips", "us-west-2"]))) : List<&2, Maybe<&2, Nat>> & (List<&2, Nat> & (List<&2, Maybe<&2, String>> & List<&2, String>))}

# Laws: the entry (R7)
# --------------------

# LAW aws_text_entry_decides (R7): a request spelled by the grammar, every
# count and length within the wire, is answered with the spelling of the
# model's answer
# EXCLUDES: a request read as another, a field lost, a reply spelled
#   another way (an index as a flag, a missing Maybe tag)
law aws_text_entry_decides:
  for +q: FA.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FA.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW aws_text_entry_left_over (R7): input left over after a spelled
# request answers the error form
# EXCLUDES: trailing input ignored, or read as part of the request
law aws_text_entry_left_over:
  for +q: FA.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FA.ffi(sp_w_req(q, rest)) == Wr.err("aws_text: malformed request") : String}

# LAW aws_text_entry_reads_only_requests (R7): an answer that is not the
# error form answers a request: the input is the spelling of a request that
# fits the wire, and the answer is the model's answer to it
# EXCLUDES: a decoder that accepts an unknown tag, a short string, a count
#   past the wire or a missing field, and answers it anyway
law aws_text_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FA.ffi(s)) == False{} : Bool}
  exs q: FA.Req
  {(s, (sp_fit_req(q), FA.ffi(s))) == (sp_w_req(q, ""), (True{}, sp_w_reply(q))) : String & (Bool & String)}

# LAW aws_text_entry_unknown_request (R7): a request tag past 5 is
# malformed, whatever follows
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law aws_text_entry_unknown_request:
  for +n: Nat
  for +rest: String
  {FA.ffi(Wr.put_nat(6n+n, rest)) == Wr.err("aws_text: malformed request") : String}

# LAW aws_text_entry_malformed_unless_request (R7): an input that does not
# begin with a spelled request that fits answers the malformed error
# EXCLUDES: another error text, or a reply, for input that holds no request
law aws_text_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(FA.ffi(s), Wr.err("aws_text: malformed request")) == False{} : Bool}
  exs q: FA.Req
  exs rest: String
  {(s, sp_fit_req(q)) == (sp_w_req(q, rest), True{}) : String & Bool}

# LAW aws_text_entry_example (R7): anchor: the wire strings Rust sends and
# the replies it reads; an unknown request, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law aws_text_entry_example:
  {[FA.ffi("0,9,us-east-1"), FA.ffi("1,2,1,a16,x-amzn-requestid"), FA.ffi("2,1,4,QUJ="), FA.ffi("3,1,x"), FA.ffi("5,7,fips-us"), FA.ffi("6,"), FA.ffi("0,1,ab")] == ["1,0,", "1,1,", "0,", "0,", "2,us", Wr.err("aws_text: malformed request"), Wr.err("aws_text: malformed request")] : List<&2, String>}

# LAW aws_text_entry_premises_witness (R7): a request that fits exists, and
# so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law aws_text_entry_premises_witness:
  {(sp_fit_req(FA.QPart{"x"}), FA.ffi("")) == (True{}, Wr.err("aws_text: malformed request")) : Bool & String}
