# eukhe: lemmas of the proofs of area codemode_source: the model
#
# Each step of Src.parse equals the step of the spec (laws/codemode_source.bend)
# it ports: the first unsupported key (csr.least, csr.other), a field's
# value (csr.lookup), and the checks of the options (csr.options); an
# array index is the wire's Nat reader on the key and ',' (csi.*).

import Base
import ../../bend/codemode_source.bend as Src
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/codemode_source.bend as CodemodeSource
import ../base/nat.bend as LNat

# ---- logic ----

def csr.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def csr.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : csr.BT(_, G)
  Unit{}

def csr.MI(m: Maybe<&2, Nat>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def csr.ns(-G: Type, -n: Nat, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> G:
  %e : csr.MI(_, G)
  Unit{}

def csr.val(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def csr.some_inj(-x: Nat, -n: Nat, e: {Some{x} == Some{n} : Maybe<&2, Nat>}) -> {x == n : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, z => csr.val(z), Some{x}, Some{n}, e)

# ---- the first unsupported key ----

def csr.least_cmp(b: Bool, +n: Nat, k: String, +m: Nat, k2: String) -> {Src.least.cmp(b, n, k, Src.Ix{m, k2}) == Some{CodemodeSource.least_of(b, Src.Ix{n, k}, Src.Ix{m, k2})} : Maybe<&2, Src.Ix>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def csr.least_with(+n: Nat, k: String, l: Maybe<&2, Src.Ix>) -> {Src.least.with(n, k, l) == Some{CodemodeSource.least_first(Src.Ix{n, k}, l)} : Maybe<&2, Src.Ix>}:
  match l:
    case None{}:
      {==}
    case Some{y}:
      match y:
        case Src.Ix{+m, k2}:
          csr.least_cmp(Nat.is_lt(m, n), n, k, m, k2)

def csr.least_pick(mi: Maybe<&2, Nat>, k: String, xs: List<&2, Src.Ix>, -l: Maybe<&2, Src.Ix>, e: {l == CodemodeSource.least_spec(xs) : Maybe<&2, Src.Ix>}) -> {Src.least.pick(mi, k, l) == CodemodeSource.least_spec(CodemodeSource.ix_one(mi, k, xs)) : Maybe<&2, Src.Ix>}:
  match mi:
    case None{}:
      e
    case Some{+n}:
      %Equal.sym(Maybe<&2, Src.Ix>, l, CodemodeSource.least_spec(xs), e) : {Src.least.with(n, k, _) == Some{CodemodeSource.least_first(Src.Ix{n, k}, CodemodeSource.least_spec(xs))} : Maybe<&2, Src.Ix>}
      csr.least_with(n, k, CodemodeSource.least_spec(xs))

# the least array-index key is the spec's
def csr.least(fs: List<&2, Src.Field>) -> {Src.least(fs) == CodemodeSource.least_spec(CodemodeSource.ixs_spec(fs)) : Maybe<&2, Src.Ix>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +r}:
      match f:
        case Src.Field{+k, v}:
          csr.least_pick(Src.index(k), k, CodemodeSource.ixs_spec(r), Src.least(r), csr.least(r))

def csr.other_at(b: Bool, k: String, x: Maybe<&2, String>) -> {Src.other.pick(b, k, x) == CodemodeSource.other_at(b, k, x) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the first key that is not supported is the spec's
def csr.other(fs: List<&2, Src.Field>) -> {Src.other(fs) == CodemodeSource.other_spec(fs) : Maybe<&2, String>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +r}:
      match f:
        case Src.Field{+k, v}:
          %csr.other(r) : {Src.other.pick(Src.supported(k), k, Src.other(r)) == CodemodeSource.other_at(CodemodeSource.supported_spec(k), k, _) : Maybe<&2, String>}
          csr.other_at(Src.supported(k), k, Src.other(r))

def csr.unsup_or(l: Maybe<&2, Src.Ix>, +fs: List<&2, Src.Field>) -> {Src.unsupported.or(l, fs) == CodemodeSource.unsupported_pick(l, fs) : Maybe<&2, String>}:
  match l:
    case Some{b}:
      match b:
        case Src.Ix{n, k}:
          {==}
    case None{}:
      csr.other(fs)

# the first unsupported key is the spec's
def csr.unsupported(+fs: List<&2, Src.Field>) -> {Src.unsupported(fs) == CodemodeSource.unsupported_spec(fs) : Maybe<&2, String>}:
  %csr.least(fs) : {Src.unsupported.or(Src.least(fs), fs) == CodemodeSource.unsupported_pick(_, fs) : Maybe<&2, String>}
  csr.unsup_or(Src.least(fs), fs)

# ---- a field's value ----

def csr.find_at(b: Bool, v: Src.Num, x: Maybe<&2, Src.Num>) -> {Src.lookup.pick(b, v, x) == CodemodeSource.find_at(b, v, x) : Maybe<&2, Src.Num>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the value of the first field named name is the spec's
def csr.lookup(fs: List<&2, Src.Field>, +name: String) -> {Src.lookup(fs, name) == CodemodeSource.find_spec(fs, name) : Maybe<&2, Src.Num>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +r}:
      match f:
        case Src.Field{k, v}:
          %csr.lookup(r, name) : {Src.lookup.pick(String.eq(k, name), v, Src.lookup(r, name)) == CodemodeSource.find_at(String.eq(k, name), v, _) : Maybe<&2, Src.Num>}
          csr.find_at(String.eq(k, name), v, Src.lookup(r, name))

# ---- the options ----

def csr.range(tok: Bool, b: Bool) -> {Src.options.range(tok, b) == CodemodeSource.timeout_at(b, tok) : Src.Answer}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def csr.timeout(m: Maybe<&2, Src.Num>, tok: Bool) -> {Src.options.timeout(tok, m) == CodemodeSource.timeout_step(m, tok) : Src.Answer}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Src.NoInt{}:
          {==}
        case Src.Int{n}:
          csr.range(tok, Src.timeout_ok(n))

def csr.tokens(m: Maybe<&2, Src.Num>, +fs: List<&2, Src.Field>) -> {Src.options.tokens(m, fs) == CodemodeSource.tokens_step(m, fs) : Src.Answer}:
  match m:
    case None{}:
      %csr.lookup(fs, "timeout_ms") : {Src.options.timeout(False{}, Src.lookup(fs, "timeout_ms")) == CodemodeSource.timeout_step(_, False{}) : Src.Answer}
      csr.timeout(Src.lookup(fs, "timeout_ms"), False{})
    case Some{v}:
      match v:
        case Src.NoInt{}:
          {==}
        case Src.Int{n}:
          %csr.lookup(fs, "timeout_ms") : {Src.options.timeout(True{}, Src.lookup(fs, "timeout_ms")) == CodemodeSource.timeout_step(_, True{}) : Src.Answer}
          csr.timeout(Src.lookup(fs, "timeout_ms"), True{})

def csr.keys(b: Maybe<&2, String>, +fs: List<&2, Src.Field>) -> {Src.options.keys(b, fs) == CodemodeSource.keys_step(b, fs) : Src.Answer}:
  match b:
    case Some{k}:
      {==}
    case None{}:
      %csr.lookup(fs, "max_output_tokens") : {Src.options.tokens(Src.lookup(fs, "max_output_tokens"), fs) == CodemodeSource.tokens_step(_, fs) : Src.Answer}
      csr.tokens(Src.lookup(fs, "max_output_tokens"), fs)

def csr.json(j: Src.Json) -> {Src.options.json(j) == CodemodeSource.json_step(j) : Src.Answer}:
  match j:
    case Src.JsonErr{t}:
      {==}
    case Src.NotObj{}:
      {==}
    case Src.Obj{+fs}:
      %csr.unsupported(fs) : {Src.options.keys(Src.unsupported(fs), fs) == CodemodeSource.keys_step(_, fs) : Src.Answer}
      csr.keys(Src.unsupported(fs), fs)

# the options of a directive are the spec's
def csr.options(d: Src.Dir) -> {Src.options(d) == CodemodeSource.dir_spec(d) : Src.Answer}:
  match d:
    case Src.Dir{e, j}:
      match e:
        case True{}:
          {==}
        case False{}:
          csr.json(j)

# with no misplaced options line, the answer is the spec's
def csr.dir(m: Maybe<&2, Src.Dir>, rb: Bool) -> {Src.parse.dir(m, rb) == CodemodeSource.first_line_spec(m, rb) : Src.Answer}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match rb:
        case True{}:
          {==}
        case False{}:
          csr.options(d)

# ---- an array index ----

def csi.len_app(a: String, +b: String) -> {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, u}:
      %csi.len_app(u, b) : {1n+String.length(String.append(u, b)) == 1n+_ : Nat}
      {==}

def csi.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# the key's length is its number's digit count
def csi.digits(+k: String, +n: Nat, e: {String.append(k, ",") == Wr.put_nat(n, "") : String}) -> {String.length(k) == LawsBase.wire_digits(n) : Nat}:
  +e1 = Equal.cong(String, Nat, z => String.length(z), String.append(k, ","), Wr.put_nat(n, ""), e)
  +e2 = Equal.trans(Nat, Nat.add(String.length(k), 1n), String.length(String.append(k, ",")), String.length(Wr.put_nat(n, "")), Equal.sym(Nat, String.length(String.append(k, ",")), Nat.add(String.length(k), 1n), csi.len_app(k, ",")), e1)
  +e3 = Equal.trans(Nat, Nat.add(String.length(k), 1n), String.length(Wr.put_nat(n, "")), 1n+LawsBase.wire_digits(n), e2, Wire.wire_digits_spells(n))
  +e4 = Equal.trans(Nat, 1n+String.length(k), Nat.add(String.length(k), 1n), 1n+LawsBase.wire_digits(n), Equal.trans(Nat, 1n+String.length(k), 1n+Nat.add(String.length(k), 0n), Nat.add(String.length(k), 1n), Equal.cong(Nat, Nat, z => 1n+z, String.length(k), Nat.add(String.length(k), 0n), Equal.sym(Nat, Nat.add(String.length(k), 0n), String.length(k), LNat.wn_add_zero_r(String.length(k)))), Equal.sym(Nat, Nat.add(String.length(k), 1n), 1n+Nat.add(String.length(k), 0n), LNat.wn_add_succ_r(String.length(k), 0n))), e3)
  Equal.cong(Nat, Nat, z => csi.pred(z), 1n+String.length(k), 1n+LawsBase.wire_digits(n), e4)

# a number spelled in at most 10 digits fits the wire
def csi.fits(+k: String, +n: Nat, short: {Nat.is_le(String.length(k), 10n) == True{} : Bool}, e: {String.append(k, ",") == Wr.put_nat(n, "") : String}) -> {LawsBase.wire_fits(n) == True{} : Bool}:
  %csi.digits(k, n, e) : {Nat.is_le(_, 14n) == True{} : Bool}
  LNat.wn_le_trans(String.length(k), 10n, 14n, short, {==})

def csi.at(b: Bool, +x: Nat, +n: Nat, -s: String, eb: {Nat.is_lt(x, Src.index_cap()) == b : Bool}, ex: {s == Wr.put_nat(x, "") : String}, e: {Src.index.at(b, x) == Some{n} : Maybe<&2, Nat>}) -> {s == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}:
  match b:
    case True{}:
      %csr.some_inj(x, n, e) : {s == LawsBase.wire_dec(_, "") : String} & {Nat.is_lt(_, 4294967295n) == True{} : Bool}
      (Equal.trans(String, s, Wr.put_nat(x, ""), LawsBase.wire_dec(x, ""), ex, Wire.wire_nat_decimal(x, "")), eb)
    case False{}:
      csr.ns({s == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}, n, e)

def csi.got(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +n: Nat, e: {Src.index.got(d) == Some{n} : Maybe<&2, Nat>}) -> {s == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}:
  match d:
    case Wr.Got{+x, r}:
      match r:
        case SNil{}:
          csi.at(Nat.is_lt(x, Src.index_cap()), x, n, s, {==}, Wire.wire_nat_exact(s, x, "", ed), e)
        case SCon{c, t}:
          csr.ns({s == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}, n, e)
    case Wr.Bad{}:
      csr.ns({s == LawsBase.wire_dec(n, "") : String} & {Nat.is_lt(n, 4294967295n) == True{} : Bool}, n, e)

def csi.reads(+k: String, +n: Nat, below: {Nat.is_lt(n, 4294967295n) == True{} : Bool}, short: {Nat.is_le(String.length(k), 10n) == True{} : Bool}, e: {String.append(k, ",") == LawsBase.wire_dec(n, "") : String}) -> {Src.index(k) == Some{n} : Maybe<&2, Nat>}:
  +ep = Equal.trans(String, String.append(k, ","), LawsBase.wire_dec(n, ""), Wr.put_nat(n, ""), e, Equal.sym(String, Wr.put_nat(n, ""), LawsBase.wire_dec(n, ""), Wire.wire_nat_decimal(n, "")))
  %Equal.sym(String, String.append(k, ","), Wr.put_nat(n, ""), ep) : {Src.index.got(Wr.get_nat(_)) == Some{n} : Maybe<&2, Nat>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, "")), Wr.Got{n, ""}, Wire.wire_nat_round_trip(n, "", csi.fits(k, n, short, ep))) : {Src.index.got(_) == Some{n} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_lt(n, 4294967295n), True{}, below) : {Src.index.at(_, n) == Some{n} : Maybe<&2, Nat>}
  {==}
