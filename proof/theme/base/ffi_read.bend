# eukhe: lemmas of the theme entry's proofs: the entry's reader answers
# what the laws' reader (spec/theme_read.bend) answers on every input, one
# lemma per stage, each a case split on the stage's input

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/resolve.bend as TResolve
import ../../../bend/ffi_theme.bend as FTh
import ../../../spec/theme_read.bend as Tr

def tl.mnat.some(r: Wr.Dec<Nat>) -> {Tr.read.mnat.some(r) == FTh.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.mnat.tag(t: Nat, +s: String) -> {Tr.read.mnat.tag(t, s) == FTh.get_mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      tl.mnat.some(Wr.get_nat(s))
    case 2n+p:
      {==}

def tl.mnat(r: Wr.Dec<Nat>) -> {Tr.read.mnat(r) == FTh.get_mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      tl.mnat.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.jstr.at(x: String, r: Wr.Dec<Maybe<&2, Nat>>) -> {Tr.read.jstr.at(x, r) == FTh.get_jstr.at(x, r) : Wr.Dec<TFile.Json>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.jstr(r: Wr.Dec<String>) -> {Tr.read.jstr(r) == FTh.get_jstr(r) : Wr.Dec<TFile.Json>}:
  match r:
    case Wr.Got{+x, +s}:
      %tl.mnat(Wr.get_nat(s)) : {Tr.read.jstr.at(x, Tr.read.mnat(Wr.get_nat(s))) == FTh.get_jstr.at(x, _) : Wr.Dec<TFile.Json>}
      tl.jstr.at(x, Tr.read.mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.jnum(r: Wr.Dec<String>) -> {Tr.read.jnum(r) == FTh.get_jnum(r) : Wr.Dec<TFile.Json>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.jother(r: Wr.Dec<String>) -> {Tr.read.jother(r) == FTh.get_jother(r) : Wr.Dec<TFile.Json>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.json.tag(t: Nat, +s: String) -> {Tr.read.json.tag(t, s) == FTh.get_json.tag(t, s) : Wr.Dec<TFile.Json>}:
  match t:
    case 0n:
      tl.jstr(Wr.get_str(s))
    case 1n:
      tl.jnum(Wr.get_str(s))
    case 2n:
      tl.jother(Wr.get_str(s))
    case 3n+p:
      {==}

def tl.json.go(r: Wr.Dec<Nat>) -> {Tr.read.json.go(r) == FTh.get_json.go(r) : Wr.Dec<TFile.Json>}:
  match r:
    case Wr.Got{t, s}:
      tl.json.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.var.val(n: String, r: Wr.Dec<TFile.Json>) -> {Tr.read.var.val(n, r) == FTh.get_var.val(n, r) : Wr.Dec<TFile.Var>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.var.go(r: Wr.Dec<String>) -> {Tr.read.var.go(r) == FTh.get_var.go(r) : Wr.Dec<TFile.Var>}:
  match r:
    case Wr.Got{+n, +s}:
      %tl.json.go(Wr.get_nat(s)) : {Tr.read.var.val(n, Tr.read.json.go(Wr.get_nat(s))) == FTh.get_var.val(n, _) : Wr.Dec<TFile.Var>}
      tl.var.val(n, Tr.read.json.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.var(+s: String) -> {Tr.read.var(s) == FTh.get_var(s) : Wr.Dec<TFile.Var>}:
  tl.var.go(Wr.get_str(s))

def tl.vars.cons(v: TFile.Var, r: Wr.Dec<List<&2, TFile.Var>>) -> {Tr.read.vars.cons(v, r) == FTh.get_vars.cons(v, r) : Wr.Dec<List<&2, TFile.Var>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.vars.go(n: Nat, cur: Wr.Dec<TFile.Var>) -> {Tr.read.vars.go(n, cur) == FTh.get_vars.go(n, cur) : Wr.Dec<List<&2, TFile.Var>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{v, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+v, +s}:
          %tl.var(s) : {Tr.read.vars.cons(v, Tr.read.vars.go(m, Tr.read.var(s))) == FTh.get_vars.cons(v, FTh.get_vars.go(m, _)) : Wr.Dec<List<&2, TFile.Var>>}
          %tl.vars.go(m, Tr.read.var(s)) : {Tr.read.vars.cons(v, Tr.read.vars.go(m, Tr.read.var(s))) == FTh.get_vars.cons(v, _) : Wr.Dec<List<&2, TFile.Var>>}
          tl.vars.cons(v, Tr.read.vars.go(m, Tr.read.var(s)))
        case Wr.Bad{}:
          {==}

def tl.vars(r: Wr.Dec<Nat>) -> {Tr.read.vars(r) == FTh.get_vars(r) : Wr.Dec<List<&2, TFile.Var>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %tl.var(s) : {Tr.read.vars.go(m, Tr.read.var(s)) == FTh.get_vars.go(m, _) : Wr.Dec<List<&2, TFile.Var>>}
          tl.vars.go(m, Tr.read.var(s))
    case Wr.Bad{}:
      {==}

def tl.mu32.some(r: Wr.Dec<U32>) -> {Tr.read.mu32.some(r) == FTh.get_mu32.some(r) : Wr.Dec<Maybe<&2, U32>>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.mu32.tag(t: Nat, +s: String) -> {Tr.read.mu32.tag(t, s) == FTh.get_mu32.tag(t, s) : Wr.Dec<Maybe<&2, U32>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      tl.mu32.some(Wr.get_u32(s))
    case 2n+p:
      {==}

def tl.mu32(r: Wr.Dec<Nat>) -> {Tr.read.mu32(r) == FTh.get_mu32(r) : Wr.Dec<Maybe<&2, U32>>}:
  match r:
    case Wr.Got{t, s}:
      tl.mu32.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.col.val(k: String, t: Maybe<&2, U32>, r: Wr.Dec<TFile.Json>) -> {Tr.read.col.val(k, t, r) == FTh.get_col.val(k, t, r) : Wr.Dec<TFile.REnt>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.col.tok(+k: String, r: Wr.Dec<Maybe<&2, U32>>) -> {Tr.read.col.tok(k, r) == FTh.get_col.tok(k, r) : Wr.Dec<TFile.REnt>}:
  match r:
    case Wr.Got{+t, +s}:
      %tl.json.go(Wr.get_nat(s)) : {Tr.read.col.val(k, t, Tr.read.json.go(Wr.get_nat(s))) == FTh.get_col.val(k, t, _) : Wr.Dec<TFile.REnt>}
      tl.col.val(k, t, Tr.read.json.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.col.go(r: Wr.Dec<String>) -> {Tr.read.col.go(r) == FTh.get_col.go(r) : Wr.Dec<TFile.REnt>}:
  match r:
    case Wr.Got{+k, +s}:
      %tl.mu32(Wr.get_nat(s)) : {Tr.read.col.tok(k, Tr.read.mu32(Wr.get_nat(s))) == FTh.get_col.tok(k, _) : Wr.Dec<TFile.REnt>}
      tl.col.tok(k, Tr.read.mu32(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.col(+s: String) -> {Tr.read.col(s) == FTh.get_col(s) : Wr.Dec<TFile.REnt>}:
  tl.col.go(Wr.get_str(s))

def tl.cols.cons(v: TFile.REnt, r: Wr.Dec<List<&2, TFile.REnt>>) -> {Tr.read.cols.cons(v, r) == FTh.get_cols.cons(v, r) : Wr.Dec<List<&2, TFile.REnt>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.cols.go(n: Nat, cur: Wr.Dec<TFile.REnt>) -> {Tr.read.cols.go(n, cur) == FTh.get_cols.go(n, cur) : Wr.Dec<List<&2, TFile.REnt>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{v, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+v, +s}:
          %tl.col(s) : {Tr.read.cols.cons(v, Tr.read.cols.go(m, Tr.read.col(s))) == FTh.get_cols.cons(v, FTh.get_cols.go(m, _)) : Wr.Dec<List<&2, TFile.REnt>>}
          %tl.cols.go(m, Tr.read.col(s)) : {Tr.read.cols.cons(v, Tr.read.cols.go(m, Tr.read.col(s))) == FTh.get_cols.cons(v, _) : Wr.Dec<List<&2, TFile.REnt>>}
          tl.cols.cons(v, Tr.read.cols.go(m, Tr.read.col(s)))
        case Wr.Bad{}:
          {==}

def tl.cols(r: Wr.Dec<Nat>) -> {Tr.read.cols(r) == FTh.get_cols(r) : Wr.Dec<List<&2, TFile.REnt>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %tl.col(s) : {Tr.read.cols.go(m, Tr.read.col(s)) == FTh.get_cols.go(m, _) : Wr.Dec<List<&2, TFile.REnt>>}
          tl.cols.go(m, Tr.read.col(s))
    case Wr.Bad{}:
      {==}

def tl.mjson.some(r: Wr.Dec<TFile.Json>) -> {Tr.read.mjson.some(r) == FTh.get_mjson.some(r) : Wr.Dec<Maybe<&2, TFile.Json>>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.mjson.tag(t: Nat, +s: String) -> {Tr.read.mjson.tag(t, s) == FTh.get_mjson.tag(t, s) : Wr.Dec<Maybe<&2, TFile.Json>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %tl.json.go(Wr.get_nat(s)) : {Tr.read.mjson.some(Tr.read.json.go(Wr.get_nat(s))) == FTh.get_mjson.some(_) : Wr.Dec<Maybe<&2, TFile.Json>>}
      tl.mjson.some(Tr.read.json.go(Wr.get_nat(s)))
    case 2n+p:
      {==}

def tl.mjson(r: Wr.Dec<Nat>) -> {Tr.read.mjson(r) == FTh.get_mjson(r) : Wr.Dec<Maybe<&2, TFile.Json>>}:
  match r:
    case Wr.Got{t, s}:
      tl.mjson.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.file.info(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, pg: Maybe<&2, TFile.Json>, cd: Maybe<&2, TFile.Json>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> {Tr.read.file.info(nm, vs, es, pg, cd, r) == FTh.get_file.info(nm, vs, es, pg, cd, r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.file.card(+nm: String, +vs: List<&2, TFile.Var>, +es: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> {Tr.read.file.card(nm, vs, es, pg, r) == FTh.get_file.card(nm, vs, es, pg, r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{+cd, +s}:
      %tl.mjson(Wr.get_nat(s)) : {Tr.read.file.info(nm, vs, es, pg, cd, Tr.read.mjson(Wr.get_nat(s))) == FTh.get_file.info(nm, vs, es, pg, cd, _) : Wr.Dec<TFile.RFile>}
      tl.file.info(nm, vs, es, pg, cd, Tr.read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.file.page(+nm: String, +vs: List<&2, TFile.Var>, +es: List<&2, TFile.REnt>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> {Tr.read.file.page(nm, vs, es, r) == FTh.get_file.page(nm, vs, es, r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{+pg, +s}:
      %tl.mjson(Wr.get_nat(s)) : {Tr.read.file.card(nm, vs, es, pg, Tr.read.mjson(Wr.get_nat(s))) == FTh.get_file.card(nm, vs, es, pg, _) : Wr.Dec<TFile.RFile>}
      tl.file.card(nm, vs, es, pg, Tr.read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.file.cols(+nm: String, +vs: List<&2, TFile.Var>, r: Wr.Dec<List<&2, TFile.REnt>>) -> {Tr.read.file.cols(nm, vs, r) == FTh.get_file.cols(nm, vs, r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{+es, +s}:
      %tl.mjson(Wr.get_nat(s)) : {Tr.read.file.page(nm, vs, es, Tr.read.mjson(Wr.get_nat(s))) == FTh.get_file.page(nm, vs, es, _) : Wr.Dec<TFile.RFile>}
      tl.file.page(nm, vs, es, Tr.read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.file.vars(+nm: String, r: Wr.Dec<List<&2, TFile.Var>>) -> {Tr.read.file.vars(nm, r) == FTh.get_file.vars(nm, r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{+vs, +s}:
      %tl.cols(Wr.get_nat(s)) : {Tr.read.file.cols(nm, vs, Tr.read.cols(Wr.get_nat(s))) == FTh.get_file.cols(nm, vs, _) : Wr.Dec<TFile.RFile>}
      tl.file.cols(nm, vs, Tr.read.cols(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.file(r: Wr.Dec<String>) -> {Tr.read.file(r) == FTh.get_file(r) : Wr.Dec<TFile.RFile>}:
  match r:
    case Wr.Got{+nm, +s}:
      %tl.vars(Wr.get_nat(s)) : {Tr.read.file.vars(nm, Tr.read.vars(Wr.get_nat(s))) == FTh.get_file.vars(nm, _) : Wr.Dec<TFile.RFile>}
      tl.file.vars(nm, Tr.read.vars(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.mstr.some(r: Wr.Dec<String>) -> {Tr.read.mstr.some(r) == FTh.get_mstr.some(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.mstr.tag(t: Nat, +s: String) -> {Tr.read.mstr.tag(t, s) == FTh.get_mstr.tag(t, s) : Wr.Dec<Maybe<&2, String>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      tl.mstr.some(Wr.get_str(s))
    case 2n+p:
      {==}

def tl.mstr(r: Wr.Dec<Nat>) -> {Tr.read.mstr(r) == FTh.get_mstr(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{t, s}:
      tl.mstr.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.mfile.some(r: Wr.Dec<TFile.RFile>) -> {Tr.read.mfile.some(r) == FTh.get_mfile.some(r) : Wr.Dec<Maybe<&2, TFile.RFile>>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.mfile.tag(t: Nat, +s: String) -> {Tr.read.mfile.tag(t, s) == FTh.get_mfile.tag(t, s) : Wr.Dec<Maybe<&2, TFile.RFile>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %tl.file(Wr.get_str(s)) : {Tr.read.mfile.some(Tr.read.file(Wr.get_str(s))) == FTh.get_mfile.some(_) : Wr.Dec<Maybe<&2, TFile.RFile>>}
      tl.mfile.some(Tr.read.file(Wr.get_str(s)))
    case 2n+p:
      {==}

def tl.mfile(r: Wr.Dec<Nat>) -> {Tr.read.mfile(r) == FTh.get_mfile(r) : Wr.Dec<Maybe<&2, TFile.RFile>>}:
  match r:
    case Wr.Got{t, s}:
      tl.mfile.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.src.body(c: Bool, st: Maybe<&2, String>, r: Wr.Dec<Maybe<&2, TFile.RFile>>) -> {Tr.read.src.body(c, st, r) == FTh.get_src.body(c, st, r) : Wr.Dec<TResolve.Src>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.src.stem(+c: Bool, r: Wr.Dec<Maybe<&2, String>>) -> {Tr.read.src.stem(c, r) == FTh.get_src.stem(c, r) : Wr.Dec<TResolve.Src>}:
  match r:
    case Wr.Got{+st, +s}:
      %tl.mfile(Wr.get_nat(s)) : {Tr.read.src.body(c, st, Tr.read.mfile(Wr.get_nat(s))) == FTh.get_src.body(c, st, _) : Wr.Dec<TResolve.Src>}
      tl.src.body(c, st, Tr.read.mfile(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.src.go(r: Wr.Dec<Bool>) -> {Tr.read.src.go(r) == FTh.get_src.go(r) : Wr.Dec<TResolve.Src>}:
  match r:
    case Wr.Got{+c, +s}:
      %tl.mstr(Wr.get_nat(s)) : {Tr.read.src.stem(c, Tr.read.mstr(Wr.get_nat(s))) == FTh.get_src.stem(c, _) : Wr.Dec<TResolve.Src>}
      tl.src.stem(c, Tr.read.mstr(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.src(+s: String) -> {Tr.read.src(s) == FTh.get_src(s) : Wr.Dec<TResolve.Src>}:
  tl.src.go(Wr.get_bool(s))

def tl.srcs.cons(v: TResolve.Src, r: Wr.Dec<List<&2, TResolve.Src>>) -> {Tr.read.srcs.cons(v, r) == FTh.get_srcs.cons(v, r) : Wr.Dec<List<&2, TResolve.Src>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.srcs.go(n: Nat, cur: Wr.Dec<TResolve.Src>) -> {Tr.read.srcs.go(n, cur) == FTh.get_srcs.go(n, cur) : Wr.Dec<List<&2, TResolve.Src>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{v, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+v, +s}:
          %tl.src(s) : {Tr.read.srcs.cons(v, Tr.read.srcs.go(m, Tr.read.src(s))) == FTh.get_srcs.cons(v, FTh.get_srcs.go(m, _)) : Wr.Dec<List<&2, TResolve.Src>>}
          %tl.srcs.go(m, Tr.read.src(s)) : {Tr.read.srcs.cons(v, Tr.read.srcs.go(m, Tr.read.src(s))) == FTh.get_srcs.cons(v, _) : Wr.Dec<List<&2, TResolve.Src>>}
          tl.srcs.cons(v, Tr.read.srcs.go(m, Tr.read.src(s)))
        case Wr.Bad{}:
          {==}

def tl.srcs(r: Wr.Dec<Nat>) -> {Tr.read.srcs(r) == FTh.get_srcs(r) : Wr.Dec<List<&2, TResolve.Src>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %tl.src(s) : {Tr.read.srcs.go(m, Tr.read.src(s)) == FTh.get_srcs.go(m, _) : Wr.Dec<List<&2, TResolve.Src>>}
          tl.srcs.go(m, Tr.read.src(s))
    case Wr.Bad{}:
      {==}

def tl.load(r: Wr.Dec<TFile.RFile>) -> {Tr.read.load(r) == FTh.get_load(r) : Wr.Dec<FTh.Req>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.resolve.files(n: String, r: Wr.Dec<List<&2, TResolve.Src>>) -> {Tr.read.resolve.files(n, r) == FTh.get_resolve.files(n, r) : Wr.Dec<FTh.Req>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tl.resolve(r: Wr.Dec<String>) -> {Tr.read.resolve(r) == FTh.get_resolve(r) : Wr.Dec<FTh.Req>}:
  match r:
    case Wr.Got{+n, +s}:
      %tl.srcs(Wr.get_nat(s)) : {Tr.read.resolve.files(n, Tr.read.srcs(Wr.get_nat(s))) == FTh.get_resolve.files(n, _) : Wr.Dec<FTh.Req>}
      tl.resolve.files(n, Tr.read.srcs(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def tl.shipped.tag(t: Nat, +s: String) -> {Tr.read.shipped.tag(t, s) == FTh.get_shipped.tag(t, s) : Wr.Dec<FTh.Req>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def tl.shipped(r: Wr.Dec<Nat>) -> {Tr.read.shipped(r) == FTh.get_shipped(r) : Wr.Dec<FTh.Req>}:
  match r:
    case Wr.Got{t, s}:
      tl.shipped.tag(t, s)
    case Wr.Bad{}:
      {==}

def tl.req.tag(t: Nat, +s: String) -> {Tr.read.req.tag(t, s) == FTh.get_req.tag(t, s) : Wr.Dec<FTh.Req>}:
  match t:
    case 0n:
      %tl.file(Wr.get_str(s)) : {Tr.read.load(Tr.read.file(Wr.get_str(s))) == FTh.get_load(_) : Wr.Dec<FTh.Req>}
      tl.load(Tr.read.file(Wr.get_str(s)))
    case 1n:
      tl.resolve(Wr.get_str(s))
    case 2n:
      tl.shipped(Wr.get_nat(s))
    case 3n+p:
      {==}

def tl.req.go(r: Wr.Dec<Nat>) -> {Tr.read.req.go(r) == FTh.get_req.go(r) : Wr.Dec<FTh.Req>}:
  match r:
    case Wr.Got{t, s}:
      tl.req.tag(t, s)
    case Wr.Bad{}:
      {==}
