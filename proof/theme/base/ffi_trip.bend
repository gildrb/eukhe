# eukhe: lemmas of the theme entry's proofs: every request the laws spell
# (spec/theme/wire.bend) that fits the wire reads back through the entry's
# decoders, whatever follows it (the wire's round trips, laws/wire.bend)

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/bundled.bend as TBundled
import ../../../bend/theme/resolve.bend as TResolve
import ../../../bend/ffi_theme.bend as FTh
import ../../../spec/theme/wire.bend as Tw
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../../wire/wire_u32_round_trip.bend as PWireU32RoundTrip
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# Primitives, turned around
# -------------------------

def tt.str(+a: String, +rest: String, h: {Tw.fits.str(a) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def tt.u32(+x: U32, +rest: String) -> {Wr.Got{x, rest} == Wr.get_u32(Wr.put_u32(x, rest)) : Wr.Dec<U32>}:
  Equal.sym(Wr.Dec<U32>, Wr.get_u32(Wr.put_u32(x, rest)), Wr.Got{x, rest}, Wire.wire_u32_round_trip(x, rest))

def tt.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# Values
# ------

def tt.mnat(m: Maybe<&2, Nat>, +rest: String, h: {Tw.fits.mnat(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FTh.get_mnat(Wr.get_nat(Tw.mnat(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      %LWire.pc.nat(n, rest, h) : {Wr.Got{Some{n}, rest} == FTh.get_mnat.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def tt.json(j: TFile.Json, +rest: String, +h: {Tw.fits.json(j) == True{} : Bool}) -> {Wr.Got{j, rest} == FTh.get_json.go(Wr.get_nat(Tw.json(j, rest))) : Wr.Dec<TFile.Json>}:
  match j:
    case TFile.JStr{+x, +at}:
      +hx = LLogicBool.wr_and_l(Tw.fits.str(x), Tw.fits.mnat(at), h)
      +ha = LLogicBool.wr_and_r(Tw.fits.str(x), Tw.fits.mnat(at), h)
      %tt.str(x, Tw.mnat(at, rest), hx) : {Wr.Got{TFile.JStr{x, at}, rest} == FTh.get_jstr(_) : Wr.Dec<TFile.Json>}
      %tt.mnat(at, rest, ha) : {Wr.Got{TFile.JStr{x, at}, rest} == FTh.get_jstr.at(x, _) : Wr.Dec<TFile.Json>}
      {==}
    case TFile.JNum{+x}:
      %tt.str(x, rest, h) : {Wr.Got{TFile.JNum{x}, rest} == FTh.get_jnum(_) : Wr.Dec<TFile.Json>}
      {==}
    case TFile.JOther{+x}:
      %tt.str(x, rest, h) : {Wr.Got{TFile.JOther{x}, rest} == FTh.get_jother(_) : Wr.Dec<TFile.Json>}
      {==}

def tt.mjson(m: Maybe<&2, TFile.Json>, +rest: String, h: {Tw.fits.mjson(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FTh.get_mjson(Wr.get_nat(Tw.mjson(m, rest))) : Wr.Dec<Maybe<&2, TFile.Json>>}:
  match m:
    case None{}:
      {==}
    case Some{+j}:
      %tt.json(j, rest, h) : {Wr.Got{Some{j}, rest} == FTh.get_mjson.some(_) : Wr.Dec<Maybe<&2, TFile.Json>>}
      {==}

def tt.mu32(m: Maybe<&2, U32>, +rest: String) -> {Wr.Got{m, rest} == FTh.get_mu32(Wr.get_nat(Tw.mu32(m, rest))) : Wr.Dec<Maybe<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %tt.u32(x, rest) : {Wr.Got{Some{x}, rest} == FTh.get_mu32.some(_) : Wr.Dec<Maybe<&2, U32>>}
      {==}

# Variables and colors
# --------------------

def tt.var(+n: String, +j: TFile.Json, +rest: String, hn: {Tw.fits.str(n) == True{} : Bool}, hj: {Tw.fits.json(j) == True{} : Bool}) -> {Wr.Got{TFile.Var{n, j}, rest} == FTh.get_var(Tw.var(TFile.Var{n, j}, rest)) : Wr.Dec<TFile.Var>}:
  %tt.str(n, Tw.json(j, rest), hn) : {Wr.Got{TFile.Var{n, j}, rest} == FTh.get_var.go(_) : Wr.Dec<TFile.Var>}
  %tt.json(j, rest, hj) : {Wr.Got{TFile.Var{n, j}, rest} == FTh.get_var.val(n, _) : Wr.Dec<TFile.Var>}
  {==}

def tt.vars_go(t: List<&2, TFile.Var>, v: TFile.Var, +rest: String, +h: {Tw.fits.vars(v <> t) == True{} : Bool}) -> {Wr.Got{v <> t, rest} == FTh.get_vars.go(List.length(&2, TFile.Var, t), FTh.get_var(Tw.var(v, Tw.vars.items(t, rest)))) : Wr.Dec<List<&2, TFile.Var>>}:
  match t:
    case Nil{}:
      match v:
        case TFile.Var{+n, +j}:
          +hn = LLogicBool.wr_and_l(Tw.fits.str(n), Bool.and(Tw.fits.json(j), True{}), h)
          +hr = LLogicBool.wr_and_r(Tw.fits.str(n), Bool.and(Tw.fits.json(j), True{}), h)
          +hj = LLogicBool.wr_and_l(Tw.fits.json(j), True{}, hr)
          %tt.var(n, j, rest, hn, hj) : {Wr.Got{[TFile.Var{n, j}], rest} == FTh.get_vars.go(0n, _) : Wr.Dec<List<&2, TFile.Var>>}
          {==}
    case +x <> +u:
      match v:
        case TFile.Var{+n, +j}:
          +hn = LLogicBool.wr_and_l(Tw.fits.str(n), Bool.and(Tw.fits.json(j), Tw.fits.vars(x <> u)), h)
          +hr = LLogicBool.wr_and_r(Tw.fits.str(n), Bool.and(Tw.fits.json(j), Tw.fits.vars(x <> u)), h)
          +hj = LLogicBool.wr_and_l(Tw.fits.json(j), Tw.fits.vars(x <> u), hr)
          +ht = LLogicBool.wr_and_r(Tw.fits.json(j), Tw.fits.vars(x <> u), hr)
          %tt.var(n, j, Tw.var(x, Tw.vars.items(u, rest)), hn, hj) : {Wr.Got{TFile.Var{n, j} <> x <> u, rest} == FTh.get_vars.go(1n+List.length(&2, TFile.Var, u), _) : Wr.Dec<List<&2, TFile.Var>>}
          %tt.vars_go(u, x, rest, ht) : {Wr.Got{TFile.Var{n, j} <> x <> u, rest} == FTh.get_vars.cons(TFile.Var{n, j}, _) : Wr.Dec<List<&2, TFile.Var>>}
          {==}

def tt.vars(vs: List<&2, TFile.Var>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, TFile.Var, vs)) == True{} : Bool}, h: {Tw.fits.vars(vs) == True{} : Bool}) -> {Wr.Got{vs, rest} == FTh.get_vars(Wr.get_nat(Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, rest)))) : Wr.Dec<List<&2, TFile.Var>>}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      %LWire.pc.nat(1n+List.length(&2, TFile.Var, t), Tw.var(v, Tw.vars.items(t, rest)), hl) : {Wr.Got{v <> t, rest} == FTh.get_vars(_) : Wr.Dec<List<&2, TFile.Var>>}
      tt.vars_go(t, v, rest, h)

def tt.col(+k: String, +x: Maybe<&2, U32>, +j: TFile.Json, +rest: String, hk: {Tw.fits.str(k) == True{} : Bool}, hj: {Tw.fits.json(j) == True{} : Bool}) -> {Wr.Got{TFile.REnt{k, x, j}, rest} == FTh.get_col(Tw.col(TFile.REnt{k, x, j}, rest)) : Wr.Dec<TFile.REnt>}:
  %tt.str(k, Tw.mu32(x, Tw.json(j, rest)), hk) : {Wr.Got{TFile.REnt{k, x, j}, rest} == FTh.get_col.go(_) : Wr.Dec<TFile.REnt>}
  %tt.mu32(x, Tw.json(j, rest)) : {Wr.Got{TFile.REnt{k, x, j}, rest} == FTh.get_col.tok(k, _) : Wr.Dec<TFile.REnt>}
  %tt.json(j, rest, hj) : {Wr.Got{TFile.REnt{k, x, j}, rest} == FTh.get_col.val(k, x, _) : Wr.Dec<TFile.REnt>}
  {==}

def tt.cols_go(t: List<&2, TFile.REnt>, e: TFile.REnt, +rest: String, +h: {Tw.fits.cols(e <> t) == True{} : Bool}) -> {Wr.Got{e <> t, rest} == FTh.get_cols.go(List.length(&2, TFile.REnt, t), FTh.get_col(Tw.col(e, Tw.cols.items(t, rest)))) : Wr.Dec<List<&2, TFile.REnt>>}:
  match t:
    case Nil{}:
      match e:
        case TFile.REnt{+k, +x, +j}:
          +hk = LLogicBool.wr_and_l(Tw.fits.str(k), Bool.and(Tw.fits.json(j), True{}), h)
          +hr = LLogicBool.wr_and_r(Tw.fits.str(k), Bool.and(Tw.fits.json(j), True{}), h)
          +hj = LLogicBool.wr_and_l(Tw.fits.json(j), True{}, hr)
          %tt.col(k, x, j, rest, hk, hj) : {Wr.Got{[TFile.REnt{k, x, j}], rest} == FTh.get_cols.go(0n, _) : Wr.Dec<List<&2, TFile.REnt>>}
          {==}
    case +y <> +u:
      match e:
        case TFile.REnt{+k, +x, +j}:
          +hk = LLogicBool.wr_and_l(Tw.fits.str(k), Bool.and(Tw.fits.json(j), Tw.fits.cols(y <> u)), h)
          +hr = LLogicBool.wr_and_r(Tw.fits.str(k), Bool.and(Tw.fits.json(j), Tw.fits.cols(y <> u)), h)
          +hj = LLogicBool.wr_and_l(Tw.fits.json(j), Tw.fits.cols(y <> u), hr)
          +ht = LLogicBool.wr_and_r(Tw.fits.json(j), Tw.fits.cols(y <> u), hr)
          %tt.col(k, x, j, Tw.col(y, Tw.cols.items(u, rest)), hk, hj) : {Wr.Got{TFile.REnt{k, x, j} <> y <> u, rest} == FTh.get_cols.go(1n+List.length(&2, TFile.REnt, u), _) : Wr.Dec<List<&2, TFile.REnt>>}
          %tt.cols_go(u, y, rest, ht) : {Wr.Got{TFile.REnt{k, x, j} <> y <> u, rest} == FTh.get_cols.cons(TFile.REnt{k, x, j}, _) : Wr.Dec<List<&2, TFile.REnt>>}
          {==}

def tt.cols(es: List<&2, TFile.REnt>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, TFile.REnt, es)) == True{} : Bool}, h: {Tw.fits.cols(es) == True{} : Bool}) -> {Wr.Got{es, rest} == FTh.get_cols(Wr.get_nat(Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, rest)))) : Wr.Dec<List<&2, TFile.REnt>>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      %LWire.pc.nat(1n+List.length(&2, TFile.REnt, t), Tw.col(e, Tw.cols.items(t, rest)), hl) : {Wr.Got{e <> t, rest} == FTh.get_cols(_) : Wr.Dec<List<&2, TFile.REnt>>}
      tt.cols_go(t, e, rest, h)

# Files
# -----

def tt.file(f: TFile.RFile, +rest: String, +h: {Tw.fits.file(f) == True{} : Bool}) -> {Wr.Got{f, rest} == FTh.get_file(Wr.get_str(Tw.file(f, rest))) : Wr.Dec<TFile.RFile>}:
  match f:
    case TFile.RFile{+nm, +vs, +es, +pg, +cd, +io}:
      +b8 = Tw.fits.mjson(io)
      +b7 = Bool.and(Tw.fits.mjson(cd), b8)
      +b6 = Bool.and(Tw.fits.mjson(pg), b7)
      +b5 = Bool.and(Tw.fits.cols(es), b6)
      +b4 = Bool.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), b5)
      +b3 = Bool.and(Tw.fits.vars(vs), b4)
      +b2 = Bool.and(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), b3)
      +h1 = LLogicBool.wr_and_l(Tw.fits.str(nm), b2, h)
      +g2 = LLogicBool.wr_and_r(Tw.fits.str(nm), b2, h)
      +h2 = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), b3, g2)
      +g3 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), b3, g2)
      +h3 = LLogicBool.wr_and_l(Tw.fits.vars(vs), b4, g3)
      +g4 = LLogicBool.wr_and_r(Tw.fits.vars(vs), b4, g3)
      +h4 = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), b5, g4)
      +g5 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), b5, g4)
      +h5 = LLogicBool.wr_and_l(Tw.fits.cols(es), b6, g5)
      +g6 = LLogicBool.wr_and_r(Tw.fits.cols(es), b6, g5)
      +h6 = LLogicBool.wr_and_l(Tw.fits.mjson(pg), b7, g6)
      +g7 = LLogicBool.wr_and_r(Tw.fits.mjson(pg), b7, g6)
      +h7 = LLogicBool.wr_and_l(Tw.fits.mjson(cd), b8, g7)
      +h8 = LLogicBool.wr_and_r(Tw.fits.mjson(cd), b8, g7)
      +r3 = Tw.mjson(io, rest)
      +r2 = Tw.mjson(cd, r3)
      +r1 = Tw.mjson(pg, r2)
      +c1 = Wr.put_nat(List.length(&2, TFile.REnt, es), Tw.cols.items(es, r1))
      +v1 = Wr.put_nat(List.length(&2, TFile.Var, vs), Tw.vars.items(vs, c1))
      %tt.str(nm, v1, h1) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file(_) : Wr.Dec<TFile.RFile>}
      %tt.vars(vs, c1, h2, h3) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file.vars(nm, _) : Wr.Dec<TFile.RFile>}
      %tt.cols(es, r1, h4, h5) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file.cols(nm, vs, _) : Wr.Dec<TFile.RFile>}
      %tt.mjson(pg, r2, h6) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file.page(nm, vs, es, _) : Wr.Dec<TFile.RFile>}
      %tt.mjson(cd, r3, h7) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file.card(nm, vs, es, pg, _) : Wr.Dec<TFile.RFile>}
      %tt.mjson(io, rest, h8) : {Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, rest} == FTh.get_file.info(nm, vs, es, pg, cd, _) : Wr.Dec<TFile.RFile>}
      {==}

# Sources
# -------

def tt.mfile(+f: TFile.RFile, +rest: String, h: {Tw.fits.file(f) == True{} : Bool}) -> {Wr.Got{Some{f}, rest} == FTh.get_mfile(Wr.get_nat(Tw.mfile(Some{f}, rest))) : Wr.Dec<Maybe<&2, TFile.RFile>>}:
  %tt.file(f, rest, h) : {Wr.Got{Some{f}, rest} == FTh.get_mfile.some(_) : Wr.Dec<Maybe<&2, TFile.RFile>>}
  {==}

def tt.mstr(+x: String, +rest: String, h: {Tw.fits.str(x) == True{} : Bool}) -> {Wr.Got{Some{x}, rest} == FTh.get_mstr(Wr.get_nat(Tw.mstr(Some{x}, rest))) : Wr.Dec<Maybe<&2, String>>}:
  %tt.str(x, rest, h) : {Wr.Got{Some{x}, rest} == FTh.get_mstr.some(_) : Wr.Dec<Maybe<&2, String>>}
  {==}

def tt.src(s: TResolve.Src, +rest: String, +h: {Tw.fits.src(s) == True{} : Bool}) -> {Wr.Got{s, rest} == FTh.get_src(Tw.src(s, rest)) : Wr.Dec<TResolve.Src>}:
  match s:
    case TResolve.Src{+c, +st, +b}:
      match st:
        case None{}:
          match b:
            case None{}:
              %tt.bool(c, Tw.mstr(None{}, Tw.mfile(None{}, rest))) : {Wr.Got{TResolve.Src{c, None{}, None{}}, rest} == FTh.get_src.go(_) : Wr.Dec<TResolve.Src>}
              {==}
            case Some{+f}:
              %tt.bool(c, Tw.mstr(None{}, Tw.mfile(Some{f}, rest))) : {Wr.Got{TResolve.Src{c, None{}, Some{f}}, rest} == FTh.get_src.go(_) : Wr.Dec<TResolve.Src>}
              %tt.mfile(f, rest, h) : {Wr.Got{TResolve.Src{c, None{}, Some{f}}, rest} == FTh.get_src.body(c, None{}, _) : Wr.Dec<TResolve.Src>}
              {==}
        case Some{+x}:
          match b:
            case None{}:
              %tt.bool(c, Tw.mstr(Some{x}, Tw.mfile(None{}, rest))) : {Wr.Got{TResolve.Src{c, Some{x}, None{}}, rest} == FTh.get_src.go(_) : Wr.Dec<TResolve.Src>}
              %tt.mstr(x, Tw.mfile(None{}, rest), h) : {Wr.Got{TResolve.Src{c, Some{x}, None{}}, rest} == FTh.get_src.stem(c, _) : Wr.Dec<TResolve.Src>}
              {==}
            case Some{+f}:
              +hx = LLogicBool.wr_and_l(Tw.fits.str(x), Tw.fits.file(f), h)
              +hf = LLogicBool.wr_and_r(Tw.fits.str(x), Tw.fits.file(f), h)
              %tt.bool(c, Tw.mstr(Some{x}, Tw.mfile(Some{f}, rest))) : {Wr.Got{TResolve.Src{c, Some{x}, Some{f}}, rest} == FTh.get_src.go(_) : Wr.Dec<TResolve.Src>}
              %tt.mstr(x, Tw.mfile(Some{f}, rest), hx) : {Wr.Got{TResolve.Src{c, Some{x}, Some{f}}, rest} == FTh.get_src.stem(c, _) : Wr.Dec<TResolve.Src>}
              %tt.mfile(f, rest, hf) : {Wr.Got{TResolve.Src{c, Some{x}, Some{f}}, rest} == FTh.get_src.body(c, Some{x}, _) : Wr.Dec<TResolve.Src>}
              {==}

def tt.srcs_go(t: List<&2, TResolve.Src>, +x: TResolve.Src, +rest: String, +h: {Tw.fits.srcs(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == FTh.get_srcs.go(List.length(&2, TResolve.Src, t), FTh.get_src(Tw.src(x, Tw.srcs.items(t, rest)))) : Wr.Dec<List<&2, TResolve.Src>>}:
  match t:
    case Nil{}:
      +hx = LLogicBool.wr_and_l(Tw.fits.src(x), True{}, h)
      %tt.src(x, rest, hx) : {Wr.Got{[x], rest} == FTh.get_srcs.go(0n, _) : Wr.Dec<List<&2, TResolve.Src>>}
      {==}
    case +y <> +u:
      +hx = LLogicBool.wr_and_l(Tw.fits.src(x), Tw.fits.srcs(y <> u), h)
      +ht = LLogicBool.wr_and_r(Tw.fits.src(x), Tw.fits.srcs(y <> u), h)
      %tt.src(x, Tw.src(y, Tw.srcs.items(u, rest)), hx) : {Wr.Got{x <> y <> u, rest} == FTh.get_srcs.go(1n+List.length(&2, TResolve.Src, u), _) : Wr.Dec<List<&2, TResolve.Src>>}
      %tt.srcs_go(u, y, rest, ht) : {Wr.Got{x <> y <> u, rest} == FTh.get_srcs.cons(x, _) : Wr.Dec<List<&2, TResolve.Src>>}
      {==}

def tt.srcs(ss: List<&2, TResolve.Src>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)) == True{} : Bool}, h: {Tw.fits.srcs(ss) == True{} : Bool}) -> {Wr.Got{ss, rest} == FTh.get_srcs(Wr.get_nat(Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.srcs.items(ss, rest)))) : Wr.Dec<List<&2, TResolve.Src>>}:
  match ss:
    case Nil{}:
      {==}
    case +x <> +t:
      %LWire.pc.nat(1n+List.length(&2, TResolve.Src, t), Tw.src(x, Tw.srcs.items(t, rest)), hl) : {Wr.Got{x <> t, rest} == FTh.get_srcs(_) : Wr.Dec<List<&2, TResolve.Src>>}
      tt.srcs_go(t, x, rest, h)

# Requests
# --------

# a request the laws spell that fits reads back, whatever follows it
def tt.req(r: FTh.Req, +rest: String, +h: {Tw.fits(r) == True{} : Bool}) -> {Wr.Got{r, rest} == FTh.get_req.go(Wr.get_nat(Tw.req(r, rest))) : Wr.Dec<FTh.Req>}:
  match r:
    case FTh.Load{+f}:
      %tt.file(f, rest, h) : {Wr.Got{FTh.Load{f}, rest} == FTh.get_load(_) : Wr.Dec<FTh.Req>}
      {==}
    case FTh.Resolve{+n, +ss}:
      +hn = LLogicBool.wr_and_l(Tw.fits.str(n), Bool.and(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss)), h)
      +hr = LLogicBool.wr_and_r(Tw.fits.str(n), Bool.and(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss)), h)
      +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss), hr)
      +hs = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), Tw.fits.srcs(ss), hr)
      %tt.str(n, Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.srcs.items(ss, rest)), hn) : {Wr.Got{FTh.Resolve{n, ss}, rest} == FTh.get_resolve(_) : Wr.Dec<FTh.Req>}
      %tt.srcs(ss, rest, hl, hs) : {Wr.Got{FTh.Resolve{n, ss}, rest} == FTh.get_resolve.files(n, _) : Wr.Dec<FTh.Req>}
      {==}
    case FTh.Shipped{s}:
      match s:
        case TBundled.Eukhe{}:
          {==}
        case TBundled.Dark{}:
          {==}
        case TBundled.Light{}:
          {==}
