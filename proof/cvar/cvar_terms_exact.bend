# eukhe: the proof of LAW cvar_terms_exact
# Each predicate, case by case: the lookup is the spec's (LR.re.find), a
# cvar is taken in a list exactly when it is one of its ids (LR.re.mem), and
# the type test is the spec's (LR.re.ty).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar.bend as Cvar
import ./base/resolve.bend as LR

def tm.unique(ds: List<&2, Cv.Decl>) -> {Cv.unique(ds) == Cvar.spec_unique(ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Cv.Decl{+i, t, c, p, r, v} <> +rest:
      %LR.re.mem(rest, i) : {Cv.unique(Cv.Decl{i, t, c, p, r, v} <> rest) == Bool.and(Bool.not(_), Cvar.spec_unique(rest)) : Bool}
      %tm.unique(rest) : {Cv.unique(Cv.Decl{i, t, c, p, r, v} <> rest) == Bool.and(Bool.not(Maybe.is_some(&2, Cv.Decl, Cv.find(rest, i))), _) : Bool}
      {==}

def tm.typed(ds: List<&2, Cv.Decl>) -> {Cv.all_typed(ds) == Cvar.spec_all_typed(ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Cv.Decl{i, +t, c, p, r, +v} <> +rest:
      %LR.re.ty(v, t) : {Cv.all_typed(Cv.Decl{i, t, c, p, r, v} <> rest) == Bool.and(_, Cvar.spec_all_typed(rest)) : Bool}
      %tm.typed(rest) : {Cv.all_typed(Cv.Decl{i, t, c, p, r, v} <> rest) == Bool.and(Cv.Ty.eq(Cv.Val.ty(v), t), _) : Bool}
      {==}

def tm.typed_at(m: Maybe<&2, Cv.Decl>, v: Maybe<&2, Cv.Val>) -> {Cv.typed.at(m, v) == Cvar.spec_typed_at(m, v) : Bool}:
  match m:
    case None{}:
      match v:
        case None{}:
          {==}
        case Some{y}:
          {==}
    case Some{d}:
      match d:
        case Cv.Decl{i, +t, c, p, r, w}:
          match v:
            case None{}:
              {==}
            case Some{+y}:
              LR.re.ty(y, t)

def tm.flag_at(m: Maybe<&2, Cv.Decl>, f: Cv.Flag) -> {Cv.flag.at(m, f) == Cvar.spec_flag.at(m, f) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      match d:
        case Cv.Decl{i, t, c, p, r, v}:
          match f:
            case Cv.Persist{}:
              {==}
            case Cv.Replicate{}:
              {==}

def tm.flag(ss: List<&2, Cv.Bind>, +es: List<&2, Cv.Decl>, +f: Cv.Flag) -> {Cv.all_flag(ss, es, f) == Cvar.spec_all_flag(ss, es, f) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Cv.Bind{+i, v} <> +rest:
      %LR.re.find(es, i) : {Cv.all_flag(Cv.Bind{i, v} <> rest, es, f) == Bool.and(Cvar.spec_flag.at(_, f), Cvar.spec_all_flag(rest, es, f)) : Bool}
      %tm.flag_at(Cv.find(es, i), f) : {Cv.all_flag(Cv.Bind{i, v} <> rest, es, f) == Bool.and(_, Cvar.spec_all_flag(rest, es, f)) : Bool}
      %tm.flag(rest, es, f) : {Cv.all_flag(Cv.Bind{i, v} <> rest, es, f) == Bool.and(Cv.flag.at(Cv.find(es, i), f), _) : Bool}
      {==}

def tm.plain(cs: List<&2, Cv.Cmd>) -> {Cv.plain(cs) == Cvar.spec_plain(cs) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case Cv.CSet{i, v}:
          tm.plain(rest)
        case Cv.CToggle{i}:
          tm.plain(rest)
        case Cv.CRun{n}:
          {==}
        case Cv.CGone{n}:
          {==}

def tm.exp(e: Cv.Exp) -> {Cv.Exp.plain(e) == Cvar.spec_exp_plain(e) : Bool}:
  match e:
    case Cv.Flat{cs}:
      tm.plain(cs)
    case Cv.Cycle{n}:
      {==}
    case Cv.Unknown{n}:
      {==}

def Cvar.cvar_terms_exact(ds, m, v, ss, es, f, e):
  (tm.unique(ds), (tm.typed(ds), (tm.typed_at(m, v), (tm.flag(ss, es, f), tm.exp(e)))))
