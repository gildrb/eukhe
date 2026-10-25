# eukhe: lemmas of the refine_plan entry proofs: a spelled request
# reads back (rpe.*_rt, from the wire round trips)

import Base
import ../../../bend/refine_plan.bend as Rp
import ../../../bend/ffi_refine_plan.bend as FRp
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/refine_plan/entry.bend as E
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool

def rpe.verb_rt(x: Rp.Verb, rest: String) -> {FRp.get_verb(E.rp_w_verb(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Verb>}:
  match x:
    case Rp.ACreate{}:
      {==}
    case Rp.AUpdate{}:
      {==}
    case Rp.ADelete{}:
      {==}

def rpe.comp_rt(x: Rp.Comp, rest: String) -> {FRp.get_comp(E.rp_w_comp(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Comp>}:
  match x:
    case Rp.KPrompt{}:
      {==}
    case Rp.KMemory{}:
      {==}
    case Rp.KSkill{}:
      {==}
    case Rp.KSubagent{}:
      {==}
    case Rp.KFactory{}:
      {==}

def rpe.val_rt(x: Rp.Val, rest: String) -> {FRp.get_val(E.rp_w_val(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Val>}:
  match x:
    case Rp.VMissing{}:
      {==}
    case Rp.VNull{}:
      {==}
    case Rp.VObject{}:
      {==}
    case Rp.VOther{}:
      {==}

def rpe.ms_rt(m: Maybe<&2, String>, +rest: String, h: {E.rp_fit_ms(m) == True{} : Bool}) -> {FRp.get_ms(E.rp_w_ms(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FRp.get_ms.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def rpe.pyref_rt(x: Rp.Pyref, +rest: String, h: {E.rp_fit_pyref(x) == True{} : Bool}) -> {FRp.get_pyref(E.rp_w_pyref(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Pyref>}:
  match x:
    case Rp.Pyref{+v1, +v2, +v3, +v4, +v5}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)))), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)))), hh0)
      +hh1 = hh0r
      +h2 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5))), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v2), Bool.and(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5))), hh1)
      +hh2 = hh1r
      +h3 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)), hh2)
      +hh2r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_ms(v5)), hh2)
      +hh3 = hh2r
      +h4 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v4), E.rp_fit_ms(v5), hh3)
      +hh3r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v4), E.rp_fit_ms(v5), hh3)
      +h5 = hh3r
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest)))))), Wr.Got{v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest))))}, rpe.ms_rt(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest)))), h1)) : {FRp.get_pyref.f1(_) == Wr.Got{Rp.Pyref{v1, v2, v3, v4, v5}, rest} : Wr.Dec<Rp.Pyref>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest))))), Wr.Got{v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest)))}, rpe.ms_rt(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest))), h2)) : {FRp.get_pyref.f2(v1, _) == Wr.Got{Rp.Pyref{v1, v2, v3, v4, v5}, rest} : Wr.Dec<Rp.Pyref>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest)))), Wr.Got{v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest))}, rpe.ms_rt(v3, E.rp_w_ms(v4, E.rp_w_ms(v5, rest)), h3)) : {FRp.get_pyref.f3(v1, v2, _) == Wr.Got{Rp.Pyref{v1, v2, v3, v4, v5}, rest} : Wr.Dec<Rp.Pyref>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v4, E.rp_w_ms(v5, rest))), Wr.Got{v4, E.rp_w_ms(v5, rest)}, rpe.ms_rt(v4, E.rp_w_ms(v5, rest), h4)) : {FRp.get_pyref.f4(v1, v2, v3, _) == Wr.Got{Rp.Pyref{v1, v2, v3, v4, v5}, rest} : Wr.Dec<Rp.Pyref>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v5, rest)), Wr.Got{v5, rest}, rpe.ms_rt(v5, rest, h5)) : {FRp.get_pyref.f5(v1, v2, v3, v4, _) == Wr.Got{Rp.Pyref{v1, v2, v3, v4, v5}, rest} : Wr.Dec<Rp.Pyref>}
      {==}

def rpe.args_rt(x: Rp.Args, +rest: String) -> {FRp.get_args(E.rp_w_args(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Args>}:
  match x:
    case Rp.Args{+v1, +v2}:
      %Equal.sym(Wr.Dec<Rp.Val>, FRp.get_val(E.rp_w_val(v1, E.rp_w_val(v2, rest))), Wr.Got{v1, E.rp_w_val(v2, rest)}, rpe.val_rt(v1, E.rp_w_val(v2, rest))) : {FRp.get_args.f1(_) == Wr.Got{Rp.Args{v1, v2}, rest} : Wr.Dec<Rp.Args>}
      %Equal.sym(Wr.Dec<Rp.Val>, FRp.get_val(E.rp_w_val(v2, rest)), Wr.Got{v2, rest}, rpe.val_rt(v2, rest)) : {FRp.get_args.f2(v1, _) == Wr.Got{Rp.Args{v1, v2}, rest} : Wr.Dec<Rp.Args>}
      {==}

def rpe.mverb_rt(m: Maybe<&2, Rp.Verb>, +rest: String) -> {FRp.get_mverb(E.rp_w_mverb(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Rp.Verb>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Rp.Verb>, FRp.get_verb(E.rp_w_verb(x, rest)), Wr.Got{x, rest}, rpe.verb_rt(x, rest)) : {FRp.get_mverb.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Rp.Verb>>}
      {==}

def rpe.mcomp_rt(m: Maybe<&2, Rp.Comp>, +rest: String) -> {FRp.get_mcomp(E.rp_w_mcomp(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Rp.Comp>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Rp.Comp>, FRp.get_comp(E.rp_w_comp(x, rest)), Wr.Got{x, rest}, rpe.comp_rt(x, rest)) : {FRp.get_mcomp.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Rp.Comp>>}
      {==}

def rpe.mpyref_rt(m: Maybe<&2, Rp.Pyref>, +rest: String, h: {E.rp_fit_mpyref(m) == True{} : Bool}) -> {FRp.get_mpyref(E.rp_w_mpyref(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Rp.Pyref>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Rp.Pyref>, FRp.get_pyref(E.rp_w_pyref(x, rest)), Wr.Got{x, rest}, rpe.pyref_rt(x, rest, h)) : {FRp.get_mpyref.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Rp.Pyref>>}
      {==}

def rpe.margs_rt(m: Maybe<&2, Rp.Args>, +rest: String) -> {FRp.get_margs(E.rp_w_margs(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Rp.Args>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<Rp.Args>, FRp.get_args(E.rp_w_args(x, rest)), Wr.Got{x, rest}, rpe.args_rt(x, rest)) : {FRp.get_margs.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Rp.Args>>}
      {==}

def rpe.ed_rt(x: Rp.Ed, +rest: String, h: {E.rp_fit_ed(x) == True{} : Bool}) -> {FRp.get_ed(E.rp_w_ed(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Ed>}:
  match x:
    case Rp.Ed{+v1, +v2, +v3, +v4, +v5, +v6, +v7, +v8, +v9, +v10}:
      +hh0 = h
      +h3 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6)), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v3), Bool.and(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6)), hh0)
      +hh1 = hh0r
      +h4 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v4), E.rp_fit_mpyref(v6), hh1)
      +h6 = hh1r
      %Equal.sym(Wr.Dec<Maybe<&2, Rp.Verb>>, FRp.get_mverb(E.rp_w_mverb(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))))))), Wr.Got{v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))))))}, rpe.mverb_rt(v1, E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))))))) : {FRp.get_ed.f1(_) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Maybe<&2, Rp.Comp>>, FRp.get_mcomp(E.rp_w_mcomp(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))))))), Wr.Got{v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))))}, rpe.mcomp_rt(v2, E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))))))) : {FRp.get_ed.f2(v1, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))))), Wr.Got{v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))))}, rpe.ms_rt(v3, E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))), h3)) : {FRp.get_ed.f3(v1, v2, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))))), Wr.Got{v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))}, rpe.ms_rt(v4, Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))), h4)) : {FRp.get_ed.f4(v1, v2, v3, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))), Wr.Got{v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))}, Wire.wire_bool_round_trip(v5, E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))))) : {FRp.get_ed.f5(v1, v2, v3, v4, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Maybe<&2, Rp.Pyref>>, FRp.get_mpyref(E.rp_w_mpyref(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))))), Wr.Got{v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))}, rpe.mpyref_rt(v6, E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))), h6)) : {FRp.get_ed.f6(v1, v2, v3, v4, v5, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Maybe<&2, Rp.Args>>, FRp.get_margs(E.rp_w_margs(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))), Wr.Got{v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))}, rpe.margs_rt(v7, Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))))) : {FRp.get_ed.f7(v1, v2, v3, v4, v5, v6, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))), Wr.Got{v8, Wr.put_bool(v9, Wr.put_bool(v10, rest))}, Wire.wire_bool_round_trip(v8, Wr.put_bool(v9, Wr.put_bool(v10, rest)))) : {FRp.get_ed.f8(v1, v2, v3, v4, v5, v6, v7, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v9, Wr.put_bool(v10, rest))), Wr.Got{v9, Wr.put_bool(v10, rest)}, Wire.wire_bool_round_trip(v9, Wr.put_bool(v10, rest))) : {FRp.get_ed.f9(v1, v2, v3, v4, v5, v6, v7, v8, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v10, rest)), Wr.Got{v10, rest}, Wire.wire_bool_round_trip(v10, rest)) : {FRp.get_ed.f10(v1, v2, v3, v4, v5, v6, v7, v8, v9, _) == Wr.Got{Rp.Ed{v1, v2, v3, v4, v5, v6, v7, v8, v9, v10}, rest} : Wr.Dec<Rp.Ed>}
      {==}

def rpe.eds_go(+t: List<&2, Rp.Ed>, +x: Rp.Ed, +rest: String, +hx: {E.rp_fit_ed(x) == True{} : Bool}, +ht: {E.rp_fit_eds.items(t) == True{} : Bool}) ->
  {Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, List.length(&2, Rp.Ed, t), FRp.get_ed(E.rp_w_ed(x, E.rp_w_eds.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Rp.Ed>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Rp.Ed>, FRp.get_ed(E.rp_w_ed(x, rest)), Wr.Got{x, rest}, rpe.ed_rt(x, rest, hx)) : {Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Rp.Ed>>}
      {==}
    case Con{+y, +u}:
      +r2 = E.rp_w_ed(y, E.rp_w_eds.items(u, rest))
      +hy = LLogicBool.tree.pt.and_l(E.rp_fit_ed(y), E.rp_fit_eds.items(u), ht)
      +hu = LLogicBool.tree.pt.and_r(E.rp_fit_ed(y), E.rp_fit_eds.items(u), ht)
      %Equal.sym(Wr.Dec<Rp.Ed>, FRp.get_ed(E.rp_w_ed(x, r2)), Wr.Got{x, r2}, rpe.ed_rt(x, r2, hx)) : {Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, 1n+List.length(&2, Rp.Ed, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rp.Ed>>}
      %Equal.sym(Wr.Dec<List<&2, Rp.Ed>>, Wr.get_list.go(~Rp.Ed, ~FRp.get_ed, List.length(&2, Rp.Ed, u), FRp.get_ed(r2)), Wr.Got{y <> u, rest}, rpe.eds_go(u, y, rest, hy, hu)) : {Wr.get_list.cons(Rp.Ed, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rp.Ed>>}
      {==}

def rpe.eds_rt(xs: List<&2, Rp.Ed>, +rest: String, h: {E.rp_fit_eds(xs) == True{} : Bool}) -> {FRp.get_eds(E.rp_w_eds(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Rp.Ed>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +h0 = h
      +hc = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(1n+List.length(&2, Rp.Ed, t)), E.rp_fit_eds.items(x <> t), h0)
      +hi = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(1n+List.length(&2, Rp.Ed, t)), E.rp_fit_eds.items(x <> t), h0)
      +hx = LLogicBool.tree.pt.and_l(E.rp_fit_ed(x), E.rp_fit_eds.items(t), hi)
      +ht = LLogicBool.tree.pt.and_r(E.rp_fit_ed(x), E.rp_fit_eds.items(t), hi)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+List.length(&2, Rp.Ed, t), E.rp_w_eds.items(x <> t, rest))), Wr.Got{1n+List.length(&2, Rp.Ed, t), E.rp_w_eds.items(x <> t, rest)}, Wire.wire_nat_round_trip(1n+List.length(&2, Rp.Ed, t), E.rp_w_eds.items(x <> t, rest), hc)) : {Wr.get_list.start(~Rp.Ed, ~FRp.get_ed, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Rp.Ed>>}
      rpe.eds_go(t, x, rest, hx, ht)

def rpe.opts_rt(x: Rp.Opts, +rest: String) -> {FRp.get_opts(E.rp_w_opts(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Opts>}:
  match x:
    case Rp.Opts{+v1, +v2}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v1, Wr.put_bool(v2, rest))), Wr.Got{v1, Wr.put_bool(v2, rest)}, Wire.wire_bool_round_trip(v1, Wr.put_bool(v2, rest))) : {FRp.get_opts.f1(_) == Wr.Got{Rp.Opts{v1, v2}, rest} : Wr.Dec<Rp.Opts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v2, rest)), Wr.Got{v2, rest}, Wire.wire_bool_round_trip(v2, rest)) : {FRp.get_opts.f2(v1, _) == Wr.Got{Rp.Opts{v1, v2}, rest} : Wr.Dec<Rp.Opts>}
      {==}

def rpe.was_rt(x: Rp.Was, +rest: String) -> {FRp.get_was(E.rp_w_was(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Was>}:
  match x:
    case Rp.Was{+v1, +v2, +v3}:
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v1, Wr.put_bool(v2, Wr.put_bool(v3, rest)))), Wr.Got{v1, Wr.put_bool(v2, Wr.put_bool(v3, rest))}, Wire.wire_bool_round_trip(v1, Wr.put_bool(v2, Wr.put_bool(v3, rest)))) : {FRp.get_was.f1(_) == Wr.Got{Rp.Was{v1, v2, v3}, rest} : Wr.Dec<Rp.Was>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v2, Wr.put_bool(v3, rest))), Wr.Got{v2, Wr.put_bool(v3, rest)}, Wire.wire_bool_round_trip(v2, Wr.put_bool(v3, rest))) : {FRp.get_was.f2(v1, _) == Wr.Got{Rp.Was{v1, v2, v3}, rest} : Wr.Dec<Rp.Was>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(v3, rest)), Wr.Got{v3, rest}, Wire.wire_bool_round_trip(v3, rest)) : {FRp.get_was.f3(v1, v2, _) == Wr.Got{Rp.Was{v1, v2, v3}, rest} : Wr.Dec<Rp.Was>}
      {==}

def rpe.wl_go(+t: List<&2, Rp.Was>, +x: Rp.Was, +rest: String) ->
  {Wr.get_list.go(~Rp.Was, ~FRp.get_was, List.length(&2, Rp.Was, t), FRp.get_was(E.rp_w_was(x, E.rp_w_wl.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Rp.Was>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Rp.Was>, FRp.get_was(E.rp_w_was(x, rest)), Wr.Got{x, rest}, rpe.was_rt(x, rest)) : {Wr.get_list.go(~Rp.Was, ~FRp.get_was, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Rp.Was>>}
      {==}
    case Con{+y, +u}:
      +r2 = E.rp_w_was(y, E.rp_w_wl.items(u, rest))
      %Equal.sym(Wr.Dec<Rp.Was>, FRp.get_was(E.rp_w_was(x, r2)), Wr.Got{x, r2}, rpe.was_rt(x, r2)) : {Wr.get_list.go(~Rp.Was, ~FRp.get_was, 1n+List.length(&2, Rp.Was, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rp.Was>>}
      %Equal.sym(Wr.Dec<List<&2, Rp.Was>>, Wr.get_list.go(~Rp.Was, ~FRp.get_was, List.length(&2, Rp.Was, u), FRp.get_was(r2)), Wr.Got{y <> u, rest}, rpe.wl_go(u, y, rest)) : {Wr.get_list.cons(Rp.Was, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Rp.Was>>}
      {==}

def rpe.wl_rt(xs: List<&2, Rp.Was>, +rest: String, h: {E.rp_fit_wl(xs) == True{} : Bool}) -> {FRp.get_wl(E.rp_w_wl(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Rp.Was>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hc = h
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+List.length(&2, Rp.Was, t), E.rp_w_wl.items(x <> t, rest))), Wr.Got{1n+List.length(&2, Rp.Was, t), E.rp_w_wl.items(x <> t, rest)}, Wire.wire_nat_round_trip(1n+List.length(&2, Rp.Was, t), E.rp_w_wl.items(x <> t, rest), hc)) : {Wr.get_list.start(~Rp.Was, ~FRp.get_was, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Rp.Was>>}
      rpe.wl_go(t, x, rest)

def rpe.win_rt(x: Rp.Win, +rest: String, h: {E.rp_fit_win(x) == True{} : Bool}) -> {FRp.get_win(E.rp_w_win(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Win>}:
  match x:
    case Rp.Win{+v1, +v2, +v3, +v4}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4))), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4))), hh0)
      +hh1 = hh0r
      +h2 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4)), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v2), Bool.and(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4)), hh1)
      +hh2 = hh1r
      +h3 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4), hh2)
      +hh2r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v3), LawsBase.wire_fits(v4), hh2)
      +h4 = hh2r
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, Wr.put_nat(v4, rest))))), Wr.Got{v1, Wr.put_nat(v2, Wr.put_nat(v3, Wr.put_nat(v4, rest)))}, Wire.wire_nat_round_trip(v1, Wr.put_nat(v2, Wr.put_nat(v3, Wr.put_nat(v4, rest))), h1)) : {FRp.get_win.f1(_) == Wr.Got{Rp.Win{v1, v2, v3, v4}, rest} : Wr.Dec<Rp.Win>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v2, Wr.put_nat(v3, Wr.put_nat(v4, rest)))), Wr.Got{v2, Wr.put_nat(v3, Wr.put_nat(v4, rest))}, Wire.wire_nat_round_trip(v2, Wr.put_nat(v3, Wr.put_nat(v4, rest)), h2)) : {FRp.get_win.f2(v1, _) == Wr.Got{Rp.Win{v1, v2, v3, v4}, rest} : Wr.Dec<Rp.Win>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v3, Wr.put_nat(v4, rest))), Wr.Got{v3, Wr.put_nat(v4, rest)}, Wire.wire_nat_round_trip(v3, Wr.put_nat(v4, rest), h3)) : {FRp.get_win.f3(v1, v2, _) == Wr.Got{Rp.Win{v1, v2, v3, v4}, rest} : Wr.Dec<Rp.Win>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v4, rest)), Wr.Got{v4, rest}, Wire.wire_nat_round_trip(v4, rest, h4)) : {FRp.get_win.f4(v1, v2, v3, _) == Wr.Got{Rp.Win{v1, v2, v3, v4}, rest} : Wr.Dec<Rp.Win>}
      {==}

def rpe.search_rt(x: Rp.Search, +rest: String, h: {E.rp_fit_search(x) == True{} : Bool}) -> {FRp.get_search(E.rp_w_search(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Rp.Search>}:
  match x:
    case Rp.SFull{}:
      {==}
    case Rp.SProbe{+v1, +v2, +v3}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), hh0)
      +hh1 = hh0r
      +h2 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), hh1)
      +h3 = hh1r
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, rest)))), Wr.Got{v1, Wr.put_nat(v2, Wr.put_nat(v3, rest))}, Wire.wire_nat_round_trip(v1, Wr.put_nat(v2, Wr.put_nat(v3, rest)), h1)) : {FRp.get_search.sprobe.f1(_) == Wr.Got{Rp.SProbe{v1, v2, v3}, rest} : Wr.Dec<Rp.Search>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v2, Wr.put_nat(v3, rest))), Wr.Got{v2, Wr.put_nat(v3, rest)}, Wire.wire_nat_round_trip(v2, Wr.put_nat(v3, rest), h2)) : {FRp.get_search.sprobe.f2(v1, _) == Wr.Got{Rp.SProbe{v1, v2, v3}, rest} : Wr.Dec<Rp.Search>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v3, rest)), Wr.Got{v3, rest}, Wire.wire_nat_round_trip(v3, rest, h3)) : {FRp.get_search.sprobe.f3(v1, v2, _) == Wr.Got{Rp.SProbe{v1, v2, v3}, rest} : Wr.Dec<Rp.Search>}
      {==}
    case Rp.SFinal{}:
      {==}

def rpe.req_rt(x: FRp.Req, +rest: String, h: {E.rp_fit_req(x) == True{} : Bool}) -> {FRp.get_req(E.rp_w_req(x, rest)) == Wr.Got{x, rest} : Wr.Dec<FRp.Req>}:
  match x:
    case FRp.QIds{+v1}:
      +h1 = h
      %Equal.sym(Wr.Dec<List<&2, Rp.Ed>>, FRp.get_eds(E.rp_w_eds(v1, rest)), Wr.Got{v1, rest}, rpe.eds_rt(v1, rest, h1)) : {FRp.get_req.qids.f1(_) == Wr.Got{FRp.QIds{v1}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.QPlan{+v1, +v2}:
      +h2 = h
      %Equal.sym(Wr.Dec<Rp.Opts>, FRp.get_opts(E.rp_w_opts(v1, E.rp_w_eds(v2, rest))), Wr.Got{v1, E.rp_w_eds(v2, rest)}, rpe.opts_rt(v1, E.rp_w_eds(v2, rest))) : {FRp.get_req.qplan.f1(_) == Wr.Got{FRp.QPlan{v1, v2}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<List<&2, Rp.Ed>>, FRp.get_eds(E.rp_w_eds(v2, rest)), Wr.Got{v2, rest}, rpe.eds_rt(v2, rest, h2)) : {FRp.get_req.qplan.f2(v1, _) == Wr.Got{FRp.QPlan{v1, v2}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.QBack{+v1, +v2}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(v1)), E.rp_fit_wl(v2), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(v1)), E.rp_fit_wl(v2), hh0)
      +h2 = hh0r
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(v1, E.rp_w_wl(v2, rest))), Wr.Got{v1, E.rp_w_wl(v2, rest)}, Wire.wire_str_round_trip(v1, E.rp_w_wl(v2, rest), h1)) : {FRp.get_req.qback.f1(_) == Wr.Got{FRp.QBack{v1, v2}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<List<&2, Rp.Was>>, FRp.get_wl(E.rp_w_wl(v2, rest)), Wr.Got{v2, rest}, rpe.wl_rt(v2, rest, h2)) : {FRp.get_req.qback.f2(v1, _) == Wr.Got{FRp.QBack{v1, v2}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.QNorm{+v1, +v2, +v3}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), E.rp_fit_ms(v3)), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v1), Bool.and(E.rp_fit_ms(v2), E.rp_fit_ms(v3)), hh0)
      +hh1 = hh0r
      +h2 = LLogicBool.tree.pt.and_l(E.rp_fit_ms(v2), E.rp_fit_ms(v3), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(E.rp_fit_ms(v2), E.rp_fit_ms(v3), hh1)
      +h3 = hh1r
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, rest)))), Wr.Got{v1, E.rp_w_ms(v2, E.rp_w_ms(v3, rest))}, rpe.ms_rt(v1, E.rp_w_ms(v2, E.rp_w_ms(v3, rest)), h1)) : {FRp.get_req.qnorm.f1(_) == Wr.Got{FRp.QNorm{v1, v2, v3}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v2, E.rp_w_ms(v3, rest))), Wr.Got{v2, E.rp_w_ms(v3, rest)}, rpe.ms_rt(v2, E.rp_w_ms(v3, rest), h2)) : {FRp.get_req.qnorm.f2(v1, _) == Wr.Got{FRp.QNorm{v1, v2, v3}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FRp.get_ms(E.rp_w_ms(v3, rest)), Wr.Got{v3, rest}, rpe.ms_rt(v3, rest, h3)) : {FRp.get_req.qnorm.f3(v1, v2, _) == Wr.Got{FRp.QNorm{v1, v2, v3}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.QScan{+v1}:
      +h1 = h
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(v1, rest)), Wr.Got{v1, rest}, Wire.wire_str_round_trip(v1, rest, h1)) : {FRp.get_req.qscan.f1(_) == Wr.Got{FRp.QScan{v1}, rest} : Wr.Dec<FRp.Req>}
      {==}
    case FRp.QFit{+v1, +v2, +v3, +v4}:
      +hh0 = h
      +h1 = LLogicBool.tree.pt.and_l(E.rp_fit_win(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4))), hh0)
      +hh0r = LLogicBool.tree.pt.and_r(E.rp_fit_win(v1), Bool.and(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4))), hh0)
      +hh1 = hh0r
      +h2 = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4)), hh1)
      +hh1r = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(v2), Bool.and(E.rp_fit_search(v3), LawsBase.wire_fits(v4)), hh1)
      +hh2 = hh1r
      +h3 = LLogicBool.tree.pt.and_l(E.rp_fit_search(v3), LawsBase.wire_fits(v4), hh2)
      +hh2r = LLogicBool.tree.pt.and_r(E.rp_fit_search(v3), LawsBase.wire_fits(v4), hh2)
      +h4 = hh2r
      %Equal.sym(Wr.Dec<Rp.Win>, FRp.get_win(E.rp_w_win(v1, Wr.put_nat(v2, E.rp_w_search(v3, Wr.put_nat(v4, rest))))), Wr.Got{v1, Wr.put_nat(v2, E.rp_w_search(v3, Wr.put_nat(v4, rest)))}, rpe.win_rt(v1, Wr.put_nat(v2, E.rp_w_search(v3, Wr.put_nat(v4, rest))), h1)) : {FRp.get_req.qfit.f1(_) == Wr.Got{FRp.QFit{v1, v2, v3, v4}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v2, E.rp_w_search(v3, Wr.put_nat(v4, rest)))), Wr.Got{v2, E.rp_w_search(v3, Wr.put_nat(v4, rest))}, Wire.wire_nat_round_trip(v2, E.rp_w_search(v3, Wr.put_nat(v4, rest)), h2)) : {FRp.get_req.qfit.f2(v1, _) == Wr.Got{FRp.QFit{v1, v2, v3, v4}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Rp.Search>, FRp.get_search(E.rp_w_search(v3, Wr.put_nat(v4, rest))), Wr.Got{v3, Wr.put_nat(v4, rest)}, rpe.search_rt(v3, Wr.put_nat(v4, rest), h3)) : {FRp.get_req.qfit.f3(v1, v2, _) == Wr.Got{FRp.QFit{v1, v2, v3, v4}, rest} : Wr.Dec<FRp.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(v4, rest)), Wr.Got{v4, rest}, Wire.wire_nat_round_trip(v4, rest, h4)) : {FRp.get_req.qfit.f4(v1, v2, v3, _) == Wr.Got{FRp.QFit{v1, v2, v3, v4}, rest} : Wr.Dec<FRp.Req>}
      {==}
