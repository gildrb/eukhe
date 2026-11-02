# eukhe: the proof of LAW dmw_ffi_exact
# The entry's decoder reads every input as the laws' reader does, stage by
# stage (dme.*); the resolver answers as the case laws' resolver does, and
# the entry spells the reply as the laws' speller does.

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel

def dme.saved_m(r: Wr.Dec<Nat>) -> {FDm.get_saved.m(r) == DefaultModel.dmr.saved.m(r) : Wr.Dec<Dm.Saved>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dme.saved_tag(t: Nat, +s: String) -> {FDm.get_saved.tag(t, s) == DefaultModel.dmr.saved.tag(t, s) : Wr.Dec<Dm.Saved>}:
  match t:
    case 0n:
      {==}
    case 1n:
      dme.saved_m(Wr.get_nat(s))
    case 2n+p:
      {==}

def dme.saved(r: Wr.Dec<Nat>) -> {FDm.get_saved.go(r) == DefaultModel.dmr.saved(r) : Wr.Dec<Dm.Saved>}:
  match r:
    case Wr.Got{t, +s}:
      dme.saved_tag(t, s)
    case Wr.Bad{}:
      {==}

def dme.next_n(r: Wr.Dec<Nat>) -> {FDm.get_next.n(r) == DefaultModel.dmr.next.n(r) : Wr.Dec<Dm.Next>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dme.next_tag(t: Nat, +s: String) -> {FDm.get_next.tag(t, s) == DefaultModel.dmr.next.tag(t, s) : Wr.Dec<Dm.Next>}:
  match t:
    case 0n:
      {==}
    case 1n:
      dme.next_n(Wr.get_nat(s))
    case 2n+p:
      {==}

def dme.next(r: Wr.Dec<Nat>) -> {FDm.get_next.go(r) == DefaultModel.dmr.next(r) : Wr.Dec<Dm.Next>}:
  match r:
    case Wr.Got{t, +s}:
      dme.next_tag(t, s)
    case Wr.Bad{}:
      {==}

def dme.in_next(sv: Dm.Saved, c: Bool, k: Bool, o: Bool, r: Wr.Dec<Dm.Next>) -> {FDm.get_in.next(sv, c, k, o, r) == DefaultModel.dmr.in.next(sv, c, k, o, r) : Wr.Dec<Dm.In>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dme.in_out(+sv: Dm.Saved, +c: Bool, +k: Bool, r: Wr.Dec<Bool>) -> {FDm.get_in.out(sv, c, k, r) == DefaultModel.dmr.in.out(sv, c, k, r) : Wr.Dec<Dm.In>}:
  match r:
    case Wr.Got{+o, +s}:
      %dme.next(Wr.get_nat(s)) : {FDm.get_in.next(sv, c, k, o, FDm.get_next(s)) == DefaultModel.dmr.in.next(sv, c, k, o, _) : Wr.Dec<Dm.In>}
      dme.in_next(sv, c, k, o, FDm.get_next(s))
    case Wr.Bad{}:
      {==}

def dme.in_key(+sv: Dm.Saved, +c: Bool, r: Wr.Dec<Bool>) -> {FDm.get_in.key(sv, c, r) == DefaultModel.dmr.in.key(sv, c, r) : Wr.Dec<Dm.In>}:
  match r:
    case Wr.Got{k, +s}:
      dme.in_out(sv, c, k, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def dme.in_cat(+sv: Dm.Saved, r: Wr.Dec<Bool>) -> {FDm.get_in.cat(sv, r) == DefaultModel.dmr.in.cat(sv, r) : Wr.Dec<Dm.In>}:
  match r:
    case Wr.Got{c, +s}:
      dme.in_key(sv, c, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def dme.in(r: Wr.Dec<Dm.Saved>) -> {FDm.get_in.go(r) == DefaultModel.dmr.in(r) : Wr.Dec<Dm.In>}:
  match r:
    case Wr.Got{sv, +s}:
      dme.in_cat(sv, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def dme.resolve(x: Dm.In) -> {Dm.resolve(x) == DefaultModel.dms.resolve(x) : Dm.Res}:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      match saved:
        case Dm.NoDefault{}:
          match next:
            case Dm.NoNext{}:
              {==}
            case Dm.Next{n}:
              {==}
        case Dm.Default{m}:
          match cat:
            case False{}:
              match next:
                case Dm.NoNext{}:
                  {==}
                case Dm.Next{n}:
                  {==}
            case True{}:
              match key:
                case False{}:
                  {==}
                case True{}:
                  match out:
                    case True{}:
                      match next:
                        case Dm.NoNext{}:
                          {==}
                        case Dm.Next{n}:
                          {==}
                    case False{}:
                      {==}

def dme.key(k: Dm.Key, -rest: String) -> {FDm.put_key(k, rest) == DefaultModel.dms.key(k, rest) : String}:
  match k:
    case Dm.K{m, r}:
      match r:
        case Dm.NotInCatalog{}:
          {==}
        case Dm.NoCredentials{}:
          {==}
        case Dm.NotInScope{}:
          {==}

def dme.res(x: Dm.Res, +rest: String) -> {FDm.put_res(x, rest) == DefaultModel.dms.res(x, rest) : String}:
  match x:
    case Dm.Runs{p, s}:
      match p:
        case Dm.Saved{}:
          match s:
            case Dm.Kept{}:
              {==}
            case Dm.Swapped{+k}:
              %dme.key(k, rest) : {Wr.put_nat(0n, Wr.put_nat(0n, Wr.put_nat(1n, FDm.put_key(k, rest)))) == Wr.put_nat(0n, Wr.put_nat(0n, Wr.put_nat(1n, _))) : String}
              {==}
        case Dm.Other{n}:
          match s:
            case Dm.Kept{}:
              {==}
            case Dm.Swapped{+k}:
              %dme.key(k, rest) : {Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(n, Wr.put_nat(1n, FDm.put_key(k, rest))))) == Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(n, Wr.put_nat(1n, _)))) : String}
              {==}
    case Dm.Nothing{}:
      {==}
    case Dm.Refused{+k}:
      %dme.key(k, rest) : {Wr.put_nat(2n, FDm.put_key(k, rest)) == Wr.put_nat(2n, _) : String}
      {==}

def dme.end(b: Bool, +x: Dm.In) -> {FDm.ffi.end(b, x) == DefaultModel.dms.end(b, x) : String}:
  match b:
    case True{}:
      %dme.resolve(x) : {FDm.put_res(Dm.resolve(x), "") == DefaultModel.dms.res(_, "") : String}
      dme.res(Dm.resolve(x), "")
    case False{}:
      {==}

def dme.go(r: Wr.Dec<Dm.In>) -> {FDm.ffi.go(r) == DefaultModel.dms.go(r) : String}:
  match r:
    case Wr.Got{x, +s}:
      dme.end(Wr.end(s), x)
    case Wr.Bad{}:
      {==}

def DefaultModel.dmw_ffi_exact(s):
  %dme.saved(Wr.get_nat(s)) : {FDm.ffi.go(FDm.get_in(s)) == DefaultModel.dms.go(DefaultModel.dmr.in(_)) : String}
  %dme.in(FDm.get_saved(s)) : {FDm.ffi.go(FDm.get_in(s)) == DefaultModel.dms.go(_) : String}
  dme.go(FDm.get_in(s))
