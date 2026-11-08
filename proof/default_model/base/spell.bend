# eukhe: the grammar's spelling of the default_model entry (laws
# dmw_spell_*) is the entry's own encoding, field by field

import Base
import ../../../bend/default_model.bend as Dm
import ../../../bend/ffi_default_model.bend as FDm
import ../../../bend/wire.bend as Wr
import ../../../laws/default_model.bend as DefaultModel

# a saved default
def dms.saved(x: Dm.Saved, rest: String) -> {FDm.put_saved(x, rest) == DefaultModel.dmw_spell_saved(x, rest) : String}:
  match x:
    case Dm.NoDefault{}:
      {==}
    case Dm.Default{m}:
      {==}

# a request
def dms.req.at(saved: Dm.Saved, next: Dm.Next, cat: Bool, key: Bool, out: Bool, rest: String) -> {FDm.put_in(Dm.In{saved, cat, key, out, next}, rest) == DefaultModel.dmw_spell_req(Dm.In{saved, cat, key, out, next}, rest) : String}:
  match saved:
    case Dm.NoDefault{}:
      match next:
        case Dm.NoNext{}:
          {==}
        case Dm.Next{n}:
          {==}
    case Dm.Default{m}:
      match next:
        case Dm.NoNext{}:
          {==}
        case Dm.Next{n}:
          {==}

def dms.req(x: Dm.In, rest: String) -> {FDm.put_in(x, rest) == DefaultModel.dmw_spell_req(x, rest) : String}:
  match x:
    case Dm.In{saved, cat, key, out, next}:
      dms.req.at(saved, next, cat, key, out, rest)

# a reason
def dms.reason(r: Dm.Reason, rest: String) -> {FDm.put_reason(r, rest) == DefaultModel.dmw_spell_reason(r, rest) : String}:
  match r:
    case Dm.NotInCatalog{}:
      {==}
    case Dm.NoCredentials{}:
      {==}
    case Dm.NotInScope{}:
      {==}

# a key
def dms.key(k: Dm.Key, +rest: String) -> {FDm.put_key(k, rest) == DefaultModel.dmw_spell_key(k, rest) : String}:
  match k:
    case Dm.K{+m, +r}:
      Equal.cong(String, String, z => Wr.put_nat(m, z), FDm.put_reason(r, rest), DefaultModel.dmw_spell_reason(r, rest), dms.reason(r, rest))

# a pick
def dms.pick(p: Dm.Pick, rest: String) -> {FDm.put_pick(p, rest) == DefaultModel.dmw_spell_pick(p, rest) : String}:
  match p:
    case Dm.Saved{}:
      {==}
    case Dm.Other{n}:
      {==}

# a substitution
def dms.sub(s: Dm.Sub, +rest: String) -> {FDm.put_sub(s, rest) == DefaultModel.dmw_spell_sub(s, rest) : String}:
  match s:
    case Dm.Kept{}:
      {==}
    case Dm.Swapped{+k}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FDm.put_key(k, rest), DefaultModel.dmw_spell_key(k, rest), dms.key(k, rest))

# a reply
def dms.res(r: Dm.Res, +rest: String) -> {FDm.put_res(r, rest) == DefaultModel.dmw_spell_res(r, rest) : String}:
  match r:
    case Dm.Runs{+p, +s}:
      %dms.sub(s, rest) : {Wr.put_nat(0n, FDm.put_pick(p, FDm.put_sub(s, rest))) == Wr.put_nat(0n, DefaultModel.dmw_spell_pick(p, _)) : String}
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FDm.put_pick(p, FDm.put_sub(s, rest)), DefaultModel.dmw_spell_pick(p, FDm.put_sub(s, rest)), dms.pick(p, FDm.put_sub(s, rest)))
    case Dm.Nothing{}:
      {==}
    case Dm.Refused{+k}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FDm.put_key(k, rest), DefaultModel.dmw_spell_key(k, rest), dms.key(k, rest))
