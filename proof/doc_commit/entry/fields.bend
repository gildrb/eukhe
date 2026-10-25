# eukhe: lemmas of the doc_commit entry proofs: the fields of a request
#
# A spelled Pub, Base and Disk reads back (dcw.rd_*), and each decoder of
# bend/ffi_doc_commit.bend answers Got only for the spec's spelling, with
# what it holds within the wire (dcw.pub, dcw.base, dcw.disk).

import Base
import ../../../bend/doc_commit.bend as Cm
import ../../../bend/ffi_doc_commit.bend as FCm
import ../../../bend/wire.bend as Wr
import ../../../laws/doc_commit.bend as DocCommit
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../base.bend as LA
import ../../base/wire_dec.bend as LE
import ../../base/wire_strs.bend as LS

# Read back
# ---------

def dcw.rd_pub(p: Cm.Pub, +rest: String) -> {FCm.get_pub(Wr.get_nat(DocCommit.sp_w_pub(p, rest))) == Wr.Got{p, rest} : Wr.Dec<Cm.Pub>}:
  match p:
    case Cm.Updated{x}:
      match x:
        case Cm.NotPlaced{}:
          {==}
        case Cm.Placed{s}:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case Cm.Deleted{r}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case Cm.Moved{x, r}:
      match x:
        case Cm.NotPlaced{}:
          match r:
            case True{}:
              {==}
            case False{}:
              {==}
        case Cm.Placed{s}:
          match s:
            case True{}:
              match r:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match r:
                case True{}:
                  {==}
                case False{}:
                  {==}

def dcw.rd_pub_back(+p: Cm.Pub, +rest: String) -> {Wr.Got{p, rest} == FCm.get_pub(Wr.get_nat(DocCommit.sp_w_pub(p, rest))) : Wr.Dec<Cm.Pub>}:
  Equal.sym(Wr.Dec<Cm.Pub>, FCm.get_pub(Wr.get_nat(DocCommit.sp_w_pub(p, rest))), Wr.Got{p, rest}, dcw.rd_pub(p, rest))

def dcw.rd_base(b: Cm.Base, +rest: String, h: {DocCommit.sp_fit_base(b) == True{} : Bool}) -> {FCm.get_base(Wr.get_nat(DocCommit.sp_w_base(b, rest))) == Wr.Got{b, rest} : Wr.Dec<Cm.Base>}:
  match b:
    case Cm.OnSeen{+xs}:
      +hh = h
      %LS.dcw.strs.back(xs, rest, LA.dcw.and_l(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), hh), LA.dcw.and_r(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), hh)) : {FCm.get_base.seen(_) == Wr.Got{Cm.OnSeen{xs}, rest} : Wr.Dec<Cm.Base>}
      {==}
    case Cm.OnBytes{}:
      {==}

def dcw.rd_base_back(+b: Cm.Base, +rest: String, h: {DocCommit.sp_fit_base(b) == True{} : Bool}) -> {Wr.Got{b, rest} == FCm.get_base(Wr.get_nat(DocCommit.sp_w_base(b, rest))) : Wr.Dec<Cm.Base>}:
  Equal.sym(Wr.Dec<Cm.Base>, FCm.get_base(Wr.get_nat(DocCommit.sp_w_base(b, rest))), Wr.Got{b, rest}, dcw.rd_base(b, rest, h))

def dcw.rd_disk(d: Cm.Disk, +rest: String, h: {DocCommit.sp_fit_disk(d) == True{} : Bool}) -> {FCm.get_disk(Wr.get_nat(DocCommit.sp_w_disk(d, rest))) == Wr.Got{d, rest} : Wr.Dec<Cm.Disk>}:
  match d:
    case Cm.Absent{}:
      {==}
    case Cm.Present{+g, +e}:
      %LE.dcw.str_back(g, Wr.put_bool(e, rest), h) : {FCm.get_disk.digest(_) == Wr.Got{Cm.Present{g, e}, rest} : Wr.Dec<Cm.Disk>}
      %LE.dcw.bool_back(e, rest) : {FCm.get_disk.expected(g, _) == Wr.Got{Cm.Present{g, e}, rest} : Wr.Dec<Cm.Disk>}
      {==}

def dcw.rd_disk_back(+d: Cm.Disk, +rest: String, h: {DocCommit.sp_fit_disk(d) == True{} : Bool}) -> {Wr.Got{d, rest} == FCm.get_disk(Wr.get_nat(DocCommit.sp_w_disk(d, rest))) : Wr.Dec<Cm.Disk>}:
  Equal.sym(Wr.Dec<Cm.Disk>, FCm.get_disk(Wr.get_nat(DocCommit.sp_w_disk(d, rest))), Wr.Got{d, rest}, dcw.rd_disk(d, rest, h))

# Placed
# ------

def dcw.PlP(s: String, d: Wr.Dec<Cm.Placed>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DocCommit.sp_w_placed(x, r) : String}
    case Wr.Bad{}:
      Unit

def dcw.placed.synced(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dcw.PlP(s, FCm.get_placed.synced(d)):
  match d:
    case Wr.Got{+b, +s2}:
      LE.dcw.after(s, 1n, s1, Wr.put_bool(b, s2), pre, Wire.wire_bool_exact(s1, b, s2, ed))
    case Wr.Bad{}:
      Unit{}

def dcw.placed.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.PlP(s, FCm.get_placed.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      dcw.placed.synced(s, s1, pre, Wr.get_bool(s1), {==})
    case 2n+u:
      Unit{}

def dcw.placed.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.PlP(s, FCm.get_placed(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.placed.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def dcw.placed(+s: String) -> dcw.PlP(s, FCm.get_placed(Wr.get_nat(s))):
  dcw.placed.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# Pub
# ---

def dcw.PbP(s: String, d: Wr.Dec<Cm.Pub>) -> Type:
  match d:
    case Wr.Got{p, r}:
      {s == DocCommit.sp_w_pub(p, r) : String}
    case Wr.Bad{}:
      Unit

def dcw.pub.updated(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Cm.Placed>, pp: dcw.PlP(s1, d)) -> dcw.PbP(s, FCm.get_pub.updated(d)):
  match d:
    case Wr.Got{+x, +r}:
      LE.dcw.after(s, 0n, s1, DocCommit.sp_w_placed(x, r), pre, pp)
    case Wr.Bad{}:
      Unit{}

def dcw.pub.deleted(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dcw.PbP(s, FCm.get_pub.deleted(d)):
  match d:
    case Wr.Got{+b, +r}:
      LE.dcw.after(s, 1n, s1, Wr.put_bool(b, r), pre, Wire.wire_bool_exact(s1, b, r, ed))
    case Wr.Bad{}:
      Unit{}

def dcw.pub.removed(-s: String, +x: Cm.Placed, +s2: String, pre: {s == Wr.put_nat(2n, DocCommit.sp_w_placed(x, s2)) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> dcw.PbP(s, FCm.get_pub.removed(x, d)):
  match d:
    case Wr.Got{+b, +r}:
      Equal.trans(String, s, Wr.put_nat(2n, DocCommit.sp_w_placed(x, s2)), Wr.put_nat(2n, DocCommit.sp_w_placed(x, Wr.put_bool(b, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, DocCommit.sp_w_placed(x, z)), s2, Wr.put_bool(b, r), Wire.wire_bool_exact(s2, b, r, ed)))
    case Wr.Bad{}:
      Unit{}

def dcw.pub.moved(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Cm.Placed>, pp: dcw.PlP(s1, d)) -> dcw.PbP(s, FCm.get_pub.moved(d)):
  match d:
    case Wr.Got{+x, +s2}:
      dcw.pub.removed(s, x, s2, LE.dcw.after(s, 2n, s1, DocCommit.sp_w_placed(x, s2), pre, pp), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dcw.pub.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.PbP(s, FCm.get_pub.tag(t, s1)):
  match t:
    case 0n:
      dcw.pub.updated(s, s1, pre, FCm.get_placed(Wr.get_nat(s1)), dcw.placed(s1))
    case 1n:
      dcw.pub.deleted(s, s1, pre, Wr.get_bool(s1), {==})
    case 2n:
      dcw.pub.moved(s, s1, pre, FCm.get_placed(Wr.get_nat(s1)), dcw.placed(s1))
    case 3n+u:
      Unit{}

def dcw.pub.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.PbP(s, FCm.get_pub(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.pub.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a Pub decoded is spelled
def dcw.pub(+s: String) -> dcw.PbP(s, FCm.get_pub(Wr.get_nat(s))):
  dcw.pub.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# Base
# ----

def dcw.BP(s: String, d: Wr.Dec<Cm.Base>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == DocCommit.sp_w_base(b, r) : String} & {DocCommit.sp_fit_base(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.base.seen(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s1, d)) -> dcw.BP(s, FCm.get_base.seen(d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e, fg) = ls
      (f, g) = fg
      (LE.dcw.after(s, 0n, s1, Wr.put_list(~String, ~Wr.put_str, xs, r), pre, e), LA.dcw.and_tt(LawsBase.wire_fits(List.length(&2, String, xs)), DocCommit.sp_fit_strs(xs), f, g))
    case Wr.Bad{}:
      Unit{}

def dcw.base.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.BP(s, FCm.get_base.tag(t, s1)):
  match t:
    case 0n:
      dcw.base.seen(s, s1, pre, FCm.get_strs(s1), LS.dcw.strs.list(s1))
    case 1n:
      (pre, {==})
    case 2n+u:
      Unit{}

def dcw.base.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.BP(s, FCm.get_base(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.base.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a Base decoded is spelled, and fits
def dcw.base(+s: String) -> dcw.BP(s, FCm.get_base(Wr.get_nat(s))):
  dcw.base.go(s, Wr.get_nat(s), LE.dcw.nat(s))

# Disk
# ----

def dcw.DP(s: String, d: Wr.Dec<Cm.Disk>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == DocCommit.sp_w_disk(x, r) : String} & {DocCommit.sp_fit_disk(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.disk.expected(-s: String, +g: String, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_str(g, s2)) : String}, fg: {LawsBase.wire_fits(String.length(g)) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> dcw.DP(s, FCm.get_disk.expected(g, d)):
  match d:
    case Wr.Got{+e, +s3}:
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_str(g, s2)), Wr.put_nat(1n, Wr.put_str(g, Wr.put_bool(e, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_str(g, z)), s2, Wr.put_bool(e, s3), Wire.wire_bool_exact(s2, e, s3, ed))), fg)
    case Wr.Bad{}:
      Unit{}

def dcw.disk.digest(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> dcw.DP(s, FCm.get_disk.digest(d)):
  match d:
    case Wr.Got{+g, +s2}:
      (e, f) = sp
      dcw.disk.expected(s, g, s2, LE.dcw.after(s, 1n, s1, Wr.put_str(g, s2), pre, e), f, Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def dcw.disk.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.DP(s, FCm.get_disk.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      dcw.disk.digest(s, s1, pre, Wr.get_str(s1), LE.dcw.str(s1))
    case 2n+u:
      Unit{}

def dcw.disk.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.DP(s, FCm.get_disk(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.disk.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a Disk decoded is spelled, and fits
def dcw.disk(+s: String) -> dcw.DP(s, FCm.get_disk(Wr.get_nat(s))):
  dcw.disk.go(s, Wr.get_nat(s), LE.dcw.nat(s))
