# eukhe: the proof of LAW doc_seen_ffi_exact
# The entry reads every input as the spec's reader does (each item reader
# is the spec's, so each list reader is) and answers the spec's verdict
# (the model's unseen anchors, lines, shown lines and whole flag are the
# spec's), spelled as the spec spells it.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/doc_seen.bend as DocSeen
import ./base.bend as LA
import ./reject_shows_lines.bend as PRejectShowsLines

# The item readers
# ----------------

def dx.mnat_some(r: Wr.Dec<Nat>) -> {Fds.get_mnat.some(r) == DocSeen.seen.sp_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dx.mnat_tag(r: Wr.Dec<Nat>) -> {Fds.get_mnat.tag(r) == DocSeen.seen.sp_mnat.tag(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          dx.mnat_some(Wr.get_nat(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def dx.mnat(s: String) -> {Fds.get_mnat(s) == DocSeen.seen.sp_mnat(s) : Wr.Dec<Maybe<&2, Nat>>}:
  dx.mnat_tag(Wr.get_nat(s))

def dx.iv_hi(lo: Nat, r: Wr.Dec<Nat>) -> {Fds.get_iv.hi(lo, r) == DocSeen.seen.sp_iv.hi(lo, r) : Wr.Dec<Ds.Iv>}:
  match r:
    case Wr.Got{hi, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dx.iv_lo(r: Wr.Dec<Nat>) -> {Fds.get_iv.lo(r) == DocSeen.seen.sp_iv.lo(r) : Wr.Dec<Ds.Iv>}:
  match r:
    case Wr.Got{lo, s}:
      dx.iv_hi(lo, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def dx.iv(s: String) -> {Fds.get_iv(s) == DocSeen.seen.sp_iv(s) : Wr.Dec<Ds.Iv>}:
  dx.iv_lo(Wr.get_nat(s))

def dx.at_w(n: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {Fds.get_at.w(n, r) == DocSeen.seen.sp_at.w(n, r) : Wr.Dec<Ds.At>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def dx.at_n(r: Wr.Dec<Nat>) -> {Fds.get_at.n(r) == DocSeen.seen.sp_at.n(r) : Wr.Dec<Ds.At>}:
  match r:
    case Wr.Got{+n, +s}:
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Fds.get_mnat(s), DocSeen.seen.sp_mnat(s), dx.mnat(s)) : {Fds.get_at.w(n, _) == DocSeen.seen.sp_at.n(Wr.Got{n, s}) : Wr.Dec<Ds.At>}
      dx.at_w(n, DocSeen.seen.sp_mnat(s))
    case Wr.Bad{}:
      {==}

def dx.at(s: String) -> {Fds.get_at(s) == DocSeen.seen.sp_at(s) : Wr.Dec<Ds.At>}:
  dx.at_n(Wr.get_nat(s))

# The list readers
# ----------------

def dx.ivs_go(n: Nat, cur: Wr.Dec<Ds.Iv>) -> {Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, n, cur) == Wr.get_list.go(~Ds.Iv, ~DocSeen.seen.sp_iv, n, cur) : Wr.Dec<List<&2, Ds.Iv>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Ds.Iv>, Fds.get_iv(r), DocSeen.seen.sp_iv(r), dx.iv(r)) : {Wr.get_list.cons(Ds.Iv, x, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, k, _)) == Wr.get_list.cons(Ds.Iv, x, Wr.get_list.go(~Ds.Iv, ~DocSeen.seen.sp_iv, k, DocSeen.seen.sp_iv(r))) : Wr.Dec<List<&2, Ds.Iv>>}
      %Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, k, DocSeen.seen.sp_iv(r)), Wr.get_list.go(~Ds.Iv, ~DocSeen.seen.sp_iv, k, DocSeen.seen.sp_iv(r)), dx.ivs_go(k, DocSeen.seen.sp_iv(r))) : {Wr.get_list.cons(Ds.Iv, x, _) == Wr.get_list.cons(Ds.Iv, x, Wr.get_list.go(~Ds.Iv, ~DocSeen.seen.sp_iv, k, DocSeen.seen.sp_iv(r))) : Wr.Dec<List<&2, Ds.Iv>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def dx.ivs_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, d) == Wr.get_list.start(~Ds.Iv, ~DocSeen.seen.sp_iv, d) : Wr.Dec<List<&2, Ds.Iv>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Ds.Iv>, Fds.get_iv(s), DocSeen.seen.sp_iv(s), dx.iv(s)) : {Wr.get_list.go(~Ds.Iv, ~Fds.get_iv, m, _) == Wr.get_list.go(~Ds.Iv, ~DocSeen.seen.sp_iv, m, DocSeen.seen.sp_iv(s)) : Wr.Dec<List<&2, Ds.Iv>>}
          dx.ivs_go(m, DocSeen.seen.sp_iv(s))
    case Wr.Bad{}:
      {==}

def dx.ats_go(n: Nat, cur: Wr.Dec<Ds.At>) -> {Wr.get_list.go(~Ds.At, ~Fds.get_at, n, cur) == Wr.get_list.go(~Ds.At, ~DocSeen.seen.sp_at, n, cur) : Wr.Dec<List<&2, Ds.At>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Ds.At>, Fds.get_at(r), DocSeen.seen.sp_at(r), dx.at(r)) : {Wr.get_list.cons(Ds.At, x, Wr.get_list.go(~Ds.At, ~Fds.get_at, k, _)) == Wr.get_list.cons(Ds.At, x, Wr.get_list.go(~Ds.At, ~DocSeen.seen.sp_at, k, DocSeen.seen.sp_at(r))) : Wr.Dec<List<&2, Ds.At>>}
      %Equal.sym(Wr.Dec<List<&2, Ds.At>>, Wr.get_list.go(~Ds.At, ~Fds.get_at, k, DocSeen.seen.sp_at(r)), Wr.get_list.go(~Ds.At, ~DocSeen.seen.sp_at, k, DocSeen.seen.sp_at(r)), dx.ats_go(k, DocSeen.seen.sp_at(r))) : {Wr.get_list.cons(Ds.At, x, _) == Wr.get_list.cons(Ds.At, x, Wr.get_list.go(~Ds.At, ~DocSeen.seen.sp_at, k, DocSeen.seen.sp_at(r))) : Wr.Dec<List<&2, Ds.At>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def dx.ats_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Ds.At, ~Fds.get_at, d) == Wr.get_list.start(~Ds.At, ~DocSeen.seen.sp_at, d) : Wr.Dec<List<&2, Ds.At>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Ds.At>, Fds.get_at(s), DocSeen.seen.sp_at(s), dx.at(s)) : {Wr.get_list.go(~Ds.At, ~Fds.get_at, m, _) == Wr.get_list.go(~Ds.At, ~DocSeen.seen.sp_at, m, DocSeen.seen.sp_at(s)) : Wr.Dec<List<&2, Ds.At>>}
          dx.ats_go(m, DocSeen.seen.sp_at(s))
    case Wr.Bad{}:
      {==}

# The verdict
# -----------

def dx.unseen(+seen: List<&2, Ds.Iv>, ats: List<&2, Ds.At>) -> {DocSeen.seen.Unseen(seen, ats) == DocSeen.seen.sp_unseen(seen, ats) : List<&2, Ds.At>}:
  match ats:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{+n, +w}:
          %Equal.sym(List<&2, Ds.At>, DocSeen.seen.Unseen(seen, rest), DocSeen.seen.sp_unseen(seen, rest), dx.unseen(seen, rest)) : {DocSeen.seen.Unseen.keep(Ds.At{n, w}, _, DocSeen.seen.In(n, seen)) == DocSeen.seen.sp_unseen(seen, Ds.At{n, w} <> rest) : List<&2, Ds.At>}
          {==}

def dx.lines(us: List<&2, Ds.At>) -> {Ds.lines(us) == DocSeen.seen.sp_lines(us) : List<&2, Nat>}:
  match us:
    case Nil{}:
      {==}
    case a <> +rest:
      match a:
        case Ds.At{n, w}:
          %Equal.sym(List<&2, Nat>, Ds.lines(rest), DocSeen.seen.sp_lines(rest), dx.lines(rest)) : {n <> _ == n <> DocSeen.seen.sp_lines(rest) : List<&2, Nat>}
          {==}

def dx.show(x: Ds.Show, -rest: String) -> {Fds.put_show(x, rest) == DocSeen.seen.sp_put_show(x, rest) : String}:
  match x:
    case Ds.Show{n, c}:
      match c:
        case None{}:
          {==}
        case Some{k}:
          {==}

def dx.shows_go(xs: List<&2, Ds.Show>, -rest: String) -> {Wr.put_list.go(~Ds.Show, ~Fds.put_show, xs, rest) == (List.length(&2, Ds.Show, xs), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Show, ~Fds.put_show, t, rest), (List.length(&2, Ds.Show, t), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest)), dx.shows_go(t, rest)) : {Wr.put_list.step(~Ds.Show, ~Fds.put_show, x, _) == (1n+List.length(&2, Ds.Show, t), DocSeen.seen.sp_put_show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest))) : Nat & String}
      %Equal.sym(String, Fds.put_show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest)), DocSeen.seen.sp_put_show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest)), dx.show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest))) : {(1n+List.length(&2, Ds.Show, t), _) == (1n+List.length(&2, Ds.Show, t), DocSeen.seen.sp_put_show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest))) : Nat & String}
      {==}

def dx.shows_go_sp(xs: List<&2, Ds.Show>, -rest: String) -> {Wr.put_list.go(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest) == (List.length(&2, Ds.Show, xs), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest), (List.length(&2, Ds.Show, t), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest)), dx.shows_go_sp(t, rest)) : {Wr.put_list.step(~Ds.Show, ~DocSeen.seen.sp_put_show, x, _) == (1n+List.length(&2, Ds.Show, t), DocSeen.seen.sp_put_show(x, LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, t, rest))) : Nat & String}
      {==}

def dx.shows(+xs: List<&2, Ds.Show>, +rest: String) -> {Wr.put_list(~Ds.Show, ~Fds.put_show, xs, rest) == Wr.put_list(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Show, ~Fds.put_show, xs, rest), (List.length(&2, Ds.Show, xs), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest)), dx.shows_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest), (List.length(&2, Ds.Show, xs), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest)), dx.shows_go_sp(xs, rest)) : {Wr.put_list.fin((List.length(&2, Ds.Show, xs), LawsBase.wire_put_items(~Ds.Show, ~DocSeen.seen.sp_put_show, xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

def dx.verdict(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>) -> {Fds.put_check(Ds.check(seen, ats), "") == DocSeen.seen.sp_verdict(DocSeen.seen.sp_unseen(seen, ats)) : String}:
  +u = DocSeen.seen.sp_unseen(seen, ats)
  %Equal.sym(List<&2, Ds.At>, Ds.unseen(seen, ats), DocSeen.seen.Unseen(seen, ats), LA.pv.unseen_eq(seen, ats)) : {Fds.put_check(Ds.check.go(_), "") == DocSeen.seen.sp_verdict(u) : String}
  %Equal.sym(List<&2, Ds.At>, DocSeen.seen.Unseen(seen, ats), u, dx.unseen(seen, ats)) : {Fds.put_check(Ds.check.go(_), "") == DocSeen.seen.sp_verdict(u) : String}
  %Equal.sym(List<&2, Nat>, Ds.lines(u), DocSeen.seen.sp_lines(u), dx.lines(u)) : {Wr.put_list(~Nat, ~Wr.put_nat, _, Wr.put_list(~Ds.Show, ~Fds.put_show, Ds.shows(List.take(&2, Ds.At, u, Ds.cap)), Wr.put_bool(Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u), ""))) == DocSeen.seen.sp_verdict(u) : String}
  %Equal.sym(List<&2, Ds.Show>, Ds.shows(List.take(&2, Ds.At, u, Ds.cap)), DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)), PRejectShowsLines.pv.shows_eq(List.take(&2, Ds.At, u, Ds.cap))) : {Wr.put_list(~Nat, ~Wr.put_nat, DocSeen.seen.sp_lines(u), Wr.put_list(~Ds.Show, ~Fds.put_show, _, Wr.put_bool(Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u), ""))) == DocSeen.seen.sp_verdict(u) : String}
  %Equal.sym(Bool, Ds.whole.go(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u), Bool.and(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), DocSeen.seen.Fits(u)), LA.pv.whole_eq(Nat.is_le(List.length(&2, Ds.At, u), Ds.cap), u)) : {Wr.put_list(~Nat, ~Wr.put_nat, DocSeen.seen.sp_lines(u), Wr.put_list(~Ds.Show, ~Fds.put_show, DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)), Wr.put_bool(_, ""))) == DocSeen.seen.sp_verdict(u) : String}
  %Equal.sym(String, Wr.put_list(~Ds.Show, ~Fds.put_show, DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)), Wr.put_bool(DocSeen.seen.Whole(u), "")), Wr.put_list(~Ds.Show, ~DocSeen.seen.sp_put_show, DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)), Wr.put_bool(DocSeen.seen.Whole(u), "")), dx.shows(DocSeen.seen.Shown(List.take(&2, Ds.At, u, Ds.cap)), Wr.put_bool(DocSeen.seen.Whole(u), ""))) : {Wr.put_list(~Nat, ~Wr.put_nat, DocSeen.seen.sp_lines(u), _) == DocSeen.seen.sp_verdict(u) : String}
  {==}

# The entry
# ---------

def dx.done(+seen: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, b: Bool) -> {Fds.run.done(seen, ats, b) == DocSeen.seen.sp_done(seen, ats, b) : String}:
  match b:
    case True{}:
      dx.verdict(seen, ats)
    case False{}:
      {==}

def dx.ats(+seen: List<&2, Ds.Iv>, r: Wr.Dec<List<&2, Ds.At>>) -> {Fds.run.ats(seen, r) == DocSeen.seen.sp_ats(seen, r) : String}:
  match r:
    case Wr.Got{ats, s}:
      dx.done(seen, ats, Wr.end(s))
    case Wr.Bad{}:
      {==}

def dx.seen(r: Wr.Dec<List<&2, Ds.Iv>>) -> {Fds.run.seen(r) == DocSeen.seen.sp_seen(r) : String}:
  match r:
    case Wr.Got{+seen, +s}:
      %Equal.sym(Wr.Dec<List<&2, Ds.At>>, Wr.get_list.start(~Ds.At, ~Fds.get_at, Wr.get_nat(s)), Wr.get_list.start(~Ds.At, ~DocSeen.seen.sp_at, Wr.get_nat(s)), dx.ats_start(Wr.get_nat(s))) : {Fds.run.ats(seen, _) == DocSeen.seen.sp_seen(Wr.Got{seen, s}) : String}
      dx.ats(seen, Wr.get_list(~Ds.At, ~DocSeen.seen.sp_at, s))
    case Wr.Bad{}:
      {==}

def DocSeen.doc_seen_ffi_exact(s):
  %Equal.sym(Wr.Dec<List<&2, Ds.Iv>>, Wr.get_list.start(~Ds.Iv, ~Fds.get_iv, Wr.get_nat(s)), Wr.get_list.start(~Ds.Iv, ~DocSeen.seen.sp_iv, Wr.get_nat(s)), dx.ivs_start(Wr.get_nat(s))) : {Fds.run.seen(_) == DocSeen.seen.sp_entry(s) : String}
  dx.seen(Wr.get_list(~Ds.Iv, ~DocSeen.seen.sp_iv, s))
