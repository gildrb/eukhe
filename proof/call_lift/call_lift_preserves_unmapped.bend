# eukhe: the proof of LAW call_lift_preserves_unmapped
#
# PROOF: the lift is the spec's (call_lift_refines_spec); an unknown, current or stranded lift keeps every index and adds nothing; a lifted call starts from the stored arguments (kept indices upto(ks, 0n), nothing added, no receipt) and every op keeps the invariant (clm.pu.inv): a move renames in place (kept indices and added count unchanged), a clash and a rename add a receipt that is no fill, a fill appends one added argument (no kept index) and one filled receipt.

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift
import ./call_lift_refines_spec.bend as PCallLiftRefinesSpec

# Appending
# ---------

def clm.pu.ki_add(args: List<&2, Cl.Arg>, -k: String, -j: String) -> {Sp.kept_indices(args) == Sp.kept_indices(List.append(&2, Cl.Arg, args, [Cl.Added{k, j}])) : List<&2, Nat>}:
  match args:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, kk}:
          %clm.pu.ki_add(rest, k, j) : {Con{i, Sp.kept_indices(rest)} == Con{i, _} : List<&2, Nat>}
          {==}
        case Cl.Added{kk, jj}:
          clm.pu.ki_add(rest, k, j)

def clm.pu.ac_add(args: List<&2, Cl.Arg>, -k: String, -j: String) -> {1n+Sp.added_count(args) == Sp.added_count(List.append(&2, Cl.Arg, args, [Cl.Added{k, j}])) : Nat}:
  match args:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Cl.Kept{i, kk}:
          clm.pu.ac_add(rest, k, j)
        case Cl.Added{kk, jj}:
          %clm.pu.ac_add(rest, k, j) : {1n+1n+Sp.added_count(rest) == 1n+_ : Nat}
          {==}

def clm.pu.fc_fil(rs: List<&2, Cl.Receipt>, -k: String) -> {1n+Sp.filled_count(rs) == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Filled{k}])) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Cl.Renamed{a, b}:
          clm.pu.fc_fil(rest, k)
        case Cl.Clashed{a, b}:
          clm.pu.fc_fil(rest, k)
        case Cl.Filled{kk}:
          %clm.pu.fc_fil(rest, k) : {1n+1n+Sp.filled_count(rest) == 1n+_ : Nat}
          {==}

def clm.pu.fc_ren(rs: List<&2, Cl.Receipt>, -a: String, -b: String) -> {Sp.filled_count(rs) == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Renamed{a, b}])) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Cl.Renamed{p, q}:
          clm.pu.fc_ren(rest, a, b)
        case Cl.Clashed{p, q}:
          clm.pu.fc_ren(rest, a, b)
        case Cl.Filled{kk}:
          %clm.pu.fc_ren(rest, a, b) : {1n+Sp.filled_count(rest) == 1n+_ : Nat}
          {==}

def clm.pu.fc_cla(rs: List<&2, Cl.Receipt>, -a: String, -b: String) -> {Sp.filled_count(rs) == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Clashed{a, b}])) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Cl.Renamed{p, q}:
          clm.pu.fc_cla(rest, a, b)
        case Cl.Clashed{p, q}:
          clm.pu.fc_cla(rest, a, b)
        case Cl.Filled{kk}:
          %clm.pu.fc_cla(rest, a, b) : {1n+Sp.filled_count(rest) == 1n+_ : Nat}
          {==}

# Moving
# ------

def clm.pu.ki_move_at(hit: Bool, a: Cl.Arg, -rest: List<&2, Cl.Arg>, -mv: List<&2, Cl.Arg>, -to: String, ih: {Sp.kept_indices(rest) == Sp.kept_indices(mv) : List<&2, Nat>}) -> {Sp.kept_indices(Con{a, rest}) == Sp.kept_indices(Sp.move.at(hit, a, rest, mv, to)) : List<&2, Nat>}:
  match hit:
    case True{}:
      match a:
        case Cl.Kept{i, k}:
          {==}
        case Cl.Added{k, j}:
          {==}
    case False{}:
      match a:
        case Cl.Kept{i, k}:
          %ih : {Con{i, Sp.kept_indices(rest)} == Con{i, _} : List<&2, Nat>}
          {==}
        case Cl.Added{k, j}:
          ih

def clm.pu.ki_move(args: List<&2, Cl.Arg>, +from: String, +to: String) -> {Sp.kept_indices(args) == Sp.kept_indices(Sp.move(args, from, to)) : List<&2, Nat>}:
  match args:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      clm.pu.ki_move_at(String.eq(Sp.key_of(a), from), a, rest, Sp.move(rest, from, to), to, clm.pu.ki_move(rest, from, to))

def clm.pu.ac_move_at(hit: Bool, a: Cl.Arg, -rest: List<&2, Cl.Arg>, -mv: List<&2, Cl.Arg>, -to: String, ih: {Sp.added_count(rest) == Sp.added_count(mv) : Nat}) -> {Sp.added_count(Con{a, rest}) == Sp.added_count(Sp.move.at(hit, a, rest, mv, to)) : Nat}:
  match hit:
    case True{}:
      match a:
        case Cl.Kept{i, k}:
          {==}
        case Cl.Added{k, j}:
          {==}
    case False{}:
      match a:
        case Cl.Kept{i, k}:
          ih
        case Cl.Added{k, j}:
          %ih : {1n+Sp.added_count(rest) == 1n+_ : Nat}
          {==}

def clm.pu.ac_move(args: List<&2, Cl.Arg>, +from: String, +to: String) -> {Sp.added_count(args) == Sp.added_count(Sp.move(args, from, to)) : Nat}:
  match args:
    case Nil{}:
      {==}
    case Con{+a, +rest}:
      clm.pu.ac_move_at(String.eq(Sp.key_of(a), from), a, rest, Sp.move(rest, from, to), to, clm.pu.ac_move(rest, from, to))

# The invariant
# -------------

# the kept indices are those stored, and every added argument is filled
def clm.pu.inv(ks: List<&2, String>, st: Cl.St) -> Type:
  match st:
    case Cl.St{+a, rs}:
      {Sp.kept_indices(a) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_count(a) == Sp.filled_count(rs) : Nat}

def clm.pu.ren_inv(present: Bool, taken: Bool, +from: String, +to: String, +args: List<&2, Cl.Arg>, +rs: List<&2, Cl.Receipt>, -ks: List<&2, String>, h: clm.pu.inv(ks, Cl.St{args, rs})) -> clm.pu.inv(ks, Sp.op_rename(present, taken, from, to, args, rs)):
  match present:
    case False{}:
      h
    case True{}:
      match taken:
        case True{}:
          %clm.pu.fc_cla(rs, from, to) : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_count(args) == _ : Nat}
          h
        case False{}:
          %clm.pu.ki_move(args, from, to) : {_ == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_count(Sp.move(args, from, to)) == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])) : Nat}
          %clm.pu.ac_move(args, from, to) : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {_ == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])) : Nat}
          %clm.pu.fc_ren(rs, from, to) : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_count(args) == _ : Nat}
          h

def clm.pu.fill_pair(-args: List<&2, Cl.Arg>, -rs: List<&2, Cl.Receipt>, -ks: List<&2, String>, h: clm.pu.inv(ks, Cl.St{args, rs})) -> {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {1n+Sp.added_count(args) == 1n+Sp.filled_count(rs) : Nat}:
  (h1, h2) = h
  %h2 : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {1n+Sp.added_count(args) == 1n+_ : Nat}
  (h1, {==})

def clm.pu.fill_inv(present: Bool, +key: String, +json: String, +args: List<&2, Cl.Arg>, +rs: List<&2, Cl.Receipt>, -ks: List<&2, String>, h: clm.pu.inv(ks, Cl.St{args, rs})) -> clm.pu.inv(ks, Sp.op_fill(present, key, json, args, rs)):
  match present:
    case True{}:
      h
    case False{}:
      %clm.pu.ki_add(args, key, json) : {_ == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_count(List.append(&2, Cl.Arg, args, [Cl.Added{key, json}])) == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])) : Nat}
      %clm.pu.ac_add(args, key, json) : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {_ == Sp.filled_count(List.append(&2, Cl.Receipt, rs, [Cl.Filled{key}])) : Nat}
      %clm.pu.fc_fil(rs, key) : {Sp.kept_indices(args) == Sp.upto(ks, 0n) : List<&2, Nat>} & {1n+Sp.added_count(args) == _ : Nat}
      clm.pu.fill_pair(args, rs, ks, h)

def clm.pu.op_inv(o: Cl.Op, st: Cl.St, -ks: List<&2, String>) -> clm.pu.inv(ks, st) -> clm.pu.inv(ks, Sp.op(o, st)):
  match o:
    case Cl.Rename{+from, +to}:
      match st:
        case Cl.St{+args, +rs}:
          h => clm.pu.ren_inv(Sp.taken(args, from), Sp.taken(args, to), from, to, args, rs, ks, h)
    case Cl.Fill{+key, +json}:
      match st:
        case Cl.St{+args, +rs}:
          h => clm.pu.fill_inv(Sp.taken(args, key), key, json, args, rs, ks, h)

def clm.pu.ops_inv(os: List<&2, Cl.Op>, +st: Cl.St, -ks: List<&2, String>) -> clm.pu.inv(ks, st) -> clm.pu.inv(ks, Sp.ops(os, st)):
  match os:
    case Nil{}:
      h => h
    case Con{+o, rest}:
      h => clm.pu.ops_inv(rest, Sp.op(o, st), ks)(clm.pu.op_inv(o, st, ks)(h))

def clm.pu.ki_stored(ks: List<&2, String>, +i: Nat) -> {Sp.kept_indices(Sp.stored(ks, i)) == Sp.upto(ks, i) : List<&2, Nat>}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, rest}:
      %clm.pu.ki_stored(rest, 1n+i) : {Con{i, Sp.kept_indices(Sp.stored(rest, 1n+i))} == Con{i, _} : List<&2, Nat>}
      {==}

def clm.pu.ac_stored(ks: List<&2, String>, +i: Nat) -> {Sp.added_count(Sp.stored(ks, i)) == 0n : Nat}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, rest}:
      clm.pu.ac_stored(rest, 1n+i)

# The lift
# --------

def clm.pu.pres(+ks: List<&2, String>, +l: Cl.Lift) -> Type:
  {Sp.kept_of(ks, l) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_of(l) == Sp.filled_of(l) : Nat}

def clm.pu.done(-cur: String, -ks: List<&2, String>, st: Cl.St) -> clm.pu.inv(ks, st) -> clm.pu.pres(ks, Sp.lift_spec.done(cur, st)):
  match st:
    case Cl.St{a, rs}:
      h => h

def clm.pu.at(at: Bool, +cur: String, +ks: List<&2, String>, p: Maybe<&2, List<&2, Cl.Step>>) -> clm.pu.pres(ks, Sp.lift_spec.at(at, cur, ks, p)):
  match at:
    case True{}:
      ({==}, {==})
    case False{}:
      match p:
        case None{}:
          ({==}, {==})
        case Some{+path}:
          clm.pu.done(cur, ks, Sp.ops(Sp.ops_of(path), Cl.St{Sp.stored(ks, 0n), []}))(clm.pu.ops_inv(Sp.ops_of(path), Cl.St{Sp.stored(ks, 0n), []}, ks)((clm.pu.ki_stored(ks, 0n), clm.pu.ac_stored(ks, 0n))))

def clm.pu.cur(+r: String, +ks: List<&2, String>, m: Maybe<&2, String>, +ss: List<&2, Cl.Step>) -> clm.pu.pres(ks, Sp.lift_spec.cur(r, ks, m, ss)):
  match m:
    case None{}:
      ({==}, {==})
    case Some{+cur}:
      clm.pu.at(String.eq(r, cur), cur, ks, Sp.chain(List.length(&2, Cl.Step, ss), ss, cur, Sp.next(ss, r)))

def CallLift.call_lift_preserves_unmapped(t, f, r, ks):
  %Equal.sym(Cl.Lift, Cl.lift(t, Cl.Call{f, r, ks}), Sp.lift_spec(t, Cl.Call{f, r, ks}), CallLift.call_lift_refines_spec(t, Cl.Call{f, r, ks})) : {Sp.kept_of(ks, _) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_of(_) == Sp.filled_of(_) : Nat}
  clm.pu.cur(r, ks, Sp.current(t, f), Sp.steps_of(t, f))
