# eukhe: lemmas the proofs of area kernel_local share: the entry's reader
# answers what the laws' reader answers on every input (one lemma per
# stage, each a case split on the stage's input), the entry reads back
# what the laws' spellers write, and its reply writers write what the
# laws' spellers write.

import Base
import ../../bend/ffi_kernel_local.bend as FKL
import ../../bend/kernel_local.bend as KL
import ../../bend/wire.bend as Wr
import ../../laws/kernel_local.bend as KernelLocal

# Logic
# -----

def kl.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def kl.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : kl.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def kl.found_tag(t: Nat, s: String) -> {KernelLocal.read_found.tag(t, s) == FKL.get_found.tag(t, s) : Wr.Dec<KL.Found>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def kl.found(r: Wr.Dec<Nat>) -> {KernelLocal.read_found(r) == FKL.get_found.go(r) : Wr.Dec<KL.Found>}:
  match r:
    case Wr.Got{t, s}:
      kl.found_tag(t, s)
    case Wr.Bad{}:
      {==}

def kl.setup_tag(t: Nat, s: String) -> {KernelLocal.read_setup.tag(t, s) == FKL.get_setup.tag(t, s) : Wr.Dec<KL.Setup>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def kl.setup(r: Wr.Dec<Nat>) -> {KernelLocal.read_setup(r) == FKL.get_setup.go(r) : Wr.Dec<KL.Setup>}:
  match r:
    case Wr.Got{t, s}:
      kl.setup_tag(t, s)
    case Wr.Bad{}:
      {==}

def kl.plan_setup(f: KL.Found, r: Wr.Dec<KL.Setup>) -> {KernelLocal.read_plan.setup(f, r) == FKL.get_plan.setup(f, r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.plan(r: Wr.Dec<KL.Found>) -> {KernelLocal.read_plan(r) == FKL.get_plan.found(r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{+f, +s}:
      %kl.setup(Wr.get_nat(s)) : {KernelLocal.read_plan.setup(f, KernelLocal.read_setup(Wr.get_nat(s))) == FKL.get_plan.setup(f, _) : Wr.Dec<KL.Ask>}
      %kl.plan_setup(f, KernelLocal.read_setup(Wr.get_nat(s))) : {KernelLocal.read_plan.setup(f, KernelLocal.read_setup(Wr.get_nat(s))) == _ : Wr.Dec<KL.Ask>}
      {==}
    case Wr.Bad{}:
      {==}

def kl.kind_tag(t: Nat, s: String) -> {KernelLocal.read_kind.tag(t, s) == FKL.get_kind.tag(t, s) : Wr.Dec<KL.FileKind>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def kl.kind(r: Wr.Dec<Nat>) -> {KernelLocal.read_kind(r) == FKL.get_kind.go(r) : Wr.Dec<KL.FileKind>}:
  match r:
    case Wr.Got{t, s}:
      kl.kind_tag(t, s)
    case Wr.Bad{}:
      {==}

def kl.left_owner(k: KL.FileKind, r: Wr.Dec<Bool>) -> {KernelLocal.read_left.owner(k, r) == FKL.get_left.owner(k, r) : Wr.Dec<KL.Left>}:
  match r:
    case Wr.Got{b, s}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case Wr.Bad{}:
      {==}

def kl.left_go(r: Wr.Dec<KL.FileKind>) -> {KernelLocal.read_left.go(r) == FKL.get_left.go(r) : Wr.Dec<KL.Left>}:
  match r:
    case Wr.Got{k, s}:
      kl.left_owner(k, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def kl.left(+s: String) -> {KernelLocal.read_left(s) == FKL.get_left(s) : Wr.Dec<KL.Left>}:
  %kl.kind(Wr.get_nat(s)) : {KernelLocal.read_left.go(KernelLocal.read_kind(Wr.get_nat(s))) == FKL.get_left.go(_) : Wr.Dec<KL.Left>}
  %kl.left_go(KernelLocal.read_kind(Wr.get_nat(s))) : {KernelLocal.read_left.go(KernelLocal.read_kind(Wr.get_nat(s))) == _ : Wr.Dec<KL.Left>}
  {==}

def kl.lefts_cons(l: KL.Left, r: Wr.Dec<List<&2, KL.Left>>) -> {KernelLocal.read_lefts.cons(l, r) == FKL.get_lefts.cons(l, r) : Wr.Dec<List<&2, KL.Left>>}:
  match r:
    case Wr.Got{ls, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.lefts(n: Nat, cur: Wr.Dec<KL.Left>) -> {KernelLocal.read_lefts(n, cur) == FKL.get_lefts.go(n, cur) : Wr.Dec<List<&2, KL.Left>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{l, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+l, +s}:
          %kl.left(s) : {KernelLocal.read_lefts.cons(l, KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == FKL.get_lefts.cons(l, FKL.get_lefts.go(m, _)) : Wr.Dec<List<&2, KL.Left>>}
          %kl.lefts(m, KernelLocal.read_left(s)) : {KernelLocal.read_lefts.cons(l, KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == FKL.get_lefts.cons(l, _) : Wr.Dec<List<&2, KL.Left>>}
          %kl.lefts_cons(l, KernelLocal.read_lefts(m, KernelLocal.read_left(s))) : {KernelLocal.read_lefts.cons(l, KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == _ : Wr.Dec<List<&2, KL.Left>>}
          {==}
        case Wr.Bad{}:
          {==}

def kl.sweep_files(r: Wr.Dec<List<&2, KL.Left>>) -> {KernelLocal.read_sweep.files(r) == FKL.get_sweep.files(r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{ls, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.sweep(r: Wr.Dec<Nat>) -> {KernelLocal.read_sweep(r) == FKL.get_sweep(r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %kl.left(s) : {KernelLocal.read_sweep.files(KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == FKL.get_sweep.files(FKL.get_lefts.go(m, _)) : Wr.Dec<KL.Ask>}
          %kl.lefts(m, KernelLocal.read_left(s)) : {KernelLocal.read_sweep.files(KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == FKL.get_sweep.files(_) : Wr.Dec<KL.Ask>}
          %kl.sweep_files(KernelLocal.read_lefts(m, KernelLocal.read_left(s))) : {KernelLocal.read_sweep.files(KernelLocal.read_lefts(m, KernelLocal.read_left(s))) == _ : Wr.Dec<KL.Ask>}
          {==}
    case Wr.Bad{}:
      {==}

def kl.age_some(r: Wr.Dec<Nat>) -> {KernelLocal.read_age.some(r) == FKL.get_age.some(r) : Wr.Dec<KL.Seen>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.age_tag(t: Nat, s: String) -> {KernelLocal.read_age.tag(t, s) == FKL.get_age.tag(t, s) : Wr.Dec<KL.Seen>}:
  match t:
    case 0n:
      {==}
    case 1n:
      kl.age_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def kl.age(r: Wr.Dec<Nat>) -> {KernelLocal.read_age(r) == FKL.get_age.go(r) : Wr.Dec<KL.Seen>}:
  match r:
    case Wr.Got{t, s}:
      kl.age_tag(t, s)
    case Wr.Bad{}:
      {==}

def kl.owner(r: Wr.Dec<Bool>) -> {KernelLocal.read_owner(r) == FKL.get_owner(r) : Wr.Dec<KL.Seen>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.seen_tag(t: Nat, s: String) -> {KernelLocal.read_seen.tag(t, s) == FKL.get_seen.tag(t, s) : Wr.Dec<KL.Seen>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      kl.owner(Wr.get_bool(s))
    case 3n:
      kl.age(Wr.get_nat(s))
    case 4n+p:
      {==}

def kl.seen(r: Wr.Dec<Nat>) -> {KernelLocal.read_seen(r) == FKL.get_seen.go(r) : Wr.Dec<KL.Seen>}:
  match r:
    case Wr.Got{t, s}:
      kl.seen_tag(t, s)
    case Wr.Bad{}:
      {==}

def kl.lock(r: Wr.Dec<KL.Seen>) -> {KernelLocal.read_lock(r) == FKL.get_lock(r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def kl.ask_tag(t: Nat, +s: String) -> {KernelLocal.read_ask.tag(t, s) == FKL.get_ask.tag(t, s) : Wr.Dec<KL.Ask>}:
  match t:
    case 0n:
      %kl.found(Wr.get_nat(s)) : {KernelLocal.read_plan(KernelLocal.read_found(Wr.get_nat(s))) == FKL.get_plan.found(_) : Wr.Dec<KL.Ask>}
      %kl.plan(KernelLocal.read_found(Wr.get_nat(s))) : {KernelLocal.read_plan(KernelLocal.read_found(Wr.get_nat(s))) == _ : Wr.Dec<KL.Ask>}
      {==}
    case 1n:
      kl.sweep(Wr.get_nat(s))
    case 2n:
      %kl.seen(Wr.get_nat(s)) : {KernelLocal.read_lock(KernelLocal.read_seen(Wr.get_nat(s))) == FKL.get_lock(_) : Wr.Dec<KL.Ask>}
      %kl.lock(KernelLocal.read_seen(Wr.get_nat(s))) : {KernelLocal.read_lock(KernelLocal.read_seen(Wr.get_nat(s))) == _ : Wr.Dec<KL.Ask>}
      {==}
    case 3n+p:
      {==}

# the entry reads every input as the laws' reader does
def kl.ask(r: Wr.Dec<Nat>) -> {KernelLocal.read_ask.go(r) == FKL.get_ask.go(r) : Wr.Dec<KL.Ask>}:
  match r:
    case Wr.Got{t, s}:
      kl.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# Round trips and writers
# -----------------------

# a file the laws spell reads back, whatever follows it
def kl.left_rt(l: KL.Left, rest: String) -> {Wr.Got{l, rest} == FKL.get_left(KernelLocal.spell_left(l, rest)) : Wr.Dec<KL.Left>}:
  match l:
    case KL.Left{k, o}:
      match k o:
        case KL.Cand{} KL.Alive{}:
          {==}
        case KL.Cand{} KL.Dead{}:
          {==}
        case KL.Aside{} KL.Alive{}:
          {==}
        case KL.Aside{} KL.Dead{}:
          {==}
        case KL.Foreign{} KL.Alive{}:
          {==}
        case KL.Foreign{} KL.Dead{}:
          {==}

# the files after the first read back, the first one being l
def kl.lefts_rt(t: List<&2, KL.Left>, +l: KL.Left, +rest: String) -> {Wr.Got{l <> t, rest} == FKL.get_lefts.go(List.length(&2, KL.Left, t), FKL.get_left(KernelLocal.spell_left(l, KernelLocal.spell_lefts(t, rest)))) : Wr.Dec<List<&2, KL.Left>>}:
  match t:
    case Nil{}:
      %kl.left_rt(l, rest) : {Wr.Got{[l], rest} == FKL.get_lefts.go(0n, _) : Wr.Dec<List<&2, KL.Left>>}
      {==}
    case +x <> +u:
      %kl.left_rt(l, KernelLocal.spell_left(x, KernelLocal.spell_lefts(u, rest))) : {Wr.Got{l <> x <> u, rest} == FKL.get_lefts.go(1n+List.length(&2, KL.Left, u), _) : Wr.Dec<List<&2, KL.Left>>}
      %kl.lefts_rt(u, x, rest) : {Wr.Got{l <> x <> u, rest} == FKL.get_lefts.cons(l, _) : Wr.Dec<List<&2, KL.Left>>}
      {==}

def kl.len_keeps(ls: List<&2, KL.Left>) -> {List.length(&2, KL.Left, ls) == List.length(&2, Bool, KL.keeps(ls)) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case l <> t:
      %kl.len_keeps(t) : {1n+List.length(&2, KL.Left, t) == 1n+_ : Nat}
      {==}

# the laws' verdict on a file is the sweep's
def kl.keep(l: KL.Left) -> {KernelLocal.keep_spec(l) == KL.keep(l) : Bool}:
  match l:
    case KL.Left{k, o}:
      match k o:
        case KL.Cand{} KL.Alive{}:
          {==}
        case KL.Cand{} KL.Dead{}:
          {==}
        case KL.Aside{} KL.Alive{}:
          {==}
        case KL.Aside{} KL.Dead{}:
          {==}
        case KL.Foreign{} KL.Alive{}:
          {==}
        case KL.Foreign{} KL.Dead{}:
          {==}

def kl.keeps_items(ls: List<&2, KL.Left>, -rest: String) -> {KernelLocal.spell_keeps(ls, rest) == FKL.put_bools.items(KL.keeps(ls), rest) : String}:
  match ls:
    case Nil{}:
      {==}
    case +l <> t:
      %kl.keeps_items(t, rest) : {Wr.put_bool(KernelLocal.keep_spec(l), KernelLocal.spell_keeps(t, rest)) == Wr.put_bool(KL.keep(l), _) : String}
      %kl.keep(l) : {Wr.put_bool(KernelLocal.keep_spec(l), KernelLocal.spell_keeps(t, rest)) == Wr.put_bool(_, KernelLocal.spell_keeps(t, rest)) : String}
      {==}

# an attempt's end on a lock that names no owner: the same on both sides
def kl.lock_old(old: Bool) -> {FKL.put_end(KL.attempt(KL.lock.past(old)), "") == KernelLocal.spell_end(KernelLocal.judge_spec.old(old), "") : String}:
  match old:
    case True{}:
      {==}
    case False{}:
      {==}
