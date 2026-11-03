# eukhe: the proof of LAW child_step_exact
# Event by event: the inbox's acts and lookups are the rule's (pcs.act,
# pcs.find), the watch's verdict is K1's (LAE.cl.look), the abort, the
# report rule, the parent's read (pcs.read) and the mark are the rule's,
# case by case.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../../laws/child/run.bend as ChildRun
import ./base/entry.bend as LAE

def pcs.hit(b: Bool, f: Ch.Fate) -> {Ch.Act.hit(b, f) == ChildRun.chr_hit(b, f) : Ch.Fate}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pcs.settle(f: Ch.Fate, a: Ch.Act, +i: Nat) -> {Ch.Fate.act(a, i, f) == ChildRun.chr_settle(f, a, i) : Ch.Fate}:
  match f:
    case Ch.Queued{}:
      match a:
        case Ch.Place{+m}:
          pcs.hit(Nat.is_eq(i, m), Ch.Placed{})
        case Ch.Pull{+m}:
          pcs.hit(Nat.is_eq(i, m), Ch.Withdrawn{})
        case Ch.PullAll{}:
          {==}
    case Ch.Withdrawn{}:
      {==}
    case Ch.Placed{}:
      {==}
    case Ch.Read{}:
      {==}

def pcs.act(xs: List<&2, Ch.Sub>, +a: Ch.Act) -> {Ch.act(xs, a) == ChildRun.chr_inbox(xs, a) : List<&2, Ch.Sub>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case Ch.Sub{+i, +f}:
          %pcs.settle(f, a, i) : {Ch.Sub{i, Ch.Fate.act(a, i, f)} <> Ch.act(r, a) == Ch.Sub{i, _} <> ChildRun.chr_inbox(r, a) : List<&2, Ch.Sub>}
          %pcs.act(r, a) : {Ch.Sub{i, Ch.Fate.act(a, i, f)} <> Ch.act(r, a) == Ch.Sub{i, Ch.Fate.act(a, i, f)} <> _ : List<&2, Ch.Sub>}
          {==}

def pcs.here(b: Bool, f: Ch.Fate, x: Maybe<&2, Ch.Fate>) -> {Maybe.or(&2, Ch.Fate, Ch.fate.here(b, f), x) == ChildRun.chr_here(b, f, x) : Maybe<&2, Ch.Fate>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pcs.find(xs: List<&2, Ch.Sub>, +n: Nat) -> {Ch.fate(xs, n) == ChildRun.chr_find(xs, n) : Maybe<&2, Ch.Fate>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +r:
      match x:
        case Ch.Sub{+i, +f}:
          %pcs.find(r, n) : {Maybe.or(&2, Ch.Fate, Ch.fate.here(Nat.is_eq(i, n), f), Ch.fate(r, n)) == ChildRun.chr_here(Nat.is_eq(i, n), f, _) : Maybe<&2, Ch.Fate>}
          pcs.here(Nat.is_eq(i, n), f, Ch.fate(r, n))

def pcs.mark(cut: Maybe<&2, Bool>, del: Bool) -> {Ch.mark(cut, del) == ChildRun.chr_mark(cut, del) : Maybe<&2, Bool>}:
  match cut:
    case None{}:
      {==}
    case Some{d}:
      {==}

def pcs.watched(x: Ch.Next) -> {Ch.watched(x) == ChildRun.chr_watched(x) : Ch.Ph}:
  match x:
    case Ch.Watch{w}:
      {==}
    case Ch.Owe{k}:
      {==}
    case Ch.Quiet{}:
      {==}

def pcs.abort(ph: Ch.Ph, del: Bool) -> {Ch.cut.ph(ph, del) == Child.ChildAbort(ph, del) : Ch.Ph}:
  match ph:
    case Ch.Watching{w}:
      match del:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ch.Owing{k, n}:
      {==}
    case Ch.Ended{}:
      {==}

def pcs.owe(f: Maybe<&2, Ch.Fate>, k: Ch.Report, +n: Nat, open: Bool, inbox: List<&2, Ch.Sub>) -> {Ch.owe(f, k, n, open, inbox) == ChildRun.chr_owe(f, k, n, open, inbox) : Ch.St}:
  match f:
    case None{}:
      match open:
        case True{}:
          {==}
        case False{}:
          {==}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          {==}
        case Ch.Placed{}:
          {==}
        case Ch.Read{}:
          {==}

def pcs.read.at(same: Bool, +n: Nat, +i: Nat, f: Ch.Fate, r: List<&2, Ch.Sub>) -> {Ch.read.at(same, n, Ch.Sub{i, f}, r) == ChildRun.chr_read.at(same, n, i, f, r) : List<&2, Ch.Sub>}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          {==}
        case Ch.Placed{}:
          {==}
        case Ch.Read{}:
          {==}
    case False{}:
      {==}

def pcs.read.sub(xs: List<&2, Ch.Sub>, +n: Nat) -> {Ch.read.sub(xs, n) == ChildRun.chr_read.sub(xs, n) : List<&2, Ch.Sub>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      match x:
        case Ch.Sub{+i, f}:
          pcs.read.at(Nat.is_eq(i, n), n, i, f, r)

def pcs.read(ph: Ch.Ph, +inbox: List<&2, Ch.Sub>) -> {Ch.read(ph, inbox) == ChildRun.chr_read(ph, inbox) : List<&2, Ch.Sub>}:
  match ph:
    case Ch.Watching{w}:
      {==}
    case Ch.Owing{k, +n}:
      pcs.read.sub(inbox, n)
    case Ch.Ended{}:
      {==}

def pcs.poll(+cfg: Ch.Cfg, cut: Maybe<&2, Bool>, +ph: Ch.Ph, +open: Bool, +inbox: List<&2, Ch.Sub>, +dt: Nat, +o: Ch.Obs) -> {Ch.task(cfg, ph, cut, open, inbox, dt, o) == ChildRun.chr_poll(cfg, cut, ph, open, inbox, dt, o) : Ch.St}:
  match cut:
    case Some{+del}:
      %pcs.abort(ph, del) : {Ch.St{Ch.cut.ph(ph, del), None{}, open, inbox} == Ch.St{_, None{}, open, inbox} : Ch.St}
      {==}
    case None{}:
      match ph:
        case Ch.Watching{+w}:
          %LAE.cl.look(cfg, w, 1n+dt, o) : {Ch.St{Ch.watched(Ch.look(cfg, w, 1n+dt, o)), None{}, open, inbox} == Ch.St{ChildRun.chr_watched(_), None{}, open, inbox} : Ch.St}
          %pcs.watched(Ch.look(cfg, w, 1n+dt, o)) : {Ch.St{Ch.watched(Ch.look(cfg, w, 1n+dt, o)), None{}, open, inbox} == Ch.St{_, None{}, open, inbox} : Ch.St}
          {==}
        case Ch.Owing{+k, +n}:
          %pcs.find(inbox, n) : {Ch.owe(Ch.fate(inbox, n), k, n, open, inbox) == ChildRun.chr_owe(_, k, n, open, inbox) : Ch.St}
          pcs.owe(Ch.fate(inbox, n), k, n, open, inbox)
        case Ch.Ended{}:
          {==}

def pcs.step(+cfg: Ch.Cfg, s: Ch.St, e: Ch.Ev) -> {Ch.step(cfg, s, e) == ChildRun.chr_step(cfg, s, e) : Ch.St}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      match e:
        case Ch.Poll{+dt, +o}:
          pcs.poll(cfg, cut, ph, open, inbox, dt, o)
        case Ch.Deliver{+m}:
          %pcs.act(inbox, Ch.Place{m}) : {Ch.St{ph, cut, open, Ch.act(inbox, Ch.Place{m})} == Ch.St{ph, cut, open, _} : Ch.St}
          {==}
        case Ch.Withdraw{+m}:
          %pcs.act(inbox, Ch.Pull{m}) : {Ch.St{ph, cut, open, Ch.act(inbox, Ch.Pull{m})} == Ch.St{ph, cut, open, _} : Ch.St}
          {==}
        case Ch.Abort{}:
          %pcs.act(inbox, Ch.PullAll{}) : {Ch.St{ph, cut, open, Ch.act(inbox, Ch.PullAll{})} == Ch.St{ph, cut, open, _} : Ch.St}
          {==}
        case Ch.Shut{}:
          %pcs.act(inbox, Ch.PullAll{}) : {Ch.St{ph, cut, False{}, Ch.act(inbox, Ch.PullAll{})} == Ch.St{ph, cut, False{}, _} : Ch.St}
          {==}
        case Ch.Reopen{}:
          {==}
        case Ch.Cut{+del}:
          %pcs.mark(cut, del) : {Ch.St{ph, Ch.mark(cut, del), open, inbox} == Ch.St{ph, _, open, inbox} : Ch.St}
          {==}
        case Ch.Collect{}:
          %pcs.read(ph, inbox) : {Ch.St{ph, cut, open, Ch.read(ph, inbox)} == Ch.St{ph, cut, open, _} : Ch.St}
          {==}

def ChildRun.child_step_exact(cfg, s, e):
  pcs.step(cfg, s, e)
