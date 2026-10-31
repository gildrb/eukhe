# eukhe: the proof of LAW cron_file_finish_exact
# The first claim record of the dispatch is dropped (once it is passed,
# every record stays); the key it names is the spec's; the first job of
# that key takes CronStore.finish_spec (cron_finish_exact) and every
# other job is untouched.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../laws/cron_store.bend as CronStore
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/logic.bend as LCfl
import ../cron_store/cron_finish_exact.bend as PFinish

def cff.names(+k: Nat, m: Maybe<&2, Nat>) -> {CF.names(k, m) == CronFile.names_spec(k, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      LCfl.cfl.eq_comm(x, k)

def cff.and_false(h: Bool) -> {Bool.and(h, False{}) == False{} : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def cff.and_true(h: Bool) -> {Bool.and(h, True{}) == h : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# once the dispatch's record is passed, every record stays
def cff.found(cs: List<&2, CF.Pin>) -> {CF.drops(cs, True{}) == CronFile.stays_spec(cs) : List<&2, Bool>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case CF.Pinned{k, +h}:
          %Equal.sym(Bool, Bool.and(h, False{}), False{}, cff.and_false(h)) : {Bool.not(_) <> CF.drops(t, Bool.or(True{}, _)) == True{} <> CronFile.stays_spec(t) : List<&2, Bool>}
          %cff.found(t) : {True{} <> CF.drops(t, True{}) == True{} <> _ : List<&2, Bool>}
          {==}
        case CF.Unpinned{}:
          %cff.found(t) : {True{} <> CF.drops(t, True{}) == True{} <> _ : List<&2, Bool>}
          {==}

def cff.drops_pin(h: Bool, +t: List<&2, CF.Pin>, ih: {CF.drops(t, False{}) == CronFile.drops_spec(t) : List<&2, Bool>}) -> {Bool.not(h) <> CF.drops(t, Bool.or(False{}, h)) == CronFile.drops_spec.pin(h, t, CronFile.drops_spec(t)) : List<&2, Bool>}:
  match h:
    case True{}:
      %cff.found(t) : {False{} <> CF.drops(t, True{}) == False{} <> _ : List<&2, Bool>}
      {==}
    case False{}:
      %ih : {True{} <> CF.drops(t, False{}) == True{} <> _ : List<&2, Bool>}
      {==}

def cff.drops(cs: List<&2, CF.Pin>) -> {CF.drops(cs, False{}) == CronFile.drops_spec(cs) : List<&2, Bool>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case CF.Pinned{k, +h}:
          %Equal.sym(Bool, Bool.and(h, True{}), h, cff.and_true(h)) : {Bool.not(_) <> CF.drops(t, Bool.or(False{}, _)) == CronFile.drops_spec.pin(h, t, CronFile.drops_spec(t)) : List<&2, Bool>}
          cff.drops_pin(h, t, cff.drops(t))
        case CF.Unpinned{}:
          %cff.drops(t) : {True{} <> CF.drops(t, False{}) == True{} <> _ : List<&2, Bool>}
          {==}

def cff.hit(cs: List<&2, CF.Pin>) -> {CF.hit(cs) == CronFile.hit_spec(cs) : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case CF.Pinned{k, h}:
          match h:
            case True{}:
              {==}
            case False{}:
              cff.hit(t)
        case CF.Unpinned{}:
          cff.hit(t)

# with no key left, every job is untouched
def cff.none(js: List<&2, CF.Slot>, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> {CF.finish.js(js, None{}, u, r, b, n) == CronFile.untouched_spec(js) : List<&2, CS.Fin>}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{key, f}:
          %cff.none(t, u, r, b, n) : {CS.Untouched{} <> CF.finish.js(t, None{}, u, r, b, n) == CS.Untouched{} <> _ : List<&2, CS.Fin>}
          {==}

def cff.slot(go: Bool, +f: CS.Fact, +t: List<&2, CF.Slot>, +k: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat, ih: {CF.finish.js(t, k, u, r, b, n) == CronFile.finish_js_spec(t, k, u, r, b, n) : List<&2, CS.Fin>}) -> {CF.finish.one(go, f, u, r, b, n) <> CF.finish.js(t, CF.finish.rest(go, k), u, r, b, n) == CronFile.finish_js_spec.slot(go, f, t, u, r, b, n, CronFile.finish_js_spec(t, k, u, r, b, n)) : List<&2, CS.Fin>}:
  match go:
    case True{}:
      %cff.none(t, u, r, b, n) : {CS.finish(u, f, r, b, n) <> CF.finish.js(t, None{}, u, r, b, n) == CronStore.finish_spec(u, f, r, b, n) <> _ : List<&2, CS.Fin>}
      %CronStore.cron_finish_exact(u, f, r, b, n) : {CS.finish(u, f, r, b, n) <> CF.finish.js(t, None{}, u, r, b, n) == _ <> CF.finish.js(t, None{}, u, r, b, n) : List<&2, CS.Fin>}
      {==}
    case False{}:
      %ih : {CS.Untouched{} <> CF.finish.js(t, k, u, r, b, n) == CS.Untouched{} <> _ : List<&2, CS.Fin>}
      {==}

def cff.js(js: List<&2, CF.Slot>, +k: Maybe<&2, Nat>, +u: Nat, +r: Bool, +b: Bool, +n: Nat) -> {CF.finish.js(js, k, u, r, b, n) == CronFile.finish_js_spec(js, k, u, r, b, n) : List<&2, CS.Fin>}:
  match js:
    case Nil{}:
      {==}
    case j <> +t:
      match j:
        case CF.Slot{+key, +f}:
          %cff.names(key, k) : {CF.finish.one(CF.names(key, k), f, u, r, b, n) <> CF.finish.js(t, CF.finish.rest(CF.names(key, k), k), u, r, b, n) == CronFile.finish_js_spec.slot(_, f, t, u, r, b, n, CronFile.finish_js_spec(t, k, u, r, b, n)) : List<&2, CS.Fin>}
          cff.slot(CF.names(key, k), f, t, k, u, r, b, n, cff.js(t, k, u, r, b, n))

def CronFile.cron_file_finish_exact(u, js, cs, r, b, n):
  %cff.drops(cs) : {CF.finish(u, js, cs, r, b, n) == CF.Closed{_, CronFile.finish_js_spec(js, CronFile.hit_spec(cs), u, r, b, n)} : CF.Closed}
  %cff.hit(cs) : {CF.finish(u, js, cs, r, b, n) == CF.Closed{CF.drops(cs, False{}), CronFile.finish_js_spec(js, _, u, r, b, n)} : CF.Closed}
  %cff.js(js, CF.hit(cs), u, r, b, n) : {CF.finish(u, js, cs, r, b, n) == CF.Closed{CF.drops(cs, False{}), _} : CF.Closed}
  {==}
