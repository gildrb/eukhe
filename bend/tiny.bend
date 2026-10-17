# tiny: the model of the local tiny-model service (docs/inference.md, S9),
# after omp's local models. A role (titles, classification, translation,
# speech, dictation) names a chain of models, local or remote. A task goes
# to the first model of the chain that is available; with none available
# it fails as Unavailable, never on a model outside the chain.
#
# A local model runs in one worker process per model, shared by every
# eukhe process. A process that needs the model connects to the worker;
# with no worker it tries to take the bind lock and starts one. A worker
# answers ping with its tag (build and settings); a process whose tag
# differs replaces the worker. An idle worker exits.
#
# A recursive scan takes the test of its first item as a parameter (Bend
# matches only parameters); `*.at` computes that test.

import Base

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# 1. The chain
# ------------

type Pick is Data:
  Use{model: Nat}
  Unavailable{}

# the head of chain is in up
def up.at(+chain: List<&2, Nat>, +up: List<&2, Nat>) -> Bool:
  match chain:
    case Nil{}:
      False{}
    case m <> rest:
      elem(up, m)

# the first model of chain that `up` holds; hit is elem(up, head)
def pick.go(chain: List<&2, Nat>, +up: List<&2, Nat>, hit: Bool) -> Pick:
  match chain:
    case Nil{}:
      Unavailable{}
    case +m <> +rest:
      match hit:
        case True{}:
          Use{m}
        case False{}:
          pick.go(rest, up, up.at(rest, up))

def pick(+chain: List<&2, Nat>, +up: List<&2, Nat>) -> Pick:
  pick.go(chain, up, up.at(chain, up))

# no model of xs is in up
def none_up(xs: List<&2, Nat>, +up: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.not(elem(up, x)), none_up(rest, up))

# 2. The worker of one model
# --------------------------

type Ev is Data:
  Need{p: Nat, tag: Nat}  # process p needs the model, with its tag
  Gone{}                  # the worker exits (idle, crash, replaced)

# the worker: none, or running with its owner process and tag
type W is Data:
  NoWorker{}
  Worker{owner: Nat, tag: Nat}

# What a need ends in
type Got is Data:
  Started{}    # the process took the lock and started the worker
  Joined{}     # the process connected to a worker with its tag
  Replaced{}   # the worker had another tag: the process replaced it

def W.tag(w: W) -> Maybe<&2, Nat>:
  match w:
    case NoWorker{}:
      None{}
    case Worker{o, t}:
      Some{t}

# the worker after a need of process p with tag, when a worker with tag
# t runs: same tag joins it, another tag replaces it
def need.w(same: Bool, +p: Nat, +tag: Nat, w: W) -> W:
  match same:
    case True{}:
      w
    case False{}:
      Worker{p, tag}

def need.g(same: Bool) -> Got:
  match same:
    case True{}:
      Joined{}
    case False{}:
      Replaced{}

# the worker after one event
def step(w: W, e: Ev) -> W:
  match w:
    case NoWorker{}:
      match e:
        case Gone{}:
          NoWorker{}
        case Need{p, tag}:
          Worker{p, tag}
    case Worker{o, +t}:
      match e:
        case Gone{}:
          NoWorker{}
        case Need{+p, +tag}:
          need.w(Nat.is_eq(t, tag), p, tag, Worker{o, t})

# what one event's need got (none for an exit)
def got(w: W, e: Ev) -> List<&2, Got>:
  match w:
    case NoWorker{}:
      match e:
        case Gone{}:
          Nil{}
        case Need{p, tag}:
          [Started{}]
    case Worker{o, t}:
      match e:
        case Gone{}:
          Nil{}
        case Need{p, tag}:
          [need.g(Nat.is_eq(t, tag))]

# the worker after events
def run(es: List<&2, Ev>, w: W) -> W:
  match es:
    case Nil{}:
      w
    case e <> rest:
      run(rest, step(w, e))

# what each need got, in order
def gots(es: List<&2, Ev>, +w: W) -> List<&2, Got>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      List.append(&2, Got, got(w, e), gots(rest, step(w, e)))

# the tag of the last need among es, if any
def last_tag(es: List<&2, Ev>, t: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match es:
    case Nil{}:
      t
    case e <> rest:
      match e:
        case Need{p, tag}:
          last_tag(rest, Some{tag})
        case Gone{}:
          last_tag(rest, None{})

# the number of needs among es
def needs(es: List<&2, Ev>) -> Nat:
  match es:
    case Nil{}:
      0n
    case e <> rest:
      match e:
        case Need{p, t}:
          1n+needs(rest)
        case Gone{}:
          needs(rest)
