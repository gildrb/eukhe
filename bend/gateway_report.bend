# gateway_report: what the Signal peer that holds the floor hears of a run
# (Rust: crates/eukhe-gateway report.rs, called by gateway.rs for every
# event of the bound session, after bend/gateway_answer.bend named the
# event's answer): one report when the run ends, nothing while it runs.
#
# - A stop goes at once, at any event; nothing is held after it.
# - Any other event that ends no run: a text or a failure becomes what the
#   gateway holds (the run's last answer so far); nothing keeps what it
#   held. Nothing goes.
# - A run end while work the run started still runs (it wakes the session
#   again): nothing goes; the gateway holds the run's last answer (the
#   end's own answer when it says something, else what it held).
# - A run end with nothing running: the run's last answer goes as the
#   report, with what the run last found left of its task; nothing is
#   held after it. A run that said nothing reports nothing.
# - What is left: a text report gets a blank line, then "Left: " and the
#   words of the left text on one line (gateway_answer's `line`); a failure
#   gets a line break and the same. A missing or blank left text adds
#   nothing.
# Pure: no IO, no @unsafe.

import Base
import ./gateway_answer.bend as Ga

# Whether an event ends a run
type End is Data:
  # the event ends no run
  ENone{}
  # the run ended: whether work it started still runs, and what the run
  # last found left of its task
  ERun{waiting: Bool, left: Maybe<&2, String>}

# What the gateway holds after an event, and what it sends now
type Out is Data:
  Out{held: Ga.Answer, send: Ga.Answer}

# Reports
# -------

def left.of(+t: String, +sep: String, +s: String, b: Bool) -> String:
  match b:
    case True{}:
      t
    case False{}:
      String.append(t, String.append(sep, String.append("Left: ", Ga.line(s))))

# t, then after sep what is left on one line; t alone when nothing is left
def left(+t: String, +sep: String, l: Maybe<&2, String>) -> String:
  match l:
    case None{}:
      t
    case Some{+s}:
      left.of(t, sep, s, Ga.blank(s))

# the report of a run whose last answer is a, with what is left (l)
def report(a: Ga.Answer, l: Maybe<&2, String>) -> Ga.Answer:
  match a:
    case Ga.ANone{}:
      Ga.ANone{}
    case Ga.AText{t}:
      Ga.AText{left(t, "\n\n", l)}
    case Ga.AFailed{r}:
      Ga.AFailed{left(r, "\n", l)}
    case Ga.AStopped{}:
      Ga.AStopped{}

# Steps
# -----

# what the gateway does with the run's last answer k at an event that ends
# (or not) the run
def at(k: Ga.Answer, e: End) -> Out:
  match e:
    case ENone{}:
      Out{k, Ga.ANone{}}
    case ERun{w, l}:
      match w:
        case True{}:
          Out{k, Ga.ANone{}}
        case False{}:
          Out{Ga.ANone{}, report(k, l)}

# the gateway held h; an event answers a and ends the run or not (e)
def step(h: Ga.Answer, a: Ga.Answer, e: End) -> Out:
  match a:
    case Ga.ANone{}:
      at(h, e)
    case Ga.AText{t}:
      at(Ga.AText{t}, e)
    case Ga.AFailed{r}:
      at(Ga.AFailed{r}, e)
    case Ga.AStopped{}:
      Out{Ga.ANone{}, Ga.AStopped{}}
