# eukhe: the proof of LAW quirks_any_at_exact

# By induction on the rules, each rule's test rewritten to the spec's.

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks

def qa.rank(r: If.Rule) -> {If.Rule.rank(r) == Quirks.qs_rule_rank(r) : Nat}:
  match r:
    case If.Rule{l, t, d, v}:
      match l:
        case If.Fam{}:
          {==}
        case If.Mod{}:
          {==}
        case If.Host{}:
          {==}

def qa.dir(r: If.Rule) -> {If.Rule.dir(r) == Quirks.qs_dir(r) : Nat}:
  match r:
    case If.Rule{l, t, d, v}:
      {==}

def qa.applies(q: If.Query, r: If.Rule) -> {If.applies(q, r) == Quirks.qs_applies(q, r) : Bool}:
  match q:
    case If.Query{f, m, h}:
      match r:
        case If.Rule{l, t, d, v}:
          match l:
            case If.Fam{}:
              {==}
            case If.Mod{}:
              {==}
            case If.Host{}:
              {==}

def Quirks.quirks_any_at_exact(rs, q, d, k):
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %Quirks.quirks_any_at_exact(rest, q, d, k) : {If.any_at(r <> rest, q, d, k) == Bool.or(Bool.and(Bool.and(Quirks.qs_applies(q, r), Nat.is_eq(Quirks.qs_dir(r), d)), Nat.is_le(k, Quirks.qs_rule_rank(r))), _) : Bool}
      %qa.applies(q, r) : {If.any_at(r <> rest, q, d, k) == Bool.or(Bool.and(Bool.and(_, Nat.is_eq(Quirks.qs_dir(r), d)), Nat.is_le(k, Quirks.qs_rule_rank(r))), If.any_at(rest, q, d, k)) : Bool}
      %qa.rank(r) : {If.any_at(r <> rest, q, d, k) == Bool.or(Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(Quirks.qs_dir(r), d)), Nat.is_le(k, _)), If.any_at(rest, q, d, k)) : Bool}
      %qa.dir(r) : {If.any_at(r <> rest, q, d, k) == Bool.or(Bool.and(Bool.and(If.applies(q, r), Nat.is_eq(_, d)), Nat.is_le(k, If.Rule.rank(r))), If.any_at(rest, q, d, k)) : Bool}
      {==}
