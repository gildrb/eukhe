# eukhe: the laws of area facts, section adaptive: adaptive thinking
# (S6.10.1) at the entry of the model facts, bend/ffi_model_facts.bend,
# on the requests Rust writes (the spellers of laws/model_facts.bend,
# built from the wire primitives)

import Base
import ../../bend/ffi_model_facts.bend as FMF
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../model_facts.bend as ModelFacts

# (S6.10.1) A wire API decides adaptive thinking from the model's explicit
# compat flag, else from the rulebook's answer as a flag with the default
# false (one rule for Anthropic Messages and Bedrock: Rust
# `adaptive_thinking`, crates/eukhe-ai/src/models.rs). The flag decision
# itself (true only at a known 1, an unknown answer the default) is
# laws/infer.bend facts_rulebook_decides and facts_rulebook_default.

# LAW facts_adaptive_compat_wins: an adaptive-thinking request carrying the model's explicit compat
# flag b answers b, whatever the rulebook's answer (every number of the
# answer within the wire)
# EXCLUDES: the rulebook's answer over the model's compat flag, a compat
#   flag read as none or flipped
law facts_adaptive_compat_wins:
  for +b: Bool
  for +a: If.Ans
  for +fits: {ModelFacts.mf.ans_fits(a) == True{} : Bool}
  {FMF.ffi(ModelFacts.spell_adaptive(Some{b}, a)) == Wr.put_bool(b, "") : String}

# LAW facts_adaptive_else_flag: an adaptive-thinking request without a compat flag answers what the
# flag request of the same rulebook answer with the default false answers:
# the rulebook decides, and no rule means false (every number of the
# answer within the wire)
# EXCLUDES: a default of true where no rule applies, a rulebook answer
#   read another way for adaptive thinking than for a flag, a decision
#   from anything but the rulebook's answer
law facts_adaptive_else_flag:
  for +a: If.Ans
  for +fits: {ModelFacts.mf.ans_fits(a) == True{} : Bool}
  {FMF.ffi(ModelFacts.spell_adaptive(None{}, a)) == FMF.ffi(ModelFacts.spell_flag(a, False{})) : String}
