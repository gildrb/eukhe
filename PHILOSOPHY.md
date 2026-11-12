# Philosophy

Working notes on what Eukhe is for. They change as the thinking does.

## The question

If AGI arrived today and any task were possible, how would you want it done? What still matters when everything is possible?

Four things:

1. **Cost.** What it may spend: money, a share of a plan's usage, tokens.
2. **Time.** When it must be finished.
3. **Truthfulness.** Whether the result was reached the way you agreed, and whether what the agent reports is what happened.
4. **Results.** The work itself. Given enough budget, reaching a goal is easy; the budget decides the quality of the result.

AGI is likely within a year. Today's harnesses are built around today's models. Eukhe is built for the models that come next, and works with weak ones too.

## Constraints, not goals

"Keep going until it's done" is the wrong instruction, for a person or an agent. With nothing else to aim at, any way to "done" will do, including ways nobody agreed to.

You give Eukhe a goal and the limits it must stay within:

- "Reach the goal without costing me more than €100."
- "Formalize the seven pillars from the spec and implement them end to end, using at most 80% of my Fable usage."
- "Finish by tonight."

Eukhe plans the work to fit. It may take longer, use a cheaper model, or pace itself, but it does not run past a limit or run out of quota halfway. Harnesses today run until the work is done with no sense of what it took or what it cost.

Without limits you can still say "hill-climb on this until I stop you" (`/autoresearch`). Most harnesses don't offer that at all.

## Done is not enough

A test checks the result, not how it was reached. In school, one student studies and passes, one studies and fails, one cheats and passes. The test cannot tell the first and third apart. Agents cheat the same way: they change the test, hard-code the expected answer, skip the check, or report success that did not happen.

So Eukhe checks the process as well as the outcome:

- Checks the agent can't edit, and checks it never sees.
- An independent review of what the agent actually did, looking for gaming.
- Labels that never claim more than is known: verified, unverified, failed, or passed but not trusted.

This is why `/goal` alone is an anti-pattern: it rewards reaching "done" by any means.

## Any model, small to AGI

The harness should take any model, from a small local one to AGI, and get the work done within the limits. A weak model makes more mistakes; the harness makes them safe to make. Its state survives a crash, it retries without repeating an effect, it checks every claim, and it never overspends. Given enough budget, even a bad model eventually reaches the goal, and reaches it honestly.

## What stops mattering, what matters more

Looking three to five years ahead, much of what harnesses do today stops mattering:

- Long system prompts and prompt engineering aimed at a model's weaknesses.
- Fixed workflows: plan mode, step lists, fixed agent roles.
- Context tricks: summaries, compaction heuristics, retrieval over the repository. Memory belongs here: useful, not where the value is.
- Many narrow tools, where a few general ones would do.
- Approving every command by hand. That does not scale to a thousand agents.
- How fast code gets written. Code becomes cheap; deciding what you want and checking that you got it does not.

What matters more:

- Intent stated exactly: the goal, the limits, the laws.
- Hard limits on cost, time, quota and rights. A smarter model can do more damage faster.
- Truthfulness: independent checks, held-out checks, a faithful record. A smarter model is also better at making a wrong result look right.
- Correct edges: state that survives crashes, effects that happen exactly once. They let a long run go unattended.
- Choosing the model: the cheapest one that can do each part, a stronger one only where it fails.

## Scaling with the model

A harness offers two kinds of things. Guidance (prompts, workflows, hints) helps a weak model and gets in a strong one's way. Guarantees (limits, verification, exactly-once effects, rights, the record) are right for a small model and for AGI alike.

Eukhe puts its weight on guarantees and keeps guidance thin and optional, chosen per model. A smarter model then gets more done inside the same limits instead of outgrowing the harness. Every new feature is either a guarantee or optional guidance, never required hand-holding.

A weak model makes more mistakes. The harness keeps them cheap and harmless:

- It runs the checks itself and hands back the failure, instead of telling the model to remember to check.
- It retries inside the budget. A model that is wrong most of the time still succeeds when each attempt is cheap, checked and can't cause damage.
- It starts with a cheap model and escalates to a stronger one only for the part that keeps failing, so the budget decides the quality.
- It splits work into smaller checked steps for a weaker model and larger ones for a stronger model. The guarantees stay the same.
- It gives the model laws as the target. Code that doesn't meet them fails its proof and is tried again, within the budget.

## Laws

People will stop reading code. They still need an exact way to say what they want. A law states a requirement precisely; a proof shows the code meets it. If the laws are good and the proofs pass, the implementation matches the spec, and nobody has to read the proofs or the code.

So good laws are the spec, formalized. A trivial law proves nothing and costs check time. Every pillar of Eukhe has a spec, and the spec becomes laws proven against the core that makes Eukhe's decisions.

## A core, not an app

Eukhe is a core with an SDK. A product embeds it and gets everything above. The `eukhe` command is one product built on it. The goal is for Eukhe to be what other harnesses and interfaces are built on.

The core runs in one of two places. As a library it runs inside the product's own process, and the product's tools are plain functions. In the daemon, sessions survive crashes and app restarts, several interfaces can share one session, and the agent's work is kept apart from the product. The SDK is planned to offer one API for both: the product picks one in its configuration and can switch later without rewriting code, and its tools, approvals, budgets and cancellation work the same way in either. Today the two have separate APIs.

## Reproducible

The same inputs give the same behavior on every machine: one pinned toolchain, one pinned Python for the kernel, locked package versions. Results that depend on what happens to be installed can't be guaranteed.

## What matters, in order

1. **Budgets:** hard limits on cost, time, tokens, tool calls and plan usage, for a task and everything it starts.
2. **Verified completion:** "done" confirmed independently, and the process checked for cheating.
3. **Exactly-once effects:** after any crash, nothing is done twice and nothing is claimed that wasn't done.
4. **Loop and autoresearch:** work toward a condition, or keep improving until stopped, within the limits.
5. **Durable sessions:** state survives anything.
6. **Capability security, a replayable record, orchestration at scale, a stable SDK contract:** what makes a thousand unattended agents safe to run.

Memory and context management help, but they don't define Eukhe, and they won't be what matters with AGI.

## Open questions

- How should a plan's usage window (for example "80% of my Fable quota") be measured and paced across providers?
- How much of a run's process can an independent judge review for faithfulness before the review costs more than it saves?
- Which limits should a parent be allowed to pass to the agents it starts?
