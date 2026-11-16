# Philosophy

Eukhe is a harness: the software between a principal and the AI agents that work for that principal. Below: what it guarantees, what it only measures, and the assumptions both rest on.

## Terms

- **Principal**: the person or organisation a run acts for, who answers for it.
- **Agent**: a process acting on model outputs. **Run**: the agent tree started from one request. **Program run**: one execution of any program other than Eukhe's own processes and its launcher: a program an agent or a check starts, a provider's command-line tool, a credential helper.
- **Effect**: an action an agent, or the harness itself, submits to the **core**, the part of the harness that allows or refuses it before it happens (program run, write, message, request, payment). A **consequence** follows outside the core's rulings, such as what a program does once started.
- **Contract**: a run's goal, checks, limits and grants, set through an input no agent or program can write; each term records its setter.
- **Check**: a fixed, capped procedure the harness runs on a copy of the work, returning confirmed, refuted or undecided.
- **Limit**: a cap on money, tokens, requests, tool calls or time, per run or per account. **Grant**: permission for a kind of effect on a target for a time.
- **Isolation**: the core, record, contract, checks, credentials and every trusted part are out of reach of agents and program runs. **Confinement in force**: a listed operating-system mechanism with no known unfixed escape holds a program run to its grants; whether isolation held is a separate fact.
- **Guarantee**: a statement about the core's rulings and record, or a bound a trusted part enforces from a ruling, that holds for every model output while isolation holds. **Measured property**: an estimate published with method, sample and date.
- **Label**: failed if a check is refuted; else unverified if there is no check or a verdict is missing or undecided; else "checks passed" with qualifiers such as "unconfined" or "not isolated"; else verified.

## Values

1. The principal answers for a run. Delegation is worth the accepted work it yields per unit of the principal's attention.
2. The contract is the principal's. An agent never sets, widens or relaxes a term of its own task or an ancestor's; it sets terms only for tasks it starts, inside its own.
3. A report never claims more than the harness knows.
4. First, never traded: no effect whose reserved worst case exceeds what remains of a limit, and no agent's effect outside a grant. Then the checks confirmed. Then cheaper or sooner.
5. A guarantee holds for a model that does not cooperate, whatever its honesty or competence.
6. An allowed effect is launched once per start. It gets a further start only when the target deduplicates it or answers that the first will never take hold; elapsed time never justifies a relaunch.
7. Permission to read and permission to send are not permission to send what was read.
8. No message is refused or held for a missing term, and nothing is asked before starting. An unset term takes the principal's standing profile, else the shipped default, recorded as "shipped default, not set by the principal". The shipped default sets no limit: a run goes until finished, shown as "until finished, shipped default", and the report says the run had no limit; limits are a profile the principal turns on. No other filled bound is unlimited, except the bound on unacknowledged spend, which follows the limits, and none is zero by omission. Shipped grants: an interactive run gets what an interactive session does without asking (model requests to the configured provider, reads and writes in the project, the default tools); other kinds of run get model requests and reads and writes in scope. With no provider configured, the run issues its report saying so.

## Assumptions (each with a dated refutation test)

1. Models keep getting more competent through 2029, and principals delegate larger tasks.
2. Unattended runs spend and act unobserved, and commit faster as models improve.
3. Some runs that optimise toward a check pass it by gaming, at a measured rate.
4. A principal's hours are bounded; accepting goals and checks a model drafted costs attention.
5. Goals admit unintended readings; checks cover part of the intent.
6. Some effects cannot be undone. Processes crash and pause, providers fail, resources are shared.
7. Crashes, contention, overreach and overspend per accepted contract do not fall as models improve.
8. For a reader of its language, accepting a law costs less attention than reading the code it governs.

## Guarantees and what Eukhe does

**Scope.** A guarantee is a statement about the core's rulings and record, or a bound that a trusted part of the harness (storage, operating system, clock) enforces from a ruling. It holds for every model output, a non-cooperating model's included, while isolation holds, and covers what agents do through effects; what program runs do, only while confinement is in force. A program that cannot be confined runs only under an explicit unconfined grant. Interactive runs hold it by default, so work proceeds, counted, and the label reads "checks passed, unconfined"; a run started without it, and every scheduled, loop or autoresearch run, refuses such a program and names the reason. A program run that can reach a protected part breaks isolation, announced first, for every run whose protected parts it could reach, running or later, and for later runs under the same operating-system user until that user's state is reset or checked again. A program holds a placeholder for a credential, which the harness swaps for the real secret on requests to that credential's hosts. A program that cannot work with a placeholder holds the real token, which the report names; starting it counts as a possible break of isolation unless the release lists the token's reach as touching no protected part. *Status:* no confinement or isolation yet; the design is settled and goes to build, where a red team attacks the code.

**Limits.** A limit is the metered spend and time the principal puts at risk if the goal, a check or the model is wrong; it is not a forecast and does not bound damage. Before the first effect every dimension has a limit or a recorded "unlimited", with its source. Each effect reserves its declared worst case first, on the run's and the account's ledgers, so spend passes a limit only when a provider reports more than it declared, which the report shows. Judging the checks, the final answer and the report are reserved first; a limit too small for them is accepted, and the run ends without spending, the report showing the arithmetic. *Status:* an unset limit is unlimited today.

**Sound report.** The report is sound; the result may still be wrong. Witnessed facts are true of the record, the label never exceeds the evidence, and model text is marked as assertion. "Verified" means every check confirmed and no qualifier applies; it confirms those checks only, not that the result meets the intent, which is at best measured.

**Checks.** Checks run on a copy of the work, out of the worker's reach. Worker code a check runs is confined to that copy or needs a grant bound to the judged work; in an interactive run holding the unconfined grant, it runs unconfined, and the verdict counts outside the guarantee, with the label "checks passed, unconfined, not isolated". A held-out check's content never goes to the worker; sent to a provider that may share state with the worker, its secrecy is only measured. It answers only confirmed or not, a bounded number of times. A model judge's yes is measured, not witnessed. A proof counts only with checker, axioms and binding fixed.

**Liveness.** While the run's core and storage are alive, or a supervisor has detected their loss, a stuck run ends or pauses with its cause shown, and every wait ends by the deadline unless time is unlimited. Starvation is ruled out only within shares carved from a parent's limits; a wait on a shared provider quota, machine or account is a pause with its cause, outside the guarantee. A message between agents is delivered at most once; one of unknown delivery is reported interrupted, never silently lost. Without a supervisor, the report says no liveness bound holds.

**Attention.** Questions, approvals, notices and the summary are bounded in count and size in advance. When a demand's answer window closes unanswered, the step is refused and the run continues, or, if the contract asks, the run waits until its deadline; never a yes. Spend since the last acknowledged summary is bounded when the principal sets a bound or turns on limits, and the run pauses at the bound; under the shipped default it is unlimited, as the report states.

**Authority.** Grants come from the contract or the shipped default and only narrow when passed to a child. A recorded stop allows no new agent effect in the subtree, and no agent can delay it. Until confinement is in force, grants and stops bound only the effects the core rules on, not what started programs do; the report says so.

**Irreversible effects.** An effect outside the core counts as irreversible unless it writes only inside the work scope, whose snapshot the harness holds and which the principal, or for an interactive run the shipped default, declared unobserved by outside processes, or its target declares it read-only. Irreversible effects draw on a count per class per run and per account; those the core can value also reserve their worst case against a cumulative money cap, which the shipped default sets to zero. A program run that reaches outside the scope or runs unconfined counts as one and reserves no money; what it does is reported unbounded, so the counts are lower bounds.

**Record and once.** Every effect is recorded with its author and cause before it happens; replay reproduces the rulings and detects changes to anchored entries. A launch follows the run's current owner durably writing its start, and storage refuses a replaced owner's writes, so each start launches at most once without relying on any clock. One of unknown outcome is reported interrupted; its reserved spend stays held.

**Trees, data and core.** A child's limits are carved from its parent's, its grants are a subset of its parent's, and no deadline in the tree is later than the root's. Writing agents form a binary tree: an agent splits work into two children with disjoint scopes, each in its own copy, and integrates their results; a write outside a child's scope comes back as a conflict and is never applied. An agent waits only when no message, child result or own work is pending. Data an agent has read keeps its sensitivity mark in all it then causes; output of an unconfined program carries the highest mark. A grant for a mark covers all data at that mark: under the interactive default the configured provider may receive data at every mark, as the report's first line says. Every interface reaches agents through one core, whose rules are specified as laws and proven where a proof is complete. Objections to the goal are recorded and amend nothing. Prompts carry no guarantee; prompt wording, context management, retries and model routing are practices, kept while measured to help. *Status:* the agent tree is specified with laws; no code runs it yet.

## The bet

For one accepted contract of fixed work, the guarantees multiply the work a principal can delegate per decision by

```
M = D0 / D1 = (q + R + a0 + S_G + S_N) / (q + R + a1 + h + ρ × S_G + S_N)
  D0, D1: decisions without and with the guarantees    q: on competence failures
  R: approvals required by rules outside the harness
  a0, a1: to accept the result without and with the report
  S_G, S_N: on failures the guarantees bound, do not bound
  ρ: share of those a bounded failure still costs    h: decisions the guarantees add
```

M exceeds 1 exactly when D0 exceeds D1: the guarantees remove more decisions, acceptance included, than they add. A growing class of bounded failures raises M only while M stays below one over the share a bounded failure of that class still costs; fewer competence failures also raise M, with no gain from the guarantees. No assumption above makes M rise as models improve, so no guarantee is claimed to gain value faster than competence. That rise is the bet, measured from every decision recorded with its cause. If by 2028-12-31, between registered model generations whose measured competence rose, measured M does not rise by the registered margin once approvals, price and speed are factored out, or rises only with a rising audited defect rate, the bet is false.

---

Definitions, derivations, refutation tests and status per statement: ledger v22 of gildrb/eukhe-philosophy.
