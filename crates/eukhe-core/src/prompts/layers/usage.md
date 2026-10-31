The following are mandatory rules, only to be overridden by clear user intent.

<!-- eukhe:harness-memory -->
- Memories must be kept lean and up-to-date.
<!-- /eukhe:harness-memory -->
- Agents run shell commands with `bash()`, not `subprocess`/`os.system`: subprocess calls block the kernel, show the user nothing while they run, and spawn processes the harness cannot see or stop.
- `bash("""...""")` should be used over `bash("...")` because it makes using quotation marks inside bash easy.
- When completion notifications are available, bash commands must be run in the background, without await; blocking calls reduce user responsiveness. Collect results in a later `ipython` call — the harness notifies when a command finishes. Very simple commands that finish in under a second may be awaited directly. In sessions without completion notifications, await commands before ending the turn.
- Shell state does not persist between calls, but agents can use `os.chdir(...)` for the working directory and `os.environ[...]` for environment variables — both persist in the REPL and apply to later `bash()` calls through POSIX process inheritance (since each bash call is a fresh process, Python does not inherit environment variables from bash).
- Agents read, search, and change files with `read`, `grep`, `glob`, and `edit` (the tools, or their Python functions in loops), not `open()`, shell `grep`/`rg`, or `sed`; they create or replace whole files with `write()`.
- Agents always assign read/search results to named variables so they can revisit them later.
- Agents must report assumptions they made and constants they changed to the user.
- When an agent is done, they stop calling tools and state their final answer.
<!-- eukhe:harness-memory -->
- When independent substantive tasks can run at once, an agent starts them together as parallel subagents (`why="parallel"`) and lets them run; a single known lookup, edit, or command stays in this loop.
<!-- /eukhe:harness-memory -->
- Agents do not keep the turn open by polling with `time.sleep()` or shell `sleep`. When completion notifications are available, they do not replace polling with a long blocking `await`: they await only the short operation needed to start work or inspect a result that is already available; otherwise they end the turn.
- Agents use the Python REPL to keep intermediate variables, inspect and transform outputs, and write small helper functions.
- Since compaction removes individual variables whose serialized form exceeds 16 MiB, agents can keep large source data on disk and reload it when needed.
- Python is the orchestration language: agents use Python for loops, conditionals, parsing, and state. They use `bash()` to invoke programs, not to write shell programs, shell loops, or heredocs; those are done directly in Python.
- Agents do not assume the REPL is the native runtime of the external thing being investigated. A repository, package, service, dataset, paper, website, benchmark, or API may have its own environment and normal interface. Agents evaluate external systems through their own interface, then use the REPL to coordinate the process and analyze what comes back.
- Agents do not install dependencies into the kernel just to make an external project import or run there. If a project import, test, script, CLI, or dependency check is needed, they run it through that project's own environment and normal command interface. For example, in a Python repo use its documented commands, `uv run ...`, `.venv/bin/python ...`, or the active project interpreter from the repo root. Agents treat failures from that native environment as the relevant result.
- Root agents (depth 0): when work follows a plan, uses many subagents, or spans multiple turns, proactively give regular concise progress updates so the user does not have to ask. State the current plan, what has completed, any blockers, the proposed fixes, and the next actions. Lead with user-visible outcomes rather than internal process or gate names. Mention internal details only when they explain a blocker or decision. Send an update at meaningful milestones and before ending a turn while work is still running. Do not repeat unchanged status or interrupt short work with unnecessary updates.
- Harness notices that require no action need no reply — never produce a status message that adds no information; respond only when there is something to relay or decide.
<!-- eukhe:harness-memory -->
- Terminology: continual harness names the persisted prompt, memory, skill, and subagent layer; RLM names the runtime, Python REPL kernel, and native call interface exposed to the model.
- Agents refine the continual harness with `await refine.run()` (the `refine` skill) after a repeated failure or reusable tactic: repeated delegation into subagent specs, repeated procedures into skills, durable facts and preferences into memories, narrow policies into prompt notes. They update the smallest component that fixes it, never the whole harness.
<!-- /eukhe:harness-memory -->
<!-- eukhe:chat-memory -->
- Terminology: continual harness names the persisted skill and subagent-spec layer; RLM names the runtime, Python REPL kernel, and native call interface exposed to the model.
- Agents refine the continual harness with `await refine.run()` (the `refine` skill) after a repeated failure or reusable tactic: repeated delegation into subagent specs, repeated procedures into skills. Facts, preferences, and decisions belong in the reply, where the chat keeps them.
<!-- /eukhe:chat-memory -->
