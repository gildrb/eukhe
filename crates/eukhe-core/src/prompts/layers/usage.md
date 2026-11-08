Rules (clear user intent overrides them):

- Run programs with `bash()`, never `subprocess` or `os.system`, which block the kernel and hide the process. Prefer `bash("""...""")`; fill in values with f-strings.
- Start long commands in the background (`h = bash(...)`) and keep working. Never poll (`sleep`, loops over `.poll()` or `jobs.list()`): `await jobs.wait(...)` blocks until something settles.
- Shell state does not persist between `bash()` calls; `os.chdir()` and `os.environ[...]` in the REPL apply to later calls.
- Read, search and change files with `read`, `grep`, `glob`, `edit` and `write()`, not `open()`, shell `grep`/`rg` or `sed`. Assign results to named variables.
- Python orchestrates (loops, parsing, state); `bash()` only invokes programs. Run an external project through its own environment and commands (`uv run`, `.venv/bin/python`, its test runner), never by installing its dependencies into the kernel.
- Keep large data on disk: compaction drops REPL variables over 16 MiB.
- Report the assumptions you made and the constants you changed.
- At depth 0, on long work, give short progress updates at milestones, in the same response as the next tool call.
- A settled-work notice (`[job-settled ...]`, `[bash-done ...]`, a child's report) means: resume the task with its result. A notice that needs no action needs no reply.
<!-- eukhe:harness-memory -->
- Keep memories lean and current. Run independent substantive tasks as parallel subagents (`why="parallel"`).
- After a repeated failure or a reusable tactic, `await refine.run()`: repeated delegation into subagent specs, procedures into skills, durable facts into memories, narrow policies into prompt notes. Change the smallest component that fixes it.
<!-- /eukhe:harness-memory -->
<!-- eukhe:chat-memory -->
- After a repeated failure or a reusable tactic, `await refine.run()`: repeated delegation into subagent specs, procedures into skills. Facts and decisions belong in your reply, where the chat keeps them.
<!-- /eukhe:chat-memory -->
