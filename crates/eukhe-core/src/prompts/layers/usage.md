Rules (clear user intent overrides them):

- Run programs with `bash()`, never `subprocess` or `os.system`, which block the kernel and hide the process. Prefer `bash("""...""")`; fill in values with f-strings.
- Run long or serial work (builds, test loops) outside the kernel: background `h = bash(...)`, the `bash` tool, or children; a long cell blocks later cells. Await a check, editing nothing: it judges one tree. Never poll (`sleep`, `.poll()` or `jobs.list()` loops).
- Shell state does not persist between `bash()` calls; `os.chdir()` and `os.environ[...]` in the REPL apply to later calls.
- Read, search and change files with `read`, `grep`, `glob`, `edit` and `write`, not `open()`, shell `grep`/`rg` or `sed`. Assign results to named variables.
- Python orchestrates (loops, parsing, state); `bash()` only invokes programs. Run an external project through its own environment and commands (`uv run`, `.venv/bin/python`, its test runner), never by installing its dependencies into the kernel.
- Report the assumptions you made and the constants you changed.
- At depth 0, on long work, give short progress updates at milestones, in the same response as the next tool call.
- On a settled-work notice (a job's or a child's report), resume with its result; one needing no action needs no reply.
<!-- eukhe:harness-memory -->
- Keep memories lean and current.
- After a repeated failure or a reusable tactic, `await refine.run()`: repeated delegation into subagent specs, procedures into skills, durable facts into memories, narrow policies into prompt notes. Change the smallest component that fixes it.
<!-- /eukhe:harness-memory -->
<!-- eukhe:chat-memory -->
- After a repeated failure or a reusable tactic, `await refine.run()`: repeated delegation into subagent specs, procedures into skills. Facts and decisions belong in your reply, where the chat keeps them.
<!-- /eukhe:chat-memory -->
