# Harness laws: jobs, limits, host and sandbox

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S2. Jobs and limits

One setting bounds every output: the output of a tool call, of a cell,
and of a job. A tool call journals only its start and its settle.

Limits:

1. The setting is `Truncation`. `On(OutputLimits)` keeps at most the
   limits (bytes, lines, head or tail) and counts the rest as dropped. It
   is the default, with 50 KiB and 2000 lines. These default values are
   in `eukhe-types` only. `Off` is the explicit opt-out: it keeps every
   byte.
2. The bytes kept and the bytes counted as dropped are every byte the
   output produced. No byte is lost in silence. A cap drops nothing from
   output that fits.
3. A tool sets its value in `ToolRegistration.truncation`. The harness
   resolves the value of a call in one place (`reporting_for`). A tool
   reads the value through `ToolExecutionApi::truncation`. Under `Off` the
   final result is not truncated.
4. `BoundedOutput` (eukhe-core) takes its bound from the same value. Past
   the bound it writes the full output to an artifact file. Under `Off` it
   keeps everything and writes no artifact.

A tool call:

1. A call journals two records: its start (the slot becomes `running`,
   with its `execute` checkpoint) and its settle (the slot becomes `done`,
   in the same commit as the result entry). No progress update is
   journaled: no output, no details, no diagnostics, no usage.
2. While the call runs, each progress update goes to the in-memory
   progress board of the Harness. The board sends each change to the live
   observers of the conversation. `watch_events` gives, in its first
   snapshot, the last progress of each running call. Then it gives each
   change as one `tool_execution_update`. No update comes after the end of
   the call.
3. The settle carries everything the call reported: every result byte,
   every warning, and all usage. A call records usage while it runs with
   `ToolExecutionApi::usage`. An abort settles from the board, so it
   carries the output that the call reported, published or not. The board
   keeps the call until its settle commits, so a settle that did not
   commit, and the abort settle after it, read the same progress.
4. Crash behavior changed. Before S2, each progress update was a commit
   to `pi.live`, so a call that a crash interrupted settled with the
   output it had committed. Now the board is lost in a crash. The partial
   live output, details, diagnostics and usage of the interrupted call are
   lost; the call settles from what is durable. When the call wrote a
   `BoundedOutput` artifact, the artifact keeps the full output.
5. A structural view (`view_state`) holds committed state only. So it
   shows the slot of a running call without its output. Use
   `watch_events` for live output.

Jobs (from the jobs slice):

A job is work that runs long: a user bash, or an `ipython` cell whose call
outlived the blocking budget. Each job has an output, one end, and a kill.

1. A job counts its output under the output cap of the session
   (`Truncation`; on by default). Under a cap of `c` bytes it keeps at most
   `c` bytes and counts the rest as dropped. The opt-out (`Truncation::Off`)
   keeps every byte. The bytes kept and the bytes dropped are every byte
   the job wrote. A cell or a script becomes a job when its call detaches;
   the job starts with the bytes the run wrote before (`JobSpec::written`),
   so it also counts every byte of the run.
2. A job ends once: it exits with a code, or the kill signal ends it. The
   end goes to the session's job writer. The job ignores every event after
   its end.
3. A kill sends the kill signal through the owner of the job: a user bash
   kills its process group, also when the command closed its stdout and
   stderr; a cell is interrupted and its kernel is killed after the
   grace. The owner reports the end that follows, so a job can end some
   time after its kill.
4. A blocking call on a job waits at most until its deadline, within the
   blocking budget of the session (`toolBlockingBudgetMs`). It answers
   `Settled` with the end when the job ends first. Else it answers
   `Detached` at the deadline, and the job goes on in the background. A
   deadline that has passed detaches at once, even when the end is ready.
   One function (`jobs::wait_until`) does every blocking wait on a job:
   the `ipython` call and its wait on a cell that holds the kernel,
   `jobs.wait`, `jobs.cancel`, and `execute_bash_and_wait`. Past the
   budget, `execute_bash_and_wait` answers `detached: {job, budgetMs}` with
   the output so far; the end of the run records its `eukhe.bash` row.
5. The start and the end of a job are session state; its output is not.
   The start creates the session document `eukhe.job` (key: the job id);
   the end retires it. So the state tree (S1) holds one node, under the
   root, for each running job. A writer task commits the records in order,
   a batch per commit, and no caller waits for it. A job that starts and
   ends in one batch commits nothing. When a batch fails, the writer
   commits its records one at a time; an end whose node is absent retires
   nothing. A record that fails alone goes to the main conversation as a
   `job_record_failed` notice. On open, the writer retires the job nodes
   that the history left (their jobs ended with the old process).
6. A rewind stops the orphan jobs. When `navigate_tree` or `fork` takes
   the session back to an earlier entry (none: before every entry), the
   session kills every running job that started after that entry was
   committed, and keeps every other job as it is. These are the jobs
   whose nodes the state tree just after that entry does not hold. The
   order comes from the entry commits that the job table sees when the
   commits occur (`JobTable::rewind_to`), not from the job nodes: the
   writer commits a node later, so an entry can come before the node of a
   job that started before it. An entry from before the open comes before
   every job. The session then waits for the ends of the killed jobs, at
   most the blocking budget. The response names the jobs that ended in
   that time (`stoppedJobs`) and the jobs that had not ended yet
   (`stoppingJobs`).
7. While a job runs, the system prompt has the section `running-jobs`. It
   gives the number and the ids of the job nodes of the state tree. The
   section is absent while no job runs.

Model: `bend/job.bend` (`step`, `ends`, `wait`, `journal`, `rewind`).
Laws: `LAWS.bend` section (S2). Proofs: `PROOF.bend` section `job`. Every law
is universal: every event is free (any output size, exit, kill or tick,
in any order; any cap or the opt-out; any budget; any tool call stream;
any job table).

| Law | Says |
| --- | --- |
| `job_output_bounded` | With a cap, a job keeps at most the cap of its output (limits 1, jobs 1). |
| `job_no_silent_loss` | The bytes kept plus the bytes dropped are every byte the job wrote before its end (limits 2). |
| `job_optout_keeps_all` | With the opt-out, a job drops nothing (limits 1). |
| `job_cap_drops_only_excess` | A cap drops nothing from output that fits (limits 2). |
| `job_ends_once` | A job reports exactly one end once it exits or is killed, and none before (jobs 2). |
| `job_end_is_final` | An ended job stays as it ended: no late output, no second end (jobs 2). |
| `job_kill_ends_now` | A kill ends a live job at once, as killed, with its output kept (jobs 3). |
| `call_blocks_at_most_budget` | A blocking call returns once its budget has passed (jobs 4). |
| `call_settles_with_job` | A call that settles in time reports the job's own end, and the job has no other end (jobs 4). |
| `stream_journals_two` | A tool call journals at most two records; no progress update is journaled (call 1). |
| `stream_settles_once` | A tool call settles exactly once when it ends (result or cancel), and not before (call 1). |
| `stream_settle_carries_all` | The settle carries every result byte, every warning, and all usage (call 3). |
| `rewind_stops_orphans` | After a rewind, every running job is a job of the target tree (jobs 6). |
| `rewind_keeps_target_jobs` | A rewind leaves every job of the target tree as it was (jobs 6). |
| `job_feed_fits`, `job_feed_no_output`, `job_feed_ended` | The step the jobs run (`feed`: the step with the bytes kept plus dropped held to the wire's largest Nat) is the step below that bound (jobs 1). |
| `job_feed_is_a_step`, `job_feed_bounded`, `job_feed_fills` | Any output is a step on a part of it; the bytes kept plus dropped never pass the bound and fill it exactly when the output passes it (jobs 1). |
| `job_entry` (`LAWS.bend` section `core_w6`) | The core's job entry, on the request Rust writes, answers the encoded `feed` and the ends the event reported. |

Gap: in the model, `rewind` stops a job at once (`stop.at` sets `running`
to false), and the bridge kill records the end at once. So the two rewind
laws are about the kill decision: which jobs get the kill and which do
not. The real kill only sends a signal (the user-bash cancel, the shell
task abort, the cell interrupt), and the job ends later, or not when its
process ignores the signal. The code does not claim more than the model:
a rewind names a job in `stoppedJobs` only when its end came within the
wait, else in `stoppingJobs`.

Code: `eukhe-durable/src/harness/output.rs` (`Truncation`,
`OutputLimits`, `OutputBuffer`); `harness/tool/invocation.rs`
(`reporting_for`, `publish_progress`, `final_result`, the
`ToolExecutionApi` methods `truncation` and `usage`); `harness/tool.rs`
`settle` (takes the call's progress from the board); `harness/live/progress.rs`
(the progress board); `harness/events.rs` `watch_events`;
`eukhe-types/src/output.rs` (the default limits);
`eukhe-core/src/durable/bounded_output.rs` (`BoundedOutput::in_session`);
`eukhe-core/src/durable/jobs/mod.rs` (`Job`, `JobState::step`: `feed`
and `ends.of`, run as the compiled Bend core, `bend/ffi_job.bend`;
`JobTable` (`start`, `rewind`, `rewind_to`, `observe`), `wait_until`);
`jobs/tree.rs` (the `eukhe.job` document, the writer, `stop_orphans`,
`running_jobs_section`);
`durable/rlm/jobs.rs` (`CellJobs`: the cell board over `Job`;
`jobs.list`, `jobs.wait`, `jobs.cancel`); `durable/rlm/tool.rs` (the
`ipython` call's wait and detach); `durable/prompt.rs` (the
`running-jobs` section); `eukhe-daemon/src/user_bash.rs` (`UserBash`:
every run is a job; `execute_bash_and_wait` detaches at the budget);
`branch_navigation.rs` (`navigate_tree` and `fork` stop the orphans).

Ties: three bridge tests compare transcripts with a Bend file byte for
byte.

- `harness::output::bridge::the_rust_output_bounder_equals_the_bend_model`
  runs `OutputBuffer` and `bend/bridge_stream.bend` on 300 generated
  scenarios: a cap (head or tail retention) or the opt-out, chunks of
  output, and the end of the output, with chunks after the end.
- `harness::tool::tests::bridge::a_real_tool_calls_journal_equals_the_bend_model`
  runs 40 real tool calls on a Harness (result bytes, warnings, usage,
  then a return or a cancel). It records every `pi.live` commit from the
  start of the call and prints `start`, `settle` (read from the result
  entry), or `progress` for any other commit in the call's slot. The
  model has no `progress` record, so a journaled progress update fails
  the test.
- `durable::jobs::bridge::the_rust_jobs_equal_the_bend_model` runs `Job`,
  `wait_until` (on the paused tokio clock; a tick is one millisecond) and
  `JobTable::rewind` with `bend/bridge_job.bend` on 300 generated
  scenarios. The scenarios reach every case: truncation, opt-out, kill,
  quit, an event after the end, a detach at the budget, a settle within
  it, a rewind that stops a job and one that keeps a job.

Regression tests:
`harness::generation::tests::live_deltas::a_long_streaming_call_commits_nothing_between_its_start_and_its_settle`
and the other `live_deltas` tests (what each publication delivers, and no
commit); `settles_an_aborted_tools_slot_with_its_status_and_entry_only`;
the eukhe-core `bounded_output` tests (the limits of a call and the
opt-out); `durable::jobs::tests` (the cap and one end, the opt-out, the
rewind kill, the wait);
`durable::open::tests::jobs_are_state_tree_nodes_the_prompt_shows_and_a_rewind_stops_the_orphans`;
the daemon tests
`user_bash::tests::an_awaited_run_past_the_budget_answers_detached_and_its_end_records_its_row`
and `branch_navigation::tests::navigate_tree_stops_the_jobs_started_after_its_target`.
Not modelled: the map from jobs to documents and from entries to tree
cursors (jobs 5 and 6), and the board's delivery order; the tests above
tie them.

### S3. The host and the sandbox

The host decides; the sandbox executes. The sandbox is the kernel (the
Python stub of a session): it sends frames to the host, one JSON object
per line. A subagent can work in a sandbox of the workspace too: a copy
of its parent's files.

The protocol:

1. The host reads the frames of the kernel in order. One gate decides on
   each frame, before any handler sees it.
2. A host request within the size limit, of a type the host serves, and
   with an id it did not see before, is accepted. Only an accepted frame
   reaches a handler, and every accepted frame reaches one. The handler's
   result or error is its one reply.
3. A host request over the size limit gets one error reply and does
   nothing. The host reads only the head of the frame (the runtime
   writes `event` and `id` first) and drops the rest, up to its newline.
   The session keeps working.
4. A host request of a type the host does not serve, without a type, or
   with a used id gets one error reply and does nothing. The reply to a
   used id has the status `duplicate`, not `error`. It goes out under the
   id of a request that can still be in flight, so the runtime drops it
   (`_resolve_host_reply`) and the host writes a diagnostic. Only the
   handler's reply settles the first request with that id.
5. Other events answer the host's own requests and need no reply. An
   oversized stream or display event is dropped with a diagnostic.
6. A frame the host cannot answer is a typed fault (`ProtocolFault`): a
   line that is not UTF-8, a line that is not a protocol frame, or an
   oversized line with no host-request header. The protocol repair then
   replaces the kernel. It is loud: the request in flight fails with the
   fault.
7. The limits are constants in one place (`frames.rs`): the line limit
   (32 MiB), the head the gate reads (4 KiB), and the ids it keeps
   (1024). The runtime fails a cell whose `display` or `host_request`
   payload is over 16 MiB before it writes the frame.

The gate decides on the frames in order, and the refusals are written in
that order. The reply of an accepted request comes when its handler
ends, and the kernel matches it by id: a long request (`rlm.run`) does
not hold back a short one.

A subagent's workspace:

1. `rlm.spawn(..., workspace="isolated")` gives the child its own copy of
   the parent's workspace. `workspace="shared"` (the default) keeps
   today's behavior: the child works in the parent's directory.
2. At the spawn, the host copies the tracked and the untracked, not
   ignored files of the parent's directory (`git ls-files`; without git,
   the files its `.gitignore` files do not ignore) two times: the base
   (the workspace as the child found it) and the child's copy (its
   working directory). It never copies `.git`, `target/`, or another
   ignored directory. A directory of more than 100,000 files is refused
   (`MAX_WORKSPACE_FILES`): the spawn fails and names `shared`. The
   hand-back lists the child's copy with its `.gitignore` files only.
   `.git/info/exclude` and the global excludes do not apply there, so a
   file of the child that only they ignore comes back to the parent.
3. A copy clones the file's extents where the filesystem can (FICLONE on
   Linux: btrfs, XFS; clonefile on macOS: APFS). Elsewhere it copies the
   bytes and logs a warning with the counts. It never copies in silence.
4. At the child's end (its run answers, fails, or stalls, or the parent
   cancels or deletes it), the host first stops the child: its worker,
   its kernel and its background jobs end, and its session stays. Then
   the host takes the child's changes back into the parent's directory,
   path by path:
   - a path the child did not change keeps the parent's content;
   - a path only the child changed gets the child's content (a removal
     too);
   - a path both changed to the same content keeps it;
   - a path both changed to different contents keeps the parent's
     content and is a conflict. The child's version stays in the
     workspace's `conflicts/` directory.
   - a path the child changed that the parent cannot hold as a file (a
     directory is at that path, or a file or a symlink is where one of
     its directories goes) keeps the parent's entry and is a conflict.
     The child's version goes to `conflicts/`, and the hand-back
     continues with the next path.
5. The child's report and its roster row (`rlm.collect`,
   `rlm.list_subagents`) carry the hand-back: the paths taken, the
   conflicts, and where the child's versions are. A hand-back that fails
   is reported too, and the copy stays.
6. Each path is replaced in one rename, from a copy beside it. The copy
   has the same name in every run, so a run after a crash removes the
   copy that the crash left. The hand-back is idempotent: a path already
   taken reads as changed by both to the same content. So a hand-back
   that a crash cut runs again from the start to the same result. Its
   record (`handback.json`) ends it, and a repeat after the record does
   not stop the child again. Then the base and the copy are removed, and
   the child's directory becomes a symlink to the parent's, so a child
   woken later starts its kernel there.
7. The workspace lives in `<agent dir>/workspaces/<parent session id>/<child id>/`.
   A child that resumes after a daemon restart keeps its copy and its
   base: its stored working directory is the copy.

Why the default is `shared`: the prompts tell the parent to fan in
through files the children write while they run ("Have children write
files and read those files for fan-in", `prompts/layers/usage.md`), and
a child replies with `agent_message` before its run ends. An isolated
child's files reach the parent only at the end. Isolation is for
children that change the same tree in parallel.

Where the sandbox runs (the kernel transport):

1. The setting `kernelTransport` selects the transport of a session. When
   it is not set, the transport is `Local`: the kernel is a child process
   of the host, in its own process group, with the host's environment.
   This is the behavior before the transport.
2. When it is set, the transport is `Wrapped`. The kernel command runs
   under the wrapper's argv (`argvPrefix`). The same stub then runs in a
   container (`docker exec -i <c>`, `podman exec -i <c>`,
   `docker run -i --rm -v ...`), in a VM, or on a remote machine
   (`ssh -T <host>`, with `"command": "shell"`). The NDJSON frames and
   the frame limits do not change: the wrapper carries stdin and stdout.
3. The wrapped kernel does not get the host's environment. It gets the
   kernel's own entries, the host variables that `env` names, and
   `EUKHE_KERNEL_OWNER=stdin`. An entry that holds a host path
   (`EUKHE_CODING_AGENT_DIR`, `EUKHE_BASH_SHELL`) gets its sandbox path,
   or it is left out with a diagnostic. The wrapper process itself keeps
   the host's environment (docker and ssh need it). The sandbox has its
   own interpreter with eukhe-runtime (`python`, default `python3`); the
   host's kernel venv is not built for it. A Python skill imports in the
   sandbox when a mount holds its directory: its sandbox path goes in
   front of `PYTHONPATH`. Its dependencies must be in the sandbox.
4. `pathMap` lists the shared mounts: each one is the same directory at
   `sandbox` and at `host`. The kernel starts in the sandbox path of the
   session's cwd. A cwd outside every mount stops the start with an error.
   The deepest mount that holds a path maps it.
5. An `fs.*` host request (`read`, `write`, `edit`, `grep`, `glob`) comes
   with the sandbox's paths. The host maps its cwd and each path argument
   (the paths of the `edit` section headers and `MV` rows too) to host
   paths before a handler sees it. It maps the paths of the reply
   (`absolute`, `destination`) back. A path outside every mount, or a
   path relative to the sandbox's home (`~`), gets the typed rejection
   (`FsError`, reason `outside`, version `transport@1`), and no handler
   runs. "Outside" is checked on the host's disk too: the host resolves
   the symlinks of the longest part of the host path (and of the cwd)
   that exists, and the result must be in the resolved host directory of
   a mount. So a symlink in a mount that points out of every mount, or a
   `..` after such a symlink, gets the same rejection.
6. The namespace snapshot of a wrapped kernel is written at the sandbox
   path of the snapshot file. When no mount holds that file, the host
   does not ask for a snapshot, and it writes a diagnostic.
7. The lifetime follows the transport. A local kernel watches the host's
   pid (`EUKHE_KERNEL_OWNER_PID`). A wrapped kernel watches its stdin:
   at start it makes a process group of its own, and at stdin EOF it
   shuts down. When a synchronous cell holds the loop, it exits after 30
   seconds from the reader's side.
8. A kill closes the kernel's stdin and then signals the wrapper's
   process group. The wrapper ends, and so the stub sees its stdin close.
   The host reaps the `bash()` process groups of a local kernel from its
   journal. It cannot reap a remote process group: the pids are not the
   host's. The stub's own shutdown and its stdin-EOF exit kill those
   groups.

An example (`settings.json`; a project scope that is not trusted cannot
set it):

```json
"kernelTransport": {
  "argvPrefix": ["docker", "exec", "-i", "box"],
  "python": "/opt/venv/bin/python",
  "pathMap": [{ "sandbox": "/work", "host": "/home/me/project" }],
  "env": ["LANG"]
}
```

`@remote`: a kernel function that the host offers as a tool.

1. `@remote` (`rlm.remote`) records a Python function and announces it
   with the host request `remote.register`: its name, its module and
   qualified name, its docstring, and the JSON schema of its keyword
   arguments (from the type hints). A parameter that cannot be given by
   keyword is refused.
2. The session adds it to the tool surface as `remote/<name>`. The model
   reaches it through `dyn` only (S7): it never enters the roster.
3. A call goes to the kernel of the calling conversation as the request
   `call` (`module`, `function`, `args`). It uses the dedicated lane, so
   it does not wait for a cell, and a cell does not wait for it. The
   `done` frame gives the result or a typed error (`RemoteCallError`):
   not running, unreachable, unknown, timeout, failed. A kernel that
   stops or restarts before it replies gives `unreachable` at once, not
   a timeout at the end of the bound. Wrong arguments give `failed` with
   the `TypeError` text. A result that strict JSON cannot carry (NaN,
   Infinity) gives `failed` (kernel reason `unencodable`); the frame
   stays valid JSON, and the kernel keeps working.
4. The session's blocking budget (S2, `toolBlockingBudgetMs`) bounds the
   call. The kernel runs a synchronous function on its own daemon
   thread. A function that hangs costs that thread: the call answers
   `timeout`, and the kernel serves the next cells and calls. The result
   of the `dyn` call keeps the S2 output limits.
5. An `async def` function runs on the kernel's event loop, not on a
   thread. If it blocks without `await`, the whole kernel stops until it
   returns: cells and other calls wait, and its timeout cannot fire. Do
   blocking work in a synchronous function.

Model: `bend/sandbox.bend` (`serve`, `merge1`, `back`, `plan`). Laws: `LAWS.bend`
section (S3). Proofs: `PROOF.bend` section `sandbox`. Every input is free:
any frames of any length and kind, any limits, any workspaces of the
parent, the base and the child.

| Law | Says |
| --- | --- |
| `proto_one_reply_each` | Every frame gets exactly one reply, in order (S3.1, S3.2-4). |
| `proto_runs_only_accepted` | The host runs only frames it accepts: within the size limit and of an allowed kind (S3.2). |
| `proto_runs_every_accepted` | The host runs every frame it accepts (S3.2). |
| `proto_rejects_oversize` | A frame over the size limit gets an error and runs nothing (S3.3). |
| `cow_keeps_parent` | A path the child did not change keeps the parent's content (workspace 4). |
| `cow_takes_child` | A path only the child changed gets the child's content (workspace 4). |
| `cow_conflict_reported` | A path both changed to different contents keeps the parent's content and is reported as a conflict: no change is lost in silence (workspace 4, 5). |
| `cow_conflict_is_real` | A conflict is real: both changed the path, to different contents (workspace 4). |
| `cow_plan`, `cow_plan_is_merge` | The plan of one path is the copy-on-write rule (keep, taken, conflict, the child's file, the child's removal), and it carries out the merge (workspace 4, 5). |
| `cow_entry` (`LAWS.bend` section `core_w6`) | The core's sandbox entry, on the request Rust writes, answers the encoded plan. |

Code: `eukhe-core/src/kernel/manager/frames.rs` (`FrameSplitter`,
`Gate::admit`, `Admission`, `Refusal`, `ProtocolFault`, the limits);
`kernel/manager/startup.rs` `wire_child` (the stdout reader) and
`do_start` (the launch of each transport);
`kernel/manager/host_requests.rs` (`start_host_request`,
`send_host_reply`, the `fs.*` path map); `kernel/transport.rs`
(`KernelTransport`, `KernelWrapper::launch`, `PathMap`);
`kernel/manager/teardown.rs` (`OrphanReap`); `kernel/manager/mod.rs`
(`remote_call`, `RemoteCallError`); `kernel/shared.rs`
(`HostRequestHandlers::serves`, `KernelHostDispatch::serves`);
`durable/rlm/kernels.rs` (`RegistryDispatch`, the `kernelTransport`
setting); `durable/rlm/remote.rs` (`remote.register`, the `remote/<name>`
tools); `eukhe-runtime/src/rlm/remote.py` (`remote`) and `repl.py`
(`_handle_call`, the stdin owner); `eukhe-core/src/child_workspace/`
(`ChildWorkspace`: `create`, `hand_back`; `merge.rs` `plan`, run as the
compiled Bend core, `bend/ffi_sandbox.bend`;
`files.rs`: the listing, the clone, the one-rename replace);
`durable/children/` (the `workspace` kwarg, `RlmSubagentHost::hand_back`,
`HandbackOutcome` on the row and the report);
`eukhe-daemon/src/rlm_children/` (the workspace at the spawn,
`hand_back`, `delete`); `eukhe-runtime/src/rlm/__init__.py` (`spawn`).

Ties: the hand-back's plan is the proven model itself (the compiled core).
One bridge test compares transcripts with `bend/bridge_sandbox.bend` byte
for byte.

- `kernel::manager::frames::bridge::the_rust_frame_gate_equals_the_bend_model`
  writes 200 generated streams of host-request frames (ids, lengths,
  kinds) as the runtime does, cuts each into reads of random sizes, and
  prints the gate's reply to each frame and the frames it served. The
  scenarios reach every rule: served, oversized, a kind not served, and a
  frame exactly at the limit.

Regression tests: `kernel_protocol_frame_caps` (an oversized host
request, an unserved type and a served one each get one reply on a real
child, and the session keeps working; an oversized line without a
header lands in repair); `kernel::manager::frames::tests`
(`a_repeated_id_of_a_request_in_flight_gets_a_duplicate_reply_and_no_handler`);
`eukhe-runtime/test/test_repl.py`
(`test_host_duplicate_reply_does_not_settle_the_request_in_flight`);
`child_workspace::tests` (the copy leaves ignored files out; the
hand-back; a hand-back cut by a crash runs again to the same result;
`a_hand_back_after_a_crash_removes_the_copy_the_crash_left_beside_a_path`;
`a_path_the_parent_holds_as_a_directory_or_under_a_file_is_a_conflict`);
the children and daemon workspace tests (`rlm_workspace_e2e`
`a_child_still_writing_at_its_end_stops_before_its_hand_back`: a child
thread that still writes at the end writes nothing after the hand-back);
`kernel::transport::tests` (the
path map both ways, the `fs.*` request and reply maps and refusals,
`fs_requests_reject_a_symlink_in_a_mount_that_points_out_of_every_mount`,
the setting, the launch argv and environment); `kernel_transport` (the real
stub under a fake wrapper, `setsid -w sh -c 'exec "$@"'`, in a sandbox
directory mapped to another host directory: the cwd, the environment,
an `fs.read` with host paths in and sandbox paths out, the typed
refusal, the kill through the closed stdin); `kernel_remote` (register,
call, a raising, unknown and hanging function, a NaN result and wrong
arguments to an async function, then cells and calls still work; a
kernel that exits during a call is unreachable);
`eukhe-runtime/test/test_remote.py` (the schema, the `call`
request, `test_a_nan_result_and_bad_async_arguments_answer_typed_errors`,
the stdin owner). Not modelled: the order of the
replies of accepted requests (handlers end in any order; the kernel
matches by id), the duplicate-id refusal and its `duplicate` reply (the
model's frames have distinct ids, and the bridge's streams too),
directories and symlinks in the hand-back (the model's
paths are flat files), the transport and `@remote` (the tests above tie
them).

### Local access: the socket dir, file modes and the working dir

This section is part of G1 (path policy). Only the user that runs eukhe
can reach the state of eukhe. A session runs only in the directory that
its create names.

1. The socket dir. The default daemon socket is
   `$TMPDIR/eukhe-<uid>/daemon.sock` (`/tmp` when `TMPDIR` is not set).
   The uid comes from `getuid()`. Before the daemon or a worker binds a
   socket, it checks the directory of the socket (the default dir or the
   directory of `--daemon-socket`). A missing directory gets mode 0700 at
   creation, in one step; its missing parents get 0700 too. The daemon
   then checks the directory again. The daemon uses the directory only
   when it is a real directory (not a symbolic link), the uid of the
   daemon owns it, and no group or other user can write in it (no `g+w`,
   no `o+w`). A user who can write in the directory can replace the
   socket; read and search bits only let a user try to connect, and the
   socket mode and the peer check (item 2) stop that. In all other cases
   the daemon does not start. The error names the directory, what is
   wrong (a symbolic link, not a directory, the owner uid, or the mode)
   and what to do: remove the path, run `chmod go-w` on your own
   directory, or give `--daemon-socket` a path in a private directory.
   After the bind, the socket file gets mode 0600. If this fails, the bind
   fails.
2. Socket peers. The listener of the supervisor socket and of each worker
   socket reads the uid of each peer (`SO_PEERCRED`). It accepts a peer
   only when that uid is the uid of the daemon. It closes every other
   peer before it reads a frame, and logs a warning with the uid of the
   peer. A peer whose uid it cannot read is closed too.
3. File modes. Each file that eukhe makes for a session (`main.jsonl`,
   the sidecars, the staged copies of an import or a fork) gets mode 0600
   when it is made. Each directory gets mode 0700 when it is made: the
   agent dir (`~/.eukhe` or `EUKHE_CODING_AGENT_DIR`), the sessions root
   (`<agent dir>/sessions` or `EUKHE_SESSION_DIR`), each session dir, and
   the staging dirs of an import or a fork. The mode is set at creation,
   so no other user can open the file in the time between. The process
   that makes a directory first sets the mode: the daemon, the CLI, the
   auth store or the session storage. At each start the daemon also sets
   0700 on the agent dir and on the sessions root. If it cannot, it does
   not start. Each open of a session sets 0700 on its session dir (an
   older eukhe made it with the umask). If it cannot, the open fails. A
   copy in a fork gets 0600 inside its private staging dir,
   because a copy keeps the mode of its source. The modes of the files of
   the user (the files that the tools write) do not change: they keep the
   umask.
4. The working dir. A session create must name a working dir. A reopen
   that names none uses the dir that the saved session recorded. The dir
   must exist and must be a directory. Else the create fails with `a
   session needs a working directory`, `working directory <path> is
   gone` or `working directory <path> is not a directory`. No path uses
   `/` or the working dir of the supervisor in place of the missing one.
   The supervisor starts each worker in the working dir of its session.
   When that dir is gone at a restart, the restart fails.

The Bend model is `bend/fsmode.bend` and the laws are in
`LAWS.bend` section `fsmode`: `socket_dir_owned`, `socket_dir_progress`,
`socket_dir_created`, `socket_dir_created_used`, `peer_same_uid`,
`peer_own_accepted`, `private_on_create`, `cwd_is_explicit`,
`cwd_none_refused`, `cwd_gone_refused`, `cwd_file_refused` and
`cwd_dir_opens`. `PROOF.bend` proves them with
`PROOF.bend` section `fsmode`.

Bridge: `fsmode_bridge::the_local_access_code_equals_the_bend_model`
(eukhe-daemon) runs the real code against `bend/bridge_fsmode.bend`. It
checks generated socket dirs (missing, dirs of the user in nine modes, a
link, a file, and system dirs of another uid), 64 generated uid pairs,
the mode of each dir and file that the real creation paths make in a new
home (the start dirs of the daemon, the socket dir, the auth store, the
session of a worker, an import and a fork), and 48 generated creates
(no cwd, an empty cwd, a missing path, a file, a dir). Not modelled: the
peer check reads the uid from the kernel; the bridge drives the rule
(`peer_verdict`), not a second user.

### The kernel environment: install once, no downloads in a session

The kernel runs on a venv (`~/.eukhe/kernel-venv`, or
`EUKHE_KERNEL_VENV`): a Python from uv and the packages that
`eukhe-runtime/requirements-kernel.txt` locks with hashes. A session
never downloads them. The user installs them once:

```sh
eukhe kernel install          # download and install the kernel venv
eukhe kernel install --check  # show its state; no network request
```

1. `eukhe kernel install` is the only command that downloads for the
   kernel. It runs `uv python install` (uv checks the Python download
   against the sha256 that it pins) and `uv pip install
   --require-hashes --only-binary :all:` on the lock (uv checks each
   wheel against its hash before it installs it). Then it installs the
   runtime from its local directory with `--offline` and checks the venv
   with `uv pip check`. The kernel starts only on a checked venv. A
   second run keeps an installed venv and downloads nothing.
2. A session uses the installed venv. When the venv is not for this
   build (after an update), the session sets it up again from local
   files only: every uv command has `--offline`, so uv uses only its
   cache and the Python installs of the last install. The Python skills
   install from their directories, also with `--offline`.
3. When local files are not sufficient, the `ipython` tool answers with
   the error `The Python kernel is not installed: run `eukhe kernel
   install` once`. The session opens and the other tools work.
4. `EUKHE_KERNEL_PYTHON` names a Python of the user. Then eukhe installs
   nothing, and `--check` shows that Python.
5. One process at a time sets up a venv: it holds the bootstrap lock
   (`kernel-venv.bootstrap.lock`, a file published with `link(2)`). An
   attempt writes a candidate file
   (`kernel-venv.bootstrap.lock.candidate-<pid>-<uuid>`) and removes it
   on every path. When a process stops inside an attempt, the next
   acquire removes the candidates and the stale locks set aside
   (`.stale-<pid>-<uuid>`) of each process that is gone. A file of a
   live process stays.

The Bend model is `bend/kernel_local.bend` and the laws are in
`LAWS.bend` section `kernel_local`: `kernel_session_never_downloads`,
`kernel_download_only_on_install`, `kernel_fetch_verified_before_use`,
`kernel_setup_runs`, `kernel_install_fetches`,
`kernel_missing_spares_tools`, `kernel_missing_names_install`,
`kernel_lock_attempt_leaves_none`, `kernel_lock_sweep_removes_dead` and
`kernel_lock_sweep_keeps_live`. `PROOF.bend` proves them with
`PROOF.bend` section `kernel_local`.

Code: `eukhe-core/src/kernel/bootstrap/setup.rs` (`setup_step`: the
venv found and the setup give the step), `venv.rs`
(`venv_build_commands`, `skill_install_args`), `mod.rs`
(`ensure_kernel_python` for a session, `install_kernel_python` for the
command, `format_setup_failure`), `dir_lock.rs` (`try_acquire_dir_lock`,
`sweep_leftovers`), and `eukhe-cli/src/kernel_command.rs`.

Bridge: `kernel::bootstrap::bridge` (eukhe-core) runs the real code
against `bend/bridge_kernel_local.bend`.
`the_rust_setup_equals_the_bend_model` checks each venv found, each
setup and each result: the uv commands (a fetch unless `--offline`;
hashed with `--require-hashes` or for `uv python install`), the check,
and the kernel. `the_rust_lock_equals_the_bend_model` makes 40 lock dirs
(a free lock, a lock of a live or a dead owner, candidates and stale
locks of live and dead processes, and other files), then sweeps and
makes one attempt. `a_missing_kernel_answers_as_its_model` opens
sessions whose venv cannot be set up and calls `ipython` and `bash`.
Not modelled: that uv keeps `--offline` and checks the hashes is uv's
contract; a process that stops inside an attempt is the model's
`Crash`, which no test makes.
