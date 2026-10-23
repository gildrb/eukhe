# Harness laws: jobs, limits, host and sandbox

Shared rules (what a law secures, the adversary, H1 to H6): [harness.md](harness.md).

### S2. Jobs and limits

One setting bounds every output: tool call, cell, job. A tool call journals only its start and settle.

Limits:

1. Setting `Truncation`. `On(OutputLimits)` keeps at most the limits (bytes, lines, head or tail), counts the rest as dropped; default, 50 KiB and 2000 lines (defaults in `eukhe-types` only). `Off`: explicit opt-out, keeps every byte.
2. Bytes kept + bytes dropped = every byte produced; no silent loss. A cap drops nothing from output that fits.
3. A tool sets its value in `ToolRegistration.truncation`; the harness resolves a call's value in one place (`reporting_for`); a tool reads it via `ToolExecutionApi::truncation`. Under `Off` the final result is not truncated.
4. `BoundedOutput` (eukhe-core) takes its bound from the same value; past it, writes the full output to an artifact file. Under `Off`: keeps everything, no artifact.

A tool call:

1. Journals two records: start (slot `running`, with its `execute` checkpoint) and settle (slot `done`, same commit as the result entry). No progress update is journaled: no output, details, diagnostics, usage.
2. While running, each progress update goes to the Harness's in-memory progress board, which sends each change to the conversation's live observers. `watch_events`: first snapshot has the last progress of each running call, then one `tool_execution_update` per change. No update after the call ends.
3. The settle carries every result byte, every warning, all usage. A call records usage while running with `ToolExecutionApi::usage`. An abort settles from the board, carrying the output the call reported, published or not. The board keeps the call until its settle commits, so an uncommitted settle and the abort settle after it read the same progress.
4. A crash loses the board: the interrupted call's partial live output, details, diagnostics and usage are lost; it settles from what is durable. A `BoundedOutput` artifact keeps the full output.
5. `view_state` holds committed state only: it shows a running call's slot without output. Live output: `watch_events`.

Jobs: work that runs long (a user bash, or an `ipython` cell whose call outlived the blocking budget). Each has an output, one end, a kill.

1. A job counts output under the session cap (`Truncation`, on by default): cap `c` bytes keeps at most `c`, counts the rest as dropped; `Truncation::Off` keeps every byte. Kept + dropped = every byte written. A cell or script becomes a job when its call detaches, starting with the bytes the run wrote before (`JobSpec::written`), so it counts every byte of the run.
2. A job ends once: exit with a code, or the kill signal. The end goes to the session's job writer. Events after the end are ignored.
3. A kill goes through the job's owner: a user bash kills its process group (also when the command closed stdout and stderr); a cell is interrupted and its kernel killed after the grace. The owner reports the end, so a job can end some time after its kill.
4. A blocking call waits at most until its deadline, within the session blocking budget (`toolBlockingBudgetMs`). Job ends first: `Settled` with the end. Else `Detached` at the deadline; the job goes on in the background. A passed deadline detaches at once, even when the end is ready. One function, `jobs::wait_until`, does every blocking wait: the `ipython` call and its wait on a cell that holds the kernel, `jobs.wait`, `jobs.cancel`, `execute_bash_and_wait`. Past the budget, `execute_bash_and_wait` answers `detached: {job, budgetMs}` with the output so far; the run's end records its `eukhe.bash` row.
5. Start and end are session state; output is not. Start creates session document `eukhe.job` (key: job id); end retires it. So the state tree (S1) holds one node under the root per running job.
   - A writer task commits records in order, a batch per commit; no caller waits for it.
   - A job that starts and ends in one batch commits nothing.
   - A failed batch is retried one record at a time; an end whose node is absent retires nothing. A record that fails alone goes to the main conversation as a `job_record_failed` notice.
   - On open, the writer retires the job nodes the history left (their jobs ended with the old process).
6. A rewind stops orphan jobs. When `navigate_tree` or `fork` goes back to an earlier entry (none: before every entry), the session kills every running job that started after that entry was committed and keeps every other job. These are the jobs whose nodes the state tree just after that entry does not hold.
   - Order comes from the entry commits the job table sees as they occur (`JobTable::rewind_to`), not from job nodes: the writer commits a node later, so an entry can come before the node of a job that started before it.
   - An entry from before the open comes before every job.
   - The session waits for the killed jobs' ends, at most the blocking budget. The response names jobs that ended in time (`stoppedJobs`) and jobs not yet ended (`stoppingJobs`).
7. While a job runs, the system prompt has section `running-jobs`: the number and ids of the state tree's job nodes. Absent when no job runs.

Model: `bend/job.bend` (`step`, `ends`, `wait`, `journal`, `rewind`). Laws: `LAWS.bend` section (S2). Proofs: `PROOF.bend` section `job`. Every law is universal: every event is free (any output size, exit, kill or tick, in any order; any cap or the opt-out; any budget; any tool call stream; any job table).

| Law | Says |
| --- | --- |
| `job_output_bounded` | cap: keeps ≤ cap (limits 1, jobs 1) |
| `job_no_silent_loss` | kept + dropped = every byte written before the end (limits 2) |
| `job_optout_keeps_all` | opt-out drops nothing (limits 1) |
| `job_cap_drops_only_excess` | output that fits: nothing dropped (limits 2) |
| `job_ends_once` | exactly one end after exit or kill; none before (jobs 2) |
| `job_end_is_final` | ended: no late output, no second end (jobs 2) |
| `job_kill_ends_now` | kill ends a live job at once as killed; output kept (jobs 3) |
| `call_blocks_at_most_budget` | blocking call returns once its budget passed (jobs 4) |
| `call_settles_with_job` | settled in time: reports the job's own end; no other end (jobs 4) |
| `stream_journals_two` | ≤ 2 journal records per call; no progress record (call 1) |
| `stream_settles_once` | settles exactly once at its end (result or cancel), not before (call 1) |
| `stream_settle_carries_all` | settle carries every result byte, warning, all usage (call 3) |
| `rewind_stops_orphans` | after rewind every running job belongs to the target tree (jobs 6) |
| `rewind_keeps_target_jobs` | target-tree jobs untouched (jobs 6) |
| `job_feed_fits`, `job_feed_no_output`, `job_feed_ended` | the jobs' step (`feed`: step with bytes kept + dropped held to the wire's largest Nat) = the step below that bound (jobs 1) |
| `job_feed_is_a_step`, `job_feed_bounded`, `job_feed_fills` | any output is a step on a part of it; kept + dropped never pass the bound, fill it exactly when the output passes it (jobs 1) |
| `job_entry` (`LAWS.bend` section `core_w6`) | core's job entry answers, on the request Rust writes, the encoded `feed` and the ends the event reported |

Gap: model `rewind` stops a job at once (`stop.at` sets `running` false); the bridge kill records the end at once. So rewind laws cover the kill decision only. The real kill only signals (user-bash cancel, shell task abort, cell interrupt); the job ends later, or never if the process ignores it. Hence `stoppedJobs` lists only jobs ended within the wait; the rest go in `stoppingJobs`.

Code: `eukhe-durable/src/harness/output.rs` (`Truncation`, `OutputLimits`, `OutputBuffer`), `harness/tool/invocation.rs` (`reporting_for`, `publish_progress`, `final_result`, `ToolExecutionApi` `truncation`, `usage`), `harness/tool.rs` `settle` (takes progress from the board), `harness/live/progress.rs` (board), `harness/events.rs` `watch_events`, `eukhe-types/src/output.rs` (default limits), `eukhe-core/src/durable/bounded_output.rs` (`BoundedOutput::in_session`), `eukhe-core/src/durable/jobs/mod.rs` (`Job`, `JobState::step`: `feed` and `ends.of`, run as the compiled Bend core, `bend/ffi_job.bend`; `JobTable` (`start`, `rewind`, `rewind_to`, `observe`), `wait_until`), `jobs/tree.rs` (`eukhe.job` document, writer, `stop_orphans`, `running_jobs_section`), `durable/rlm/jobs.rs` (`CellJobs`: cell board over `Job`; `jobs.list`, `jobs.wait`, `jobs.cancel`), `durable/rlm/tool.rs` (`ipython` wait and detach), `durable/prompt.rs` (`running-jobs`), `eukhe-daemon/src/user_bash.rs` (`UserBash`: every run a job; `execute_bash_and_wait` detaches at the budget), `branch_navigation.rs` (`navigate_tree`, `fork` stop orphans).

Ties (transcripts equal to a Bend file byte for byte):
- `harness::output::bridge::the_rust_output_bounder_equals_the_bend_model`: `OutputBuffer` vs `bridge/bridge_stream.bend`, 300 generated scenarios: a cap (head or tail) or opt-out, output chunks, the end, chunks after the end.
- `harness::tool::tests::bridge::a_real_tool_calls_journal_equals_the_bend_model`: 40 real tool calls on a Harness (result bytes, warnings, usage, then return or cancel). Records every `pi.live` commit from the call's start; prints `start`, `settle` (read from the result entry), or `progress` for any other commit in the slot. The model has no `progress`, so a journaled progress update fails.
- `durable::jobs::bridge::the_rust_jobs_equal_the_bend_model`: `Job`, `wait_until` (paused tokio clock; tick = 1 ms) and `JobTable::rewind` vs `bridge/bridge_job.bend`, 300 generated scenarios reaching every case: truncation, opt-out, kill, quit, event after end, detach at budget, settle within it, rewind that stops a job, rewind that keeps one.

Regression tests: `harness::generation::tests::live_deltas::a_long_streaming_call_commits_nothing_between_its_start_and_its_settle` and the other `live_deltas` tests (what each publication delivers; no commit), `settles_an_aborted_tools_slot_with_its_status_and_entry_only`, eukhe-core `bounded_output` tests (call limits, opt-out), `durable::jobs::tests` (cap and one end, opt-out, rewind kill, wait), `durable::open::tests::jobs_are_state_tree_nodes_the_prompt_shows_and_a_rewind_stops_the_orphans`, daemon `user_bash::tests::an_awaited_run_past_the_budget_answers_detached_and_its_end_records_its_row`, `branch_navigation::tests::navigate_tree_stops_the_jobs_started_after_its_target`.

Not modelled (the tests tie them): map from jobs to documents and from entries to tree cursors (jobs 5, 6); the board's delivery order.

### S3. The host and the sandbox

The host decides; the sandbox executes. The sandbox is the kernel (a session's Python stub): it sends frames to the host, one JSON object per line. A subagent can also work in a workspace sandbox: a copy of its parent's files.

The protocol:

1. The host reads kernel frames in order. One gate decides on each frame before any handler sees it.
2. Accepted: a host request within the size limit, of a served type, with an unseen id. Only accepted frames reach a handler; every one reaches one. The handler's result or error is its one reply.
3. Over the size limit: one error reply, no effect. The host reads only the frame head (the runtime writes `event` and `id` first) and drops the rest up to its newline. The session keeps working.
4. Unserved type, no type, or used id: one error reply, no effect. A used id gets status `duplicate`, not `error`; it goes out under the id of a request possibly still in flight, so the runtime drops it (`_resolve_host_reply`) and the host writes a diagnostic. Only the handler's reply settles the first request with that id.
5. Other events answer the host's own requests; no reply. An oversized stream or display event is dropped with a diagnostic.
6. A frame the host cannot answer is a typed fault (`ProtocolFault`): non-UTF-8 line, non-protocol line, oversized line with no host-request header. Protocol repair then replaces the kernel, loudly: the request in flight fails with the fault.
7. Limits, constants in `frames.rs`: line 32 MiB, gate head 4 KiB, ids kept 1024. The runtime fails a cell whose `display` or `host_request` payload is over 16 MiB before writing the frame.

The gate decides frames in order; refusals go out in that order. An accepted request's reply comes when its handler ends; the kernel matches by id, so a long request (`rlm.run`) does not hold back a short one.

A subagent's workspace:

1. `rlm.spawn(..., workspace="isolated")`: the child gets its own copy of the parent's workspace. `workspace="shared"` (default): the child works in the parent's directory.
2. At spawn the host copies the tracked and untracked, not ignored files of the parent's directory (`git ls-files`; without git, the files its `.gitignore` files do not ignore) twice: the base (workspace as the child found it) and the child's copy (its working directory).
   - Never copies `.git`, `target/`, or another ignored directory.
   - Over 100,000 files (`MAX_WORKSPACE_FILES`): refused; the spawn fails and names `shared`.
   - The hand-back lists the child's copy with its `.gitignore` files only. `.git/info/exclude` and global excludes do not apply there, so a child file only they ignore comes back to the parent.
3. A copy clones extents where the filesystem can (FICLONE on Linux: btrfs, XFS; clonefile on macOS: APFS). Elsewhere it copies bytes and logs a warning with the counts; never silently.
4. At the child's end (its run answers, fails or stalls, or the parent cancels or deletes it), the host first stops the child: worker, kernel and background jobs end; the session stays. Then it takes the child's changes into the parent's directory, path by path:

   | Path | Result |
   | --- | --- |
   | child did not change | parent's content |
   | only child changed | child's content (a removal too) |
   | both changed, same content | kept |
   | both changed, different contents | parent's content; conflict; child's version in the workspace's `conflicts/` |
   | child changed, parent cannot hold it as a file (a directory there, or a file or symlink where one of its directories goes) | parent's entry; conflict; child's version to `conflicts/`; continues with the next path |
5. The child's report and roster row (`rlm.collect`, `rlm.list_subagents`) carry the hand-back: paths taken, conflicts, where the child's versions are. A failed hand-back is reported too; the copy stays.
6. Each path is replaced in one rename from a copy beside it. The copy has the same name in every run, so a run after a crash removes the copy the crash left. Idempotent: a path already taken reads as changed by both to the same content, so a hand-back cut by a crash reruns from the start to the same result. Its record (`handback.json`) ends it; a repeat after the record does not stop the child again. Then base and copy are removed, and the child's directory becomes a symlink to the parent's, so a child woken later starts its kernel there.
7. Location: `<agent dir>/workspaces/<parent session id>/<child id>/`. A child resumed after a daemon restart keeps its copy and base; its stored working directory is the copy.

Default is `shared` because the prompts tell the parent to fan in through files the children write while running ("Have children write files and read those files for fan-in", `prompts/layers/usage.md`), and a child replies with `agent_message` before its run ends. An isolated child's files reach the parent only at the end. Isolation is for children that change the same tree in parallel.

Where the sandbox runs (the kernel transport):

1. Setting `kernelTransport` selects a session's transport. Unset: `Local`, the kernel is a host child process in its own process group with the host's environment.
2. Set: `Wrapped`. The kernel command runs under the wrapper argv (`argvPrefix`); the same stub runs in a container (`docker exec -i <c>`, `podman exec -i <c>`, `docker run -i --rm -v ...`), a VM, or a remote machine (`ssh -T <host>`, with `"command": "shell"`). NDJSON frames and frame limits do not change: the wrapper carries stdin and stdout.
3. Environment of a wrapped kernel: not the host's. It gets the kernel's own entries, host variables named in `env`, and `EUKHE_KERNEL_OWNER=stdin`. An entry holding a host path (`EUKHE_CODING_AGENT_DIR`, `EUKHE_BASH_SHELL`) gets its sandbox path, or is left out with a diagnostic. The wrapper process keeps the host's environment (docker and ssh need it).
   - The sandbox has its own interpreter with eukhe-runtime (`python`, default `python3`); the host's kernel venv is not built for it.
   - A Python skill imports in the sandbox when a mount holds its directory: its sandbox path goes in front of `PYTHONPATH`. Its dependencies must be in the sandbox.
4. `pathMap` lists shared mounts: each is the same directory at `sandbox` and `host`. The kernel starts in the sandbox path of the session cwd. A cwd outside every mount stops the start with an error. The deepest mount holding a path maps it.
5. An `fs.*` host request (`read`, `write`, `edit`, `grep`, `glob`) comes with sandbox paths. The host maps its cwd and each path argument (also `edit` section header paths and `MV` rows) to host paths before a handler sees it, and maps reply paths (`absolute`, `destination`) back.
   - A path outside every mount, or relative to the sandbox home (`~`): typed rejection (`FsError`, reason `outside`, version `transport@1`); no handler runs.
   - "Outside" is also checked on the host disk: the host resolves symlinks of the longest existing part of the host path (and cwd); the result must be in the resolved host directory of a mount. So a symlink in a mount pointing out of every mount, or `..` after it, gets the same rejection.
6. A wrapped kernel's namespace snapshot is written at the sandbox path of the snapshot file. If no mount holds that file, the host asks for no snapshot and writes a diagnostic.
7. Lifetime follows the transport. Local kernel: watches the host pid (`EUKHE_KERNEL_OWNER_PID`). Wrapped kernel: watches stdin; at start makes its own process group, shuts down at stdin EOF. If a synchronous cell holds the loop, it exits after 30 seconds from the reader's side.
8. A kill closes the kernel's stdin, then signals the wrapper's process group; the wrapper ends, so the stub sees stdin close. The host reaps a local kernel's `bash()` process groups from its journal. It cannot reap remote ones (pids are not the host's): the stub's own shutdown and its stdin-EOF exit kill them.

Example (`settings.json`; an untrusted project scope cannot set it):

```json
"kernelTransport": {
  "argvPrefix": ["docker", "exec", "-i", "box"],
  "python": "/opt/venv/bin/python",
  "pathMap": [{ "sandbox": "/work", "host": "/home/me/project" }],
  "env": ["LANG"]
}
```

`@remote`: a kernel function the host offers as a tool.

1. `@remote` (`rlm.remote`) records a Python function and announces it with host request `remote.register`: name, module and qualified name, docstring, JSON schema of its keyword arguments (from type hints). A parameter that cannot be given by keyword is refused.
2. The session adds it to the tool surface as `remote/<name>`, reachable through `dyn` only (S7); never in the roster.
3. A call goes to the calling conversation's kernel as request `call` (`module`, `function`, `args`) on the dedicated lane: it does not wait for a cell, nor a cell for it. The `done` frame gives the result or a typed error (`RemoteCallError`): not running, unreachable, unknown, timeout, failed.
   - A kernel that stops or restarts before replying: `unreachable` at once, not a timeout at the end of the bound.
   - Wrong arguments: `failed` with the `TypeError` text.
   - A result strict JSON cannot carry (NaN, Infinity): `failed` (kernel reason `unencodable`); the frame stays valid JSON; the kernel keeps working.
4. The session blocking budget (S2, `toolBlockingBudgetMs`) bounds the call. The kernel runs a synchronous function on its own daemon thread; a hanging function costs that thread: the call answers `timeout`, and the kernel serves the next cells and calls. The `dyn` result keeps the S2 output limits.
5. An `async def` function runs on the kernel event loop, not a thread. If it blocks without `await`, the whole kernel stops until it returns: cells and calls wait, and its timeout cannot fire. Do blocking work in a synchronous function.

Model: `bend/sandbox.bend` (`serve`, `merge1`, `back`, `plan`). Laws: `LAWS.bend` section (S3). Proofs: `PROOF.bend` section `sandbox`. Every input is free: any frames of any length and kind, any limits, any parent, base and child workspaces.

| Law | Says |
| --- | --- |
| `proto_one_reply_each` | every frame: exactly one reply, in order (S3.1, S3.2-4) |
| `proto_runs_only_accepted` | runs only accepted frames: within size limit, allowed kind (S3.2) |
| `proto_runs_every_accepted` | runs every accepted frame (S3.2) |
| `proto_rejects_oversize` | over size limit: error, runs nothing (S3.3) |
| `cow_keeps_parent` | child did not change: parent's content (workspace 4) |
| `cow_takes_child` | only child changed: child's content (workspace 4) |
| `cow_conflict_reported` | both changed differently: parent's content, reported conflict; no silent loss (workspace 4, 5) |
| `cow_conflict_is_real` | conflict only if both changed to different contents (workspace 4) |
| `cow_plan`, `cow_plan_is_merge` | one path's plan = the copy-on-write rule (keep, taken, conflict, child's file, child's removal); it carries out the merge (workspace 4, 5) |
| `cow_entry` (`LAWS.bend` section `core_w6`) | core's sandbox entry answers, on the request Rust writes, the encoded plan |

Code: `eukhe-core/src/kernel/manager/frames.rs` (`FrameSplitter`, `Gate::admit`, `Admission`, `Refusal`, `ProtocolFault`, limits), `kernel/manager/startup.rs` `wire_child` (stdout reader) and `do_start` (launch of each transport), `kernel/manager/host_requests.rs` (`start_host_request`, `send_host_reply`, `fs.*` path map), `kernel/transport.rs` (`KernelTransport`, `KernelWrapper::launch`, `PathMap`), `kernel/manager/teardown.rs` (`OrphanReap`), `kernel/manager/mod.rs` (`remote_call`, `RemoteCallError`), `kernel/shared.rs` (`HostRequestHandlers::serves`, `KernelHostDispatch::serves`), `durable/rlm/kernels.rs` (`RegistryDispatch`, `kernelTransport` setting), `durable/rlm/remote.rs` (`remote.register`, `remote/<name>` tools), `eukhe-runtime/src/rlm/remote.py` (`remote`), `repl.py` (`_handle_call`, stdin owner), `eukhe-core/src/child_workspace/` (`ChildWorkspace`: `create`, `hand_back`; `merge.rs` `plan`, run as the compiled Bend core, `bend/ffi_sandbox.bend`; `files.rs`: listing, clone, one-rename replace), `durable/children/` (`workspace` kwarg, `RlmSubagentHost::hand_back`, `HandbackOutcome` on row and report), `eukhe-daemon/src/rlm_children/` (workspace at spawn, `hand_back`, `delete`), `eukhe-runtime/src/rlm/__init__.py` (`spawn`).

Ties: hand-back plan = the proven model itself (compiled core). One bridge, transcripts equal to `bridge/bridge_sandbox.bend` byte for byte:
- `kernel::manager::frames::bridge::the_rust_frame_gate_equals_the_bend_model`: 200 generated streams of host-request frames (ids, lengths, kinds) written as the runtime does, cut into reads of random sizes; prints the gate's reply per frame and the frames served. Reaches every rule: served, oversized, unserved kind, frame exactly at the limit.

Tests: `kernel_protocol_frame_caps` (real child: oversized request, unserved type, served one: one reply each; session keeps working; oversized headerless line lands in repair); `kernel::manager::frames::tests` (`a_repeated_id_of_a_request_in_flight_gets_a_duplicate_reply_and_no_handler`); `eukhe-runtime/test/test_repl.py` (`test_host_duplicate_reply_does_not_settle_the_request_in_flight`); `child_workspace::tests` (copy omits ignored files; hand-back; crash-cut hand-back reruns to the same result; `a_hand_back_after_a_crash_removes_the_copy_the_crash_left_beside_a_path`; `a_path_the_parent_holds_as_a_directory_or_under_a_file_is_a_conflict`); children and daemon workspace tests (`rlm_workspace_e2e` `a_child_still_writing_at_its_end_stops_before_its_hand_back`: a child thread writing at the end writes nothing after the hand-back); `kernel::transport::tests` (path map both ways; `fs.*` request and reply maps, refusals; `fs_requests_reject_a_symlink_in_a_mount_that_points_out_of_every_mount`; setting; launch argv, environment); `kernel_transport` (real stub under fake wrapper `setsid -w sh -c 'exec "$@"'`, sandbox dir mapped to another host dir: cwd, environment, `fs.read` host paths in and sandbox paths out, typed refusal, kill via closed stdin); `kernel_remote` (register, call; raising, unknown, hanging function; NaN result; wrong args to an async function; then cells and calls still work; kernel exiting mid-call: unreachable); `eukhe-runtime/test/test_remote.py` (schema, `call` request, `test_a_nan_result_and_bad_async_arguments_answer_typed_errors`, stdin owner).

Not modelled: order of accepted requests' replies (handlers end in any order; the kernel matches by id); the duplicate-id refusal and its `duplicate` reply (model and bridge frames have distinct ids); directories and symlinks in the hand-back (model paths are flat files); the transport and `@remote` (the tests above tie them).

### Local access: the socket dir, file modes and the working dir

Part of G1 (path policy). Only the user running eukhe reaches eukhe's state. A session runs only in the directory its create names.

1. Socket dir. Default daemon socket: `$TMPDIR/eukhe-<uid>/daemon.sock` (`/tmp` if `TMPDIR` unset); uid from `getuid()`. Before the daemon or a worker binds a socket, it checks the socket's directory (the default, or the directory of `--daemon-socket`).
   - A missing directory is created with mode 0700 in one step; missing parents get 0700 too. The daemon then checks it again.
   - Used only if: a real directory (not a symlink), owned by the daemon's uid, no group or other write (no `g+w`, no `o+w`). A user who can write there can replace the socket; read and search bits only allow a connect attempt, which the socket mode and peer check (item 2) stop.
   - Else the daemon does not start. The error names the directory, the fault (symlink, not a directory, owner uid, or mode) and the fix: remove the path, run `chmod go-w` on your own directory, or give `--daemon-socket` a path in a private directory.
   - After the bind, the socket file gets mode 0600; if that fails, the bind fails.
2. Socket peers. The supervisor socket and each worker socket listener read each peer's uid (`SO_PEERCRED`) and accept only the daemon's uid. Every other peer is closed before any frame is read, with a warning logging its uid. A peer whose uid cannot be read is closed too.
3. File modes. Each file eukhe makes for a session (`main.jsonl`, sidecars, staged copies of an import or fork): 0600 at creation. Each directory: 0700 at creation: the agent dir (`~/.eukhe` or `EUKHE_CODING_AGENT_DIR`), the sessions root (`<agent dir>/sessions` or `EUKHE_SESSION_DIR`), each session dir, import and fork staging dirs. The mode is set at creation, so no other user can open the file in between.
   - The process that makes a directory first sets its mode: daemon, CLI, auth store or session storage.
   - At each start the daemon also sets 0700 on the agent dir and sessions root; if it cannot, it does not start.
   - Each session open sets 0700 on its session dir (an older eukhe made it with the umask); if it cannot, the open fails.
   - A fork copy gets 0600 inside its private staging dir, because a copy keeps its source's mode.
   - The user's files (written by the tools) keep the umask.
4. Working dir. A session create must name one; a reopen naming none uses the dir the saved session recorded. It must exist and be a directory, else the create fails with `a session needs a working directory`, `working directory <path> is gone` or `working directory <path> is not a directory`. No path substitutes `/` or the supervisor's working dir. The supervisor starts each worker in its session's working dir; if that dir is gone at a restart, the restart fails.

Model: `bend/fsmode.bend`. Laws: `LAWS.bend` section `fsmode`: `socket_dir_owned`, `socket_dir_progress`, `socket_dir_created`, `socket_dir_created_used`, `peer_same_uid`, `peer_own_accepted`, `private_on_create`, `cwd_is_explicit`, `cwd_none_refused`, `cwd_gone_refused`, `cwd_file_refused`, `cwd_dir_opens`. Proofs: `PROOF.bend` section `fsmode`.

Bridge: `fsmode_bridge::the_local_access_code_equals_the_bend_model` (eukhe-daemon) runs the real code against `bridge/bridge_fsmode.bend`: generated socket dirs (missing, user dirs in nine modes, a link, a file, system dirs of another uid), 64 generated uid pairs, the mode of each dir and file the real creation paths make in a new home (daemon start dirs, socket dir, auth store, a worker's session, an import, a fork), and 48 generated creates (no cwd, empty cwd, missing path, a file, a dir). Not modelled: the peer check reads the uid from the kernel; the bridge drives the rule (`peer_verdict`), not a second user.

### The kernel environment: install once, no downloads in a session

The kernel runs on a venv (`~/.eukhe/kernel-venv`, or `EUKHE_KERNEL_VENV`): a Python from uv plus the packages `eukhe-runtime/requirements-kernel.txt` locks with hashes. A session never downloads them. Install once:

```sh
eukhe kernel install          # download and install the kernel venv
eukhe kernel install --check  # show its state; no network request
```

1. `eukhe kernel install` is the only command that downloads for the kernel. It runs `uv python install` (uv checks the Python download against its pinned sha256) and `uv pip install --require-hashes --only-binary :all:` on the lock (uv checks each wheel's hash before install). Then it installs the runtime from its local directory with `--offline` and checks the venv with `uv pip check`. The kernel starts only on a checked venv. A second run keeps an installed venv, downloads nothing.
2. A session uses the installed venv. If the venv is not for this build (after an update), the session rebuilds it from local files only: every uv command has `--offline` (only uv's cache and the last install's Python installs). Python skills install from their directories, also `--offline`.
3. If local files are not sufficient, `ipython` answers with the error `The Python kernel is not installed: run `eukhe kernel install` once`. The session opens; other tools work.
4. `EUKHE_KERNEL_PYTHON` names a user Python: eukhe installs nothing; `--check` shows that Python.
5. One process at a time sets up a venv, holding the bootstrap lock (`kernel-venv.bootstrap.lock`, a file published with `link(2)`). An attempt writes a candidate file (`kernel-venv.bootstrap.lock.candidate-<pid>-<uuid>`) and removes it on every path. If a process stops inside an attempt, the next acquire removes the candidates and set-aside stale locks (`.stale-<pid>-<uuid>`) of each process that is gone. A live process's file stays.

Model: `bend/kernel_local.bend`. Laws: `LAWS.bend` section `kernel_local`: `kernel_session_never_downloads`, `kernel_download_only_on_install`, `kernel_fetch_verified_before_use`, `kernel_setup_runs`, `kernel_install_fetches`, `kernel_missing_spares_tools`, `kernel_missing_names_install`, `kernel_lock_attempt_leaves_none`, `kernel_lock_sweep_removes_dead`, `kernel_lock_sweep_keeps_live`. Proofs: `PROOF.bend` section `kernel_local`.

Code: `eukhe-core/src/kernel/bootstrap/setup.rs` (`setup_step`: venv found and setup give the step), `venv.rs` (`venv_build_commands`, `skill_install_args`), `mod.rs` (`ensure_kernel_python` for a session, `install_kernel_python` for the command, `format_setup_failure`), `dir_lock.rs` (`try_acquire_dir_lock`, `sweep_leftovers`), `eukhe-cli/src/kernel_command.rs`.

Bridge: `kernel::bootstrap::bridge` (eukhe-core) vs `bridge/bridge_kernel_local.bend`:
- `the_rust_setup_equals_the_bend_model`: each venv found, setup and result: the uv commands (a fetch unless `--offline`; hashed with `--require-hashes` or for `uv python install`), the check, the kernel.
- `the_rust_lock_equals_the_bend_model`: 40 lock dirs (free lock, lock of a live or dead owner, candidates and stale locks of live and dead processes, other files), then a sweep and one attempt.
- `a_missing_kernel_answers_as_its_model`: opens sessions whose venv cannot be set up; calls `ipython` and `bash`.

Not modelled: `--offline` and hash checks are uv's contract; a process stopping inside an attempt is the model's `Crash`, which no test makes.
