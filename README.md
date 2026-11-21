# Eukhe

Eukhe is an agent harness that works a task with no person watching and gives a report at the end. A task is done only when the user's checks pass on the final code.

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64)
```

## Use

```sh
cd project
eukhe                                                     # start; /login at the first start
eukhe -p --accept-cmd 'npm test' "fix the failing tests"  # script; exit 0 only when all checks pass
```

In a session, `/accept cmd --protect tests/app.test.js npm test` sets a check. Then type the task. `eukhe --help` shows all commands.

## Checks

<p align="center"><b>Task:</b> "sort the list"<br><img src="media/sort-1.gif" width="640" alt="Sixteen bars sort in four rounds; the agent says done; the check fills each bar blue from left to right: checks passed"><br><i>The agent says done. The check passes.</i></p>

<p align="center"><b>Next task:</b> "make the sort faster"<br><img src="media/sort-2.gif" width="640" alt="The faster sort takes two rounds and leaves two bars swapped; the agent says done; the check stops red at the pair; the agent swaps them back"><br><i>Two values are out of order. The task goes back to the agent.</i></p>

<p align="center"><b>Before a pass counts:</b><br><img src="media/sort-3.gif" width="640" alt="Eukhe drops the last merge round on purpose; the check stops red where the two halves meet; the break is undone and the check passes"><br><i>Eukhe breaks the code on purpose. The check finds the break.</i></p>

The agent cannot set, change, skip or remove a check. A check that finds less than 80 % of the breaks is weak, and the task ends `checks passed, not certified`. After 3 failed checks in sequence, the task ends `failed`.

## Limits

<p align="center"><img src="media/sort-limit.gif" width="640" alt="A $5 budget with $1 kept for the report; each round reserves its cost, spends, frees the rest; the third round would need the kept money and does not start; the report says two rounds done, two left"><br><i><code>/budget set cost=5 time=2h</code>: a step that needs the money kept for the report does not start.</i></p>

Each step reserves its maximum cost before it starts. The report gives the work done, the work not done and the limit that stopped it.

## Crash recovery

<p align="center"><img src="media/sort-crash.gif" width="640" alt="The run stops in the middle of a round; it starts again with the completed rounds in place; the interrupted round runs again; the check passes"><br><i>After a crash, completed steps stay complete. An interrupted step runs again when that is safe.</i></p>

Eukhe settles an interrupted step from its evidence: the file content, the git ref or the job exit. A step that is not safe to repeat is recorded as not run, and the run continues. `/effects` shows these steps.

## Parallel work

<p align="center"><img src="media/sort-split.gif" width="640" alt="The agent gives each half of the list to a child; both children sort their half at the same time; the halves come back and the agent merges them; the check passes"><br><i>Two child agents each sort one half at the same time. The parent agent merges the halves.</i></p>

Each child works on its own files in its own copy. A parent can set the checks of a child.

## Report

At the end, one report gives the agent's final answer and the result of each check.

**Target:** each step runs without a question in the terminal, the browser, the phone and a script; one message at the end lists each irreversible effect. **Status:** being built.

**Target:** `/undo` puts the files back to their state before a prompt and names the irreversible effects that it cannot undo. **Status:** being built.

## Limitations

There is no sandbox. Code that the agent runs has the user's permissions and can change the files that a check reads; a check fails on a change only to its `--protect` files. A check that finds the breaks can pass on wrong code that is not similar to a break, for example a hard-coded answer. A model request that a crash interrupts is not sent again, and its reserved cost stays counted until its usage is known. A limit that is not set has no maximum.

## Credits

Eukhe is a fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi). The memory design is Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449) and [OptMem](https://github.com/VictorTaelin/OptMem). The edit tools, the tokenizers and the harness design come from [oh-my-pi](https://github.com/can1357/oh-my-pi), and the Claude tokenizer vocabulary from Sander Land's [ctok](https://github.com/sanderland/ctok). Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
