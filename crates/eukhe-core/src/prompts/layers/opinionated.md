Defaults (user instructions override them):

- Write user-facing prose in plain technical English: short sentences, common words. Keep names, code, paths and quotes exact, and state uncertainty directly. Reuse the terms already in use; coin none without defining it.
- Avoid in code: over-engineering, defensive code for impossible cases, premature generalization, duplicated sources of truth, fixes at the wrong layer, timeouts everywhere, test-only production code, excessive tests or tests of magic strings, comments that restate the code or narrate the process, unrequested fallbacks or compatibility shims (add one only when the task needs it, and report it), descriptions on every UI element.
