//! The kernel setup's plan: which of the pinned uv fetch, the pinned Python
//! fetch and the kernel env's making run before the kernel starts. The
//! kernel runs on one pinned standalone Python that Eukhe fetches itself,
//! with a pinned uv release that it also fetches itself, into its own
//! directory, on the first kernel use; a session and `eukhe kernel install`
//! run the same plan. The rule is `plan` of `bend/kernel_local.bend`, run by
//! the compiled Bend core (`bend/ffi_kernel_local.bend`, request 0; laws
//! `kernel_plan_read_by_rust`, `kernel_offline_once_fetched`,
//! `kernel_uv_fetched_iff_absent`, `kernel_python_fetched_iff_absent`,
//! `kernel_env_made_iff_absent`, `kernel_fetch_verified_before_use`,
//! `kernel_setup_uses_only_present` and `kernel_setup_ends_started` in
//! `laws/kernel_local.bend`).

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{Entry, Error};

/// What of the pinned kernel toolchain is on disk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Have {
    /// The pinned uv release.
    pub(crate) uv: bool,
    /// The pinned Python.
    pub(crate) python: bool,
    /// The kernel env.
    pub(crate) env: bool,
}

/// One step of the setup, in order; the kernel starts after the last.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetupStep {
    /// Download the pinned uv release archive; it is checked against the
    /// pinned sha256 before it is unpacked.
    FetchUv,
    /// `uv python install` of the pinned version from the pinned download
    /// list; uv checks the archive against the pinned sha256 before it
    /// installs it.
    FetchPython,
    /// `uv venv --offline`: the kernel env from local files only, never
    /// the network.
    MakeEnv,
}

/// The steps for what the setup finds (the compiled Bend core's plan).
pub(crate) fn setup_steps(have: Have) -> Vec<SetupStep> {
    eukhe_bend::expect_core(Entry::KernelLocal, ask(have))
}

/// One action of the core's plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Act {
    /// The uv fetch; `true`: the archive is checked against the pinned
    /// sha256 before it is unpacked.
    FetchUv(bool),
    /// The Python fetch; `true`: uv checks the archive against the pinned
    /// sha256 before it installs it.
    FetchPython(bool),
    /// The env's making, from local files only.
    MakeEnv,
    /// The kernel starts.
    Run,
}

fn ask(have: Have) -> Result<Vec<SetupStep>, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .bool(have.uv)
        .bool(have.python)
        .bool(have.env);
    let reply = eukhe_bend::call(Entry::KernelLocal, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let count = reader.count()?;
    let mut acts = Vec::with_capacity(count.min(4));
    for _ in 0..count {
        acts.push(match reader.tag_of(4, "a setup action")? {
            0 => Act::FetchUv(reader.bool()?),
            1 => Act::FetchPython(reader.bool()?),
            2 => Act::MakeEnv,
            // `tag_of` answers a tag below 4: this is 3.
            _ => Act::Run,
        });
    }
    reader.end()?;
    steps_of(&acts).map_err(Error::from)
}

/// The steps the plan `acts` describes. A plan ends with the start and
/// starts the kernel nowhere else; before it come the uv fetch, the Python
/// fetch and the env's making, each at most once, in that order, every
/// fetch hashed.
fn steps_of(acts: &[Act]) -> Result<Vec<SetupStep>, WireError> {
    let Some((Act::Run, before)) = acts.split_last() else {
        return Err(not_a_plan());
    };
    let steps = before
        .iter()
        .map(|act| match act {
            Act::FetchUv(true) => Ok(SetupStep::FetchUv),
            Act::FetchPython(true) => Ok(SetupStep::FetchPython),
            Act::MakeEnv => Ok(SetupStep::MakeEnv),
            Act::FetchUv(false) | Act::FetchPython(false) | Act::Run => Err(not_a_plan()),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if steps.windows(2).all(|pair| place(pair[0]) < place(pair[1])) {
        Ok(steps)
    } else {
        Err(not_a_plan())
    }
}

/// Where a step stands in a setup.
fn place(step: SetupStep) -> u8 {
    match step {
        SetupStep::FetchUv => 0,
        SetupStep::FetchPython => 1,
        SetupStep::MakeEnv => 2,
    }
}

fn not_a_plan() -> WireError {
    WireError::Malformed {
        at: 0,
        expected: "a setup plan: the uv fetch, the Python fetch and the env's making, each at \
                   most once, in that order, every fetch hashed; then the start",
    }
}

#[cfg(test)]
mod tests {
    use super::SetupStep::{FetchPython, FetchUv, MakeEnv};
    use super::*;

    /// The compiled core's plan for each of the eight things a setup can
    /// find: what is not there is fetched or made, in order, and nothing
    /// else (law `kernel_plan_read_by_rust`).
    #[test]
    fn the_steps_come_from_the_compiled_core() {
        let have = |uv, python, env| Have { uv, python, env };
        let cases: [(Have, &[SetupStep]); 8] = [
            (have(true, true, true), &[]),
            (have(true, true, false), &[MakeEnv]),
            (have(true, false, true), &[FetchPython]),
            (have(true, false, false), &[FetchPython, MakeEnv]),
            (have(false, true, true), &[FetchUv]),
            (have(false, true, false), &[FetchUv, MakeEnv]),
            (have(false, false, true), &[FetchUv, FetchPython]),
            (have(false, false, false), &[FetchUv, FetchPython, MakeEnv]),
        ];
        for (have, steps) in cases {
            let Have { uv, python, env } = have;
            assert_eq!(
                setup_steps(have),
                steps,
                "uv {uv}, python {python}, env {env}"
            );
        }
    }

    /// A reply that is not a plan is malformed: a fetch that is not
    /// hashed, no start at the end, a start before the end, a step out of
    /// order or twice.
    #[test]
    fn a_reply_that_is_not_a_plan_is_malformed() {
        let replies: [&[Act]; 8] = [
            &[],
            &[Act::MakeEnv],
            &[Act::FetchUv(false), Act::Run],
            &[Act::FetchUv(true), Act::FetchPython(false), Act::Run],
            &[Act::Run, Act::Run],
            &[Act::Run, Act::MakeEnv, Act::Run],
            &[Act::MakeEnv, Act::FetchUv(true), Act::Run],
            &[Act::MakeEnv, Act::MakeEnv, Act::Run],
        ];
        for acts in replies {
            assert!(
                matches!(steps_of(acts), Err(WireError::Malformed { .. })),
                "{acts:?}"
            );
        }
        assert_eq!(
            steps_of(&[Act::FetchUv(true), Act::MakeEnv, Act::Run]).ok(),
            Some(vec![FetchUv, MakeEnv])
        );
    }
}
