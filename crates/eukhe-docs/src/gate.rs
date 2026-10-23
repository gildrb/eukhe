//! The host's check of every path a document tool reads or writes (the
//! path policy, docs/tools.md S7, `laws/path_policy.bend` (G1)).

use eukhe_types::path_policy::RealPath;

/// What a document tool does to a path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Access {
    /// Reads the content of one file.
    Read,
    /// Lists the names in a directory (a directory read, a glob).
    List,
    /// Reads the content of every file under a directory (a grep).
    Search,
    /// Creates, replaces or deletes the file (a move: its source and its
    /// destination).
    Write,
}

/// The host's check of each path access: the path policy and, when the
/// policy asks for it, the user's approval.
///
/// The document tools call [`AccessGate::check`] once for each access,
/// before it happens, with the resolved path (symlinks followed, as
/// [`eukhe_types::path_policy::resolve`] gives it): the access then
/// happens on its real path. An implementation decides on that value as
/// it is (it does not resolve the real path again: that would lose a
/// loop) and may block until the user answers. It returns `Err` with the
/// reason, for the model, when the access must not happen.
pub trait AccessGate: Sync {
    /// Let `access` to `real` happen, or refuse it with the reason.
    /// `display` names the path as the model wrote it.
    ///
    /// # Errors
    ///
    /// The reason the access did not happen (the policy refused it, the
    /// user denied it, or no one answered).
    fn check(&self, access: Access, real: &RealPath, display: &str) -> Result<(), String>;
}

/// The gate of the tests whose subject is not the gate: it lets every
/// access happen.
#[cfg(test)]
pub(crate) struct Open;

#[cfg(test)]
impl AccessGate for Open {
    fn check(&self, _access: Access, _real: &RealPath, _display: &str) -> Result<(), String> {
        Ok(())
    }
}
