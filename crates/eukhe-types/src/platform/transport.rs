//! Transport contract for eukhe's sockets and streams.
//!
//! Callers bind/connect through these functions and never name a concrete
//! socket type; `AF_UNIX` sockets are the only implementation. An endpoint
//! is named by a path:
//!
//! - On Linux eukhe binds it as an abstract socket whose name is the path's
//!   bytes: no file, so no grant on a directory reaches it, and the kernel
//!   frees the name when the listener closes (`/proc/net/unix` shows it as
//!   `@<path>`). A Landlock domain scoped for abstract sockets cannot
//!   connect to it.
//! - Elsewhere it is a socket file at the path.
//!
//! A connect reaches the abstract socket first (Linux) and, when none
//! listens, a socket file at the path: an earlier release's daemon, or
//! another program's socket. Both ends apply the compiled core's rules to
//! the other end: a listener drops a peer of another uid before a frame is
//! read. A client refuses a socket file's listener of another uid (the
//! file's private dir keeps other users out), and an abstract endpoint's
//! listener unless it runs as this uid and is the process recorded for the
//! endpoint: any user can bind a free abstract name first, so the listener
//! records its pid beside the name's path ([`record_path`]) once bound.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::time::Duration;

use anyhow::Result;

use super::access::{current_uid, PeerRule, PeerRules, PeerVerdict, ServerVerdict};

/// Whether eukhe's endpoints are socket files (`false` on Linux: abstract
/// sockets named by their path).
pub const ENDPOINTS_ARE_FILES: bool = cfg!(not(target_os = "linux"));

/// A full-duplex stream between a client and a daemon endpoint.
///
/// `split` consumes the boxed stream into its owned halves; concrete socket
/// types implement this, and callers hold only the erased halves.
pub trait TransportStream: Send + Sync {
    fn split(self: Box<Self>) -> (Box<dyn AsyncReadHalf>, Box<dyn AsyncWriteHalf>);
}

/// Owned read half of a [`TransportStream`]; blanket-implemented.
pub trait AsyncReadHalf: tokio::io::AsyncRead + Unpin + Send {}
impl<T> AsyncReadHalf for T where T: tokio::io::AsyncRead + Unpin + Send {}

/// Owned write half of a [`TransportStream`]; blanket-implemented.
pub trait AsyncWriteHalf: tokio::io::AsyncWrite + Unpin + Send {}
impl<T> AsyncWriteHalf for T where T: tokio::io::AsyncWrite + Unpin + Send {}

impl TransportStream for tokio::net::UnixStream {
    fn split(self: Box<Self>) -> (Box<dyn AsyncReadHalf>, Box<dyn AsyncWriteHalf>) {
        let (reader, writer) = tokio::net::UnixStream::into_split(*self);
        (Box::new(reader), Box::new(writer))
    }
}

/// Future returned by [`TransportListener::accept`].
pub type AcceptFuture<'a> =
    Pin<Box<dyn Future<Output = std::io::Result<Box<dyn TransportStream>>> + Send + 'a>>;

/// A bound transport endpoint that hands out connected streams.
pub trait TransportListener: Send + Sync {
    /// Future-boxed so the trait stays dyn-compatible (RPITIT methods are not);
    /// the future borrows the listener for the duration of the accept.
    fn accept(&self) -> AcceptFuture<'_>;
}

/// A bound socket whose accept applies a peer rule.
struct PeerListener {
    listener: tokio::net::UnixListener,
    peers: PeerRule,
    /// The pid record this listener wrote (abstract endpoints), removed
    /// when it closes while it still names this process.
    record: Option<PathBuf>,
}

impl Drop for PeerListener {
    fn drop(&mut self) {
        if let Some(record) = &self.record {
            if read_record(record) == std::process::id() {
                let _ = std::fs::remove_file(record);
            }
        }
    }
}

/// Every accepted connection passes the listener's peer rule (the one
/// [`bind_transport`] was given): a peer the rule drops (or one whose
/// credentials cannot be read) is closed before a frame is read, with a
/// warning, and the accept waits for the next peer. This one place covers
/// the supervisor socket and every worker socket.
impl TransportListener for PeerListener {
    fn accept(&self) -> AcceptFuture<'_> {
        Box::pin(async move {
            let own_uid = current_uid();
            loop {
                let (stream, _address) = self.listener.accept().await?;
                match stream.peer_cred() {
                    Ok(credentials) => match (self.peers)(credentials.uid(), own_uid) {
                        PeerVerdict::Accept => {
                            return Ok(Box::new(stream) as Box<dyn TransportStream>);
                        }
                        PeerVerdict::Drop => tracing::warn!(
                            peer_uid = credentials.uid(),
                            own_uid,
                            "dropped a socket peer of another uid"
                        ),
                    },
                    Err(error) => tracing::warn!(
                        %error,
                        "dropped a socket peer whose credentials cannot be read"
                    ),
                }
            }
        })
    }
}

/// The longest abstract socket name: `sun_path` (108 bytes) less the
/// leading NUL that marks the name abstract.
#[cfg(target_os = "linux")]
const MAX_ABSTRACT_NAME: usize = 107;

/// The abstract address of `path` in the form tokio and socket2 take: a
/// NUL, then the path's bytes.
///
/// # Errors
///
/// The path is longer than an abstract name may be.
#[cfg(target_os = "linux")]
fn abstract_address(path: &Path) -> std::io::Result<PathBuf> {
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    let bytes = path.as_os_str().as_bytes();
    if bytes.len() > MAX_ABSTRACT_NAME {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!(
                "socket path exceeds the {MAX_ABSTRACT_NAME}-byte limit of an abstract socket name: {}",
                path.display()
            ),
        ));
    }
    let mut name = Vec::with_capacity(bytes.len() + 1);
    name.push(0);
    name.extend_from_slice(bytes);
    Ok(PathBuf::from(std::ffi::OsString::from_vec(name)))
}

/// The abstract name of `path` as std takes it.
#[cfg(target_os = "linux")]
fn abstract_std_address(path: &Path) -> std::io::Result<std::os::unix::net::SocketAddr> {
    use std::os::linux::net::SocketAddrExt;
    use std::os::unix::ffi::OsStrExt;
    let address = abstract_address(path)?;
    std::os::unix::net::SocketAddr::from_abstract_name(&address.as_os_str().as_bytes()[1..])
}

/// `AF_UNIX` `sun_path` capacity less its terminating NUL: 108 bytes on
/// Linux, 104 on macOS (`sys/un.h`).
#[cfg(target_os = "linux")]
const MAX_SUN_PATH: usize = 107;
#[cfg(not(target_os = "linux"))]
const MAX_SUN_PATH: usize = 103;

/// A kernel-valid `AF_UNIX` address of a socket file for `bind`/`connect`.
///
/// Paths within the limit pass through unchanged. On Linux a longer path is
/// re-anchored through an `O_PATH` descriptor on its parent directory
/// (`/proc/self/fd/<fd>/<file name>`): the socket file stays at the
/// original (deep) location while the address handed to the kernel stays
/// short (an earlier release's daemon under a deep `TMPDIR`). Other
/// platforms surface the natural path-length error.
struct UnixSocketAddress {
    address: PathBuf,
    /// Holds the directory descriptor open for the address lifetime; the
    /// re-anchored `/proc/self/fd` path is valid only while this lives.
    _dir: Option<std::fs::File>,
}

impl UnixSocketAddress {
    /// The effective address to hand to `bind`/`connect`.
    fn effective(&self) -> &Path {
        &self.address
    }

    /// Resolve `path` into a kernel-valid `AF_UNIX` address, or fail with the
    /// original path in the message.
    fn new(path: &Path) -> std::io::Result<Self> {
        if path.as_os_str().len() <= MAX_SUN_PATH {
            return Ok(Self {
                address: path.to_path_buf(),
                _dir: None,
            });
        }
        #[cfg(target_os = "linux")]
        {
            let (address, dir) = Self::through_dir_fd(path)?;
            Ok(Self {
                address,
                _dir: Some(dir),
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            Err(too_long(path))
        }
    }

    /// Re-anchor a too-long path through `/proc/self/fd/<dir fd>/<file name>`.
    #[cfg(target_os = "linux")]
    fn through_dir_fd(path: &Path) -> std::io::Result<(PathBuf, std::fs::File)> {
        use std::os::fd::AsRawFd;
        use std::os::unix::fs::OpenOptionsExt;
        // `O_PATH` (Linux `asm-generic`): an fd that references the directory
        // without read/write access; only `/proc/self/fd` traversal uses it.
        const O_PATH: i32 = 0o200_000;
        let (Some(name), Some(parent)) = (path.file_name(), path.parent()) else {
            return Err(too_long(path));
        };
        let dir = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(O_PATH)
            .open(parent)?;
        let address = PathBuf::from(format!(
            "/proc/self/fd/{}/{}",
            dir.as_raw_fd(),
            name.to_string_lossy()
        ));
        if address.as_os_str().len() > MAX_SUN_PATH {
            return Err(too_long(path));
        }
        Ok((address, dir))
    }
}

/// The error of a socket file path no address can name.
fn too_long(path: &Path) -> std::io::Error {
    std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        format!(
            "AF_UNIX socket path exceeds the {MAX_SUN_PATH}-byte limit: {}",
            path.display()
        ),
    )
}

/// The longest path [`bind_transport`] binds, in bytes: an abstract
/// name's (Linux), else a socket file address's.
#[cfg(target_os = "linux")]
pub const ENDPOINT_NAME_LIMIT: usize = MAX_ABSTRACT_NAME;
#[cfg(not(target_os = "linux"))]
pub const ENDPOINT_NAME_LIMIT: usize = MAX_SUN_PATH;

/// Whether `path` can name an endpoint [`bind_transport`] binds: an
/// abstract name (Linux), else a socket file address.
#[must_use]
pub fn is_addressable(path: &Path) -> bool {
    path.as_os_str().len() <= ENDPOINT_NAME_LIMIT
}

/// Bind a listening endpoint at `path` whose accept applies `peers` to
/// each connected peer. An abstract endpoint (Linux) records this
/// process's pid at [`record_path`] once bound; the record goes when the
/// listener closes.
///
/// # Errors
///
/// Returns an error if `path` cannot name an endpoint, if binding the
/// listener fails (another listener holds the name), or if the pid cannot
/// be recorded.
pub async fn bind_transport(path: &Path, peers: PeerRule) -> Result<Box<dyn TransportListener>> {
    let listener = bind_tokio(path)?;
    let record = (!ENDPOINTS_ARE_FILES).then(|| record_path(path));
    Ok(Box::new(PeerListener {
        listener,
        peers,
        record,
    }))
}

/// Bind the endpoint at `path` as a bare tokio listener, with no peer rule
/// (a test's stand-in daemon); inside a tokio runtime. An abstract
/// endpoint (Linux) records this process's pid at [`record_path`].
///
/// # Errors
///
/// `path` cannot name an endpoint, the bind fails, or the pid cannot be
/// recorded.
pub fn bind_tokio(path: &Path) -> std::io::Result<tokio::net::UnixListener> {
    #[cfg(target_os = "linux")]
    {
        let listener = tokio::net::UnixListener::bind(abstract_address(path)?)?;
        write_record(path)?;
        Ok(listener)
    }
    #[cfg(not(target_os = "linux"))]
    {
        tokio::net::UnixListener::bind(UnixSocketAddress::new(path)?.effective())
    }
}

/// Bind the endpoint at `path` as a bare blocking std listener, with no
/// peer rule (a test's stand-in daemon). An abstract endpoint (Linux)
/// records this process's pid at [`record_path`].
///
/// # Errors
///
/// `path` cannot name an endpoint, the bind fails, or the pid cannot be
/// recorded.
pub fn bind_std(path: &Path) -> std::io::Result<std::os::unix::net::UnixListener> {
    #[cfg(target_os = "linux")]
    {
        let listener = std::os::unix::net::UnixListener::bind_addr(&abstract_std_address(path)?)?;
        write_record(path)?;
        Ok(listener)
    }
    #[cfg(not(target_os = "linux"))]
    {
        std::os::unix::net::UnixListener::bind(UnixSocketAddress::new(path)?.effective())
    }
}

/// Where the listener of the abstract endpoint `path` records its pid:
/// `<file name>.pid` beside the path (in eukhe's run dir for its default
/// endpoints, a dir only this user reaches).
#[must_use]
pub fn record_path(path: &Path) -> PathBuf {
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(".pid");
    path.with_file_name(name)
}

/// The pid recorded at `record`: 0 when none is (no file, not a regular
/// file, or no pid in it).
fn read_record(record: &Path) -> u32 {
    let is_file = std::fs::symlink_metadata(record).is_ok_and(|metadata| metadata.is_file());
    if !is_file {
        return 0;
    }
    std::fs::read_to_string(record)
        .ok()
        .and_then(|text| text.trim().parse().ok())
        .unwrap_or(0)
}

/// Record this process's pid for the endpoint `path`: a private file
/// written whole beside the record, then renamed over it.
#[cfg(target_os = "linux")]
fn write_record(path: &Path) -> std::io::Result<()> {
    use std::io::Write;
    use std::os::unix::fs::OpenOptionsExt;
    let record = record_path(path);
    let mut name = record.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{}.tmp", std::process::id()));
    let staged = record.with_file_name(name);
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(super::access::PRIVATE_FILE_MODE)
        .open(&staged)?;
    file.write_all(format!("{}\n", std::process::id()).as_bytes())?;
    drop(file);
    std::fs::rename(&staged, &record)
}

/// Connect to the endpoint at `path`: its abstract socket (Linux), else a
/// socket file there. No rule: the caller checks the peer, or is a test or
/// a probe that sends nothing.
///
/// # Errors
///
/// Nothing listens at `path`, or the connect fails.
pub async fn connect_tokio(path: &Path) -> std::io::Result<tokio::net::UnixStream> {
    connect_tokio_reached(path).await.map(|(stream, _)| stream)
}

/// [`connect_tokio`], and whether it reached an abstract socket.
async fn connect_tokio_reached(path: &Path) -> std::io::Result<(tokio::net::UnixStream, bool)> {
    #[cfg(target_os = "linux")]
    {
        let abstract_error = match abstract_address(path) {
            Ok(address) => match tokio::net::UnixStream::connect(address).await {
                Ok(stream) => return Ok((stream, true)),
                Err(error) => error,
            },
            Err(error) => error,
        };
        if !super::endpoints::is_socket_file(path) {
            return Err(no_endpoint(abstract_error));
        }
    }
    let stream = tokio::net::UnixStream::connect(UnixSocketAddress::new(path)?.effective()).await?;
    Ok((stream, false))
}

/// The error of an abstract connect at a path with no socket file: a
/// refused connect means nothing listens at that name, reported as a
/// missing socket file was (`ENOENT`).
#[cfg(target_os = "linux")]
fn no_endpoint(error: std::io::Error) -> std::io::Error {
    if error.kind() == std::io::ErrorKind::ConnectionRefused {
        std::io::Error::from_raw_os_error(libc::ENOENT)
    } else {
        error
    }
}

/// [`connect_tokio`], blocking.
///
/// # Errors
///
/// Nothing listens at `path`, or the connect fails.
pub fn connect_std(path: &Path) -> std::io::Result<std::os::unix::net::UnixStream> {
    connect_std_reached(path).map(|(stream, _)| stream)
}

/// [`connect_std`], and whether it reached an abstract socket.
fn connect_std_reached(path: &Path) -> std::io::Result<(std::os::unix::net::UnixStream, bool)> {
    #[cfg(target_os = "linux")]
    {
        let abstract_error = match abstract_std_address(path) {
            Ok(address) => match std::os::unix::net::UnixStream::connect_addr(&address) {
                Ok(stream) => return Ok((stream, true)),
                Err(error) => error,
            },
            Err(error) => error,
        };
        if !super::endpoints::is_socket_file(path) {
            return Err(no_endpoint(abstract_error));
        }
    }
    let stream =
        std::os::unix::net::UnixStream::connect(UnixSocketAddress::new(path)?.effective())?;
    Ok((stream, false))
}

/// The refusal of a listener whose uid the peer rule drops.
fn foreign_listener(path: &Path, uid: u32) -> std::io::Error {
    std::io::Error::new(
        std::io::ErrorKind::PermissionDenied,
        format!(
            "the socket {} is served by uid {uid}, not by this user (uid {})",
            path.display(),
            current_uid()
        ),
    )
}

/// How long a client waits for the listener of an abstract endpoint to
/// record its pid (it records once bound), and how often it looks again.
const RECORD_WAIT: Duration = Duration::from_millis(500);
const RECORD_POLL: Duration = Duration::from_millis(10);

/// The refusal of the listener of the abstract endpoint `path` the server
/// rule did not accept.
fn server_refusal(
    path: &Path,
    verdict: ServerVerdict,
    uid: u32,
    pid: u32,
    recorded: u32,
) -> std::io::Error {
    let why = match verdict {
        ServerVerdict::OtherUid => return foreign_listener(path, uid),
        ServerVerdict::Served => format!("the socket {} is served", path.display()),
        ServerVerdict::NoRecord => format!(
            "the socket {} is served by pid {pid}, but no Eukhe process is recorded for it in {}",
            path.display(),
            record_path(path).display()
        ),
        ServerVerdict::OtherPid => format!(
            "the socket {} is served by pid {pid}, not by the Eukhe process recorded for it (pid {recorded})",
            path.display()
        ),
    };
    std::io::Error::new(std::io::ErrorKind::PermissionDenied, why)
}

/// The server rule's verdict on a listener of `uid` and `pid` at the
/// abstract endpoint `path`, against the pid recorded now.
fn server_verdict(path: &Path, rules: PeerRules, uid: u32, pid: u32) -> (ServerVerdict, u32) {
    let recorded = read_record(&record_path(path));
    ((rules.server)(uid, current_uid(), pid, recorded), recorded)
}

/// Whether to look at the record again: a listener that has just bound
/// may not have recorded its pid yet.
fn record_pending(verdict: ServerVerdict) -> bool {
    matches!(verdict, ServerVerdict::NoRecord | ServerVerdict::OtherPid)
}

/// Apply `rules` to the listener behind a connected stream: the server
/// rule at an abstract endpoint (waiting up to [`RECORD_WAIT`] for its
/// record), the peer rule at a socket file.
async fn check_listener(
    path: &Path,
    rules: PeerRules,
    is_abstract: bool,
    uid: u32,
    pid: u32,
) -> std::io::Result<()> {
    if !is_abstract {
        return match (rules.peer)(uid, current_uid()) {
            PeerVerdict::Accept => Ok(()),
            PeerVerdict::Drop => Err(foreign_listener(path, uid)),
        };
    }
    let deadline = tokio::time::Instant::now() + RECORD_WAIT;
    loop {
        let (verdict, recorded) = server_verdict(path, rules, uid, pid);
        match verdict {
            ServerVerdict::Served => return Ok(()),
            pending if record_pending(pending) && tokio::time::Instant::now() < deadline => {
                tokio::time::sleep(RECORD_POLL).await;
            }
            refused => return Err(server_refusal(path, refused, uid, pid, recorded)),
        }
    }
}

/// [`check_listener`], blocking.
fn check_listener_blocking(
    path: &Path,
    rules: PeerRules,
    is_abstract: bool,
    uid: u32,
    pid: u32,
) -> std::io::Result<()> {
    if !is_abstract {
        return match (rules.peer)(uid, current_uid()) {
            PeerVerdict::Accept => Ok(()),
            PeerVerdict::Drop => Err(foreign_listener(path, uid)),
        };
    }
    let deadline = std::time::Instant::now() + RECORD_WAIT;
    loop {
        let (verdict, recorded) = server_verdict(path, rules, uid, pid);
        match verdict {
            ServerVerdict::Served => return Ok(()),
            pending if record_pending(pending) && std::time::Instant::now() < deadline => {
                std::thread::sleep(RECORD_POLL);
            }
            refused => return Err(server_refusal(path, refused, uid, pid, recorded)),
        }
    }
}

/// Connect to the endpoint at `path` asynchronously; a listener `rules`
/// do not accept is refused before a frame.
///
/// # Errors
///
/// Returns an error if nothing listens at `path`, the connect fails, the
/// listener's credentials cannot be read, or `rules` refuse it.
pub async fn connect_transport(path: &Path, rules: PeerRules) -> Result<Box<dyn TransportStream>> {
    let (stream, _pid) = connect_checked(path, rules).await?;
    Ok(Box::new(stream))
}

/// The pid of the process listening at the endpoint `path`, once `rules`
/// accept it (0 where the platform does not report a listener's pid);
/// `None` when nothing listens there.
///
/// # Errors
///
/// The connect fails other than for want of a listener, the listener's
/// credentials cannot be read, or `rules` refuse it.
pub async fn listener_pid(path: &Path, rules: PeerRules) -> std::io::Result<Option<u32>> {
    match connect_checked(path, rules).await {
        Ok((_stream, pid)) => Ok(Some(pid)),
        Err(error)
            if matches!(
                error.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::ConnectionRefused
            ) =>
        {
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Connect to the endpoint at `path` and apply `rules` to its listener;
/// the stream and the listener's pid (0 where the platform does not
/// report it).
async fn connect_checked(
    path: &Path,
    rules: PeerRules,
) -> std::io::Result<(tokio::net::UnixStream, u32)> {
    let (stream, is_abstract) = connect_tokio_reached(path).await?;
    let credentials = stream.peer_cred()?;
    let pid = credentials
        .pid()
        .and_then(|pid| u32::try_from(pid).ok())
        .unwrap_or(0);
    check_listener(path, rules, is_abstract, credentials.uid(), pid).await?;
    Ok((stream, pid))
}

/// The uid and pid of the process at the other end of `stream` (the pid
/// is 0 where the platform does not report it).
fn std_peer_credentials(stream: &std::os::unix::net::UnixStream) -> std::io::Result<(u32, u32)> {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        nix::sys::socket::getsockopt(stream, nix::sys::socket::sockopt::PeerCredentials)
            .map(|credentials| {
                (
                    credentials.uid(),
                    u32::try_from(credentials.pid()).unwrap_or(0),
                )
            })
            .map_err(std::io::Error::from)
    }
    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    {
        nix::unistd::getpeereid(stream)
            .map(|(uid, _gid)| (uid.as_raw(), 0))
            .map_err(std::io::Error::from)
    }
}

/// Definitive nonblocking refusal of the socket file at `path`, used by the
/// exit cleanup before it unlinks the file. A saturated backlog can yield
/// `EAGAIN` on Linux rather than a completed connect. Only
/// `ConnectionRefused` permits unlink; all unknown outcomes fail closed.
/// Reuse the transport's long-path re-anchor so deep socket paths retain
/// their stale-cleanup behavior.
///
/// The refused verdict is definitive on Linux only: on macOS and the BSDs a
/// saturated listen queue ALSO refuses the connect, so a live successor that
/// filled its backlog is indistinguishable from a dead path by this probe.
/// There the function never claims closure (the exit cleanup preserves the
/// path; the next bind's stale-socket prepare cleans a file nothing serves).
#[must_use]
pub fn unix_listener_definitely_closed(path: &Path) -> bool {
    #[cfg(not(target_os = "linux"))]
    {
        let _ = path;
        false
    }
    #[cfg(target_os = "linux")]
    {
        let Ok(effective) = UnixSocketAddress::new(path) else {
            return false;
        };
        let Ok(address) = socket2::SockAddr::unix(effective.effective()) else {
            return false;
        };
        let Ok(socket) = socket2::Socket::new(socket2::Domain::UNIX, socket2::Type::STREAM, None)
        else {
            return false;
        };
        if socket.set_nonblocking(true).is_err() {
            return false;
        }
        matches!(
            socket.connect(&address),
            Err(error) if error.kind() == std::io::ErrorKind::ConnectionRefused
        )
    }
}

/// A blocking full-duplex stream, for the CLI's one-shot command client.
pub trait BlockingTransportStream:
    std::fmt::Debug + std::io::Read + std::io::Write + Send + Sync
{
    /// Duplicate the underlying handle so reads and writes can proceed on
    /// separate owned halves.
    ///
    /// # Errors
    ///
    /// Returns an error if the underlying handle cannot be duplicated.
    fn try_clone_box(&self) -> std::io::Result<Box<dyn BlockingTransportStream>>;
    /// Deadline a pending read (poll granularity for deadline-driven waits).
    ///
    /// # Errors
    ///
    /// Returns an error if setting the read deadline on the underlying
    /// stream fails.
    fn set_read_timeout(&self, timeout: std::time::Duration) -> std::io::Result<()>;
}

impl BlockingTransportStream for std::os::unix::net::UnixStream {
    fn try_clone_box(&self) -> std::io::Result<Box<dyn BlockingTransportStream>> {
        Ok(Box::new(self.try_clone()?))
    }

    fn set_read_timeout(&self, timeout: std::time::Duration) -> std::io::Result<()> {
        std::os::unix::net::UnixStream::set_read_timeout(self, Some(timeout))
    }
}

/// Connect to the endpoint at `path`, blocking until connected; a listener
/// `rules` do not accept is refused before a frame.
///
/// # Errors
///
/// Returns an error if nothing listens at `path`, the connect fails, the
/// listener's credentials cannot be read, or `rules` refuse it.
pub fn connect_blocking(
    path: &Path,
    rules: PeerRules,
) -> std::io::Result<Box<dyn BlockingTransportStream>> {
    let (stream, is_abstract) = connect_std_reached(path)?;
    let (uid, pid) = std_peer_credentials(&stream)?;
    check_listener_blocking(path, rules, is_abstract, uid, pid)?;
    Ok(Box::new(stream))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// These tests bind but never accept through the listener: its peer
    /// rule never runs.
    fn never_accepts(_: u32, _: u32) -> PeerVerdict {
        PeerVerdict::Drop
    }

    /// The rule of these tests: same uid only.
    fn same_uid(peer: u32, own: u32) -> PeerVerdict {
        if peer == own {
            PeerVerdict::Accept
        } else {
            PeerVerdict::Drop
        }
    }

    /// The server rule of these tests (the compiled core's, which
    /// eukhe-types does not link): this uid, a record, the recorded pid.
    fn recorded_own(peer: u32, own: u32, pid: u32, recorded: u32) -> ServerVerdict {
        if peer != own {
            ServerVerdict::OtherUid
        } else if recorded == 0 {
            ServerVerdict::NoRecord
        } else if pid == recorded {
            ServerVerdict::Served
        } else {
            ServerVerdict::OtherPid
        }
    }

    fn never_served(_: u32, _: u32, _: u32, _: u32) -> ServerVerdict {
        ServerVerdict::OtherUid
    }

    /// This user's own listeners.
    const OWN: PeerRules = PeerRules {
        peer: same_uid,
        server: recorded_own,
    };

    /// No listener.
    const NONE: PeerRules = PeerRules {
        peer: never_accepts,
        server: never_served,
    };

    /// A directory whose full path length is exactly `target` bytes.
    ///
    /// The ambient `TMPDIR` can already be deep (this very harness keeps long
    /// temp paths), so the base falls back to `/tmp` when needed to stay short.
    fn dir_of_exact_len(tag: &str, target: usize) -> PathBuf {
        let tag = format!("pa-transport-sun-path-{tag}-{}", std::process::id());
        let base = std::env::temp_dir().join(&tag);
        let base = if base.as_os_str().len() + 21 <= target {
            base
        } else {
            Path::new("/tmp").join(&tag)
        };
        let mut dir = base;
        // Keep at least one byte of room for a file name after the separator,
        // and at least one byte for the final pad component (an empty pad
        // would join a trailing separator instead of a name).
        while dir.as_os_str().len() + 22 < target {
            dir = dir.join("d".repeat(20));
        }
        // Pad one final component: appending adds a separator plus the name.
        let pad = target
            .checked_sub(dir.as_os_str().len() + 1)
            .expect("base must leave room for a file name");
        dir = dir.join("d".repeat(pad));
        assert_eq!(dir.as_os_str().len(), target);
        std::fs::create_dir_all(&dir).expect("create deep dir");
        dir
    }

    /// On Linux an endpoint is an abstract socket: no file appears at its
    /// path, both connects reach it, and a second bind of the name fails.
    /// Elsewhere it is a socket file.
    #[tokio::test]
    async fn an_endpoint_binds_by_its_path_and_both_connects_reach_it() {
        use tokio::io::{AsyncReadExt, AsyncWriteExt};
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("daemon.sock");
        let listener = bind_transport(&socket, same_uid).await.expect("bind");
        assert_eq!(
            super::super::endpoints::is_socket_file(&socket),
            ENDPOINTS_ARE_FILES
        );
        assert!(bind_transport(&socket, never_accepts).await.is_err());
        let client = connect_transport(&socket, OWN).await.expect("connect");
        let server = listener.accept().await.expect("accept");
        let (_reader, mut writer) = server.split();
        writer.write_all(b"ping").await.expect("write");
        let (mut reader, _writer) = client.split();
        let mut buf = [0u8; 4];
        reader.read_exact(&mut buf).await.expect("read");
        assert_eq!(&buf, b"ping");
        let blocking = connect_blocking(&socket, OWN);
        assert!(blocking.is_ok(), "{blocking:?}");
        let _ = std::fs::remove_file(&socket);
    }

    /// A client refuses a listener whose uid the rule drops, before a frame.
    #[tokio::test]
    async fn a_client_refuses_a_listener_the_rule_drops() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("daemon.sock");
        let _listener = bind_tokio(&socket).expect("bind");
        let error = connect_transport(&socket, NONE)
            .await
            .err()
            .expect("refused");
        assert!(error.to_string().contains("not by this user"), "{error}");
        let error = connect_blocking(&socket, NONE).expect_err("refused");
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        let _ = std::fs::remove_file(&socket);
    }

    /// A socket file another program (or an earlier release) bound is
    /// reached when no abstract socket of that name listens.
    #[tokio::test]
    async fn a_socket_file_is_reached_when_no_abstract_socket_listens() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("legacy.sock");
        let _listener = tokio::net::UnixListener::bind(&socket).expect("bind a file");
        assert!(connect_transport(&socket, OWN).await.is_ok());
        assert!(connect_blocking(&socket, OWN).is_ok());
    }

    /// An abstract endpoint's listener records its pid once bound and
    /// takes the record away when it closes; a client accepts it only as
    /// the recorded process: a listener with no record, or another pid on
    /// record (a squatter of this uid), is refused, the error naming why.
    #[cfg(target_os = "linux")]
    #[tokio::test]
    async fn an_abstract_listener_is_accepted_only_as_the_recorded_process() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("daemon.sock");
        let record = record_path(&socket);
        assert_eq!(record, dir.path().join("daemon.sock.pid"));
        let listener = bind_transport(&socket, same_uid).await.expect("bind");
        assert_eq!(read_record(&record), std::process::id());
        assert!(connect_transport(&socket, OWN).await.is_ok());
        drop(listener);
        assert!(!record.exists());

        // A squatter: the name bound without a record.
        let _squatter =
            tokio::net::UnixListener::bind(abstract_address(&socket).expect("name")).expect("bind");
        let error = connect_transport(&socket, OWN)
            .await
            .err()
            .expect("refused");
        assert!(
            error.to_string().contains("no Eukhe process is recorded"),
            "{error}"
        );
        let error = connect_blocking(&socket, OWN).expect_err("refused");
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
        // Another pid on record.
        std::fs::write(&record, format!("{}\n", std::process::id() + 1)).expect("record");
        let error = connect_transport(&socket, OWN)
            .await
            .err()
            .expect("refused");
        assert!(
            error
                .to_string()
                .contains("not by the Eukhe process recorded"),
            "{error}"
        );
        // The squatter's own pid on record: it is this process.
        std::fs::write(&record, format!("{}\n", std::process::id())).expect("record");
        assert!(connect_transport(&socket, OWN).await.is_ok());
    }

    /// A client waits for a listener that bound but has not recorded its
    /// pid yet.
    #[cfg(target_os = "linux")]
    #[tokio::test]
    async fn a_client_waits_for_the_record_of_a_listener_that_just_bound() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let socket = dir.path().join("daemon.sock");
        let _listener =
            tokio::net::UnixListener::bind(abstract_address(&socket).expect("name")).expect("bind");
        let late = socket.clone();
        let recorder = tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(100)).await;
            write_record(&late).expect("record");
        });
        assert!(connect_transport(&socket, OWN).await.is_ok());
        recorder.await.expect("recorder");
    }

    /// The `/proc/self/fd` re-anchor of a deep socket file exists on Linux
    /// only.
    #[cfg(target_os = "linux")]
    #[tokio::test]
    async fn a_deep_socket_file_is_reached_through_its_dir() {
        let dir = dir_of_exact_len("deep", 120);
        let socket = dir.join("daemon.sock");
        let _ = std::fs::remove_file(&socket);
        assert!(socket.as_os_str().len() > MAX_SUN_PATH);
        let address = UnixSocketAddress::new(&socket).expect("re-anchor");
        let _listener = tokio::net::UnixListener::bind(address.effective()).expect("bind");
        assert!(super::super::endpoints::is_socket_file(&socket));
        assert!(connect_transport(&socket, OWN).await.is_ok());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A path past the name limit errors clearly.
    #[tokio::test]
    async fn an_endpoint_path_past_the_limit_errors_clearly() {
        let dir = dir_of_exact_len("toolong", 120);
        let socket = dir.join("n".repeat(120));
        let error = bind_transport(&socket, never_accepts)
            .await
            .err()
            .expect("no address names it");
        assert!(error.to_string().contains("exceeds"), "{error}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
