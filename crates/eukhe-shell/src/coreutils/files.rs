//! `ls`, `mkdir`, `rm`, `rmdir`, `touch`, `cp`, `mv`.

use std::path::Path;

use super::{flags, reason, Output};

/// `ls` with `-1`, `-a`, `-A`: one name per line, as when its output is
/// not a terminal.
pub(super) fn ls(args: &[String], cwd: &Path) -> Option<Output> {
    let (set, operands) = flags(args, "1aA")?;
    let dot = ".".to_string();
    let mut operands = if operands.is_empty() {
        vec![&dot]
    } else {
        operands
    };
    operands.sort();
    let mut out = Output::default();
    let (mut files, mut dirs) = (Vec::new(), Vec::new());
    for operand in operands {
        match std::fs::metadata(cwd.join(operand)) {
            Ok(meta) if meta.is_dir() => dirs.push(operand),
            Ok(_) => files.push(operand),
            Err(error) => out.fail(
                "ls",
                &format!("cannot access '{operand}': {}", reason(&error)),
                2,
            ),
        }
    }
    let headers = files.len() + dirs.len() > 1;
    let mut sections = Vec::new();
    if !files.is_empty() {
        sections.push(
            files
                .iter()
                .flat_map(|file| {
                    [
                        file.as_str(),
                        "
",
                    ]
                })
                .collect::<String>(),
        );
    }
    for dir in dirs {
        match std::fs::read_dir(cwd.join(dir)) {
            Ok(entries) => {
                let mut names: Vec<String> = entries
                    .filter_map(Result::ok)
                    .map(|entry| entry.file_name().to_string_lossy().into_owned())
                    .filter(|name| !name.starts_with('.') || set.contains('a') || set.contains('A'))
                    .collect();
                names.sort();
                if set.contains('a') {
                    names.splice(0..0, [".".to_string(), "..".to_string()]);
                }
                let listing: String = names
                    .iter()
                    .flat_map(|name| {
                        [
                            name.as_str(),
                            "
",
                        ]
                    })
                    .collect();
                sections.push(if headers {
                    format!("{dir}:\n{listing}")
                } else {
                    listing
                });
            }
            Err(error) => out.fail(
                "ls",
                &format!("cannot open directory '{dir}': {}", reason(&error)),
                2,
            ),
        }
    }
    out.stdout = sections.join("\n").into_bytes();
    Some(out)
}

pub(super) fn mkdir(args: &[String], cwd: &Path) -> Option<Output> {
    let (set, operands) = flags(args, "p")?;
    let mut out = Output::default();
    for operand in operands {
        let path = cwd.join(operand);
        let made = if set.contains('p') {
            std::fs::create_dir_all(&path)
        } else {
            std::fs::create_dir(&path)
        };
        if let Err(error) = made {
            out.fail(
                "mkdir",
                &format!("cannot create directory '{operand}': {}", reason(&error)),
                1,
            );
        }
    }
    Some(out)
}

pub(super) fn rm(args: &[String], cwd: &Path) -> Option<Output> {
    let (set, operands) = flags(args, "rRf")?;
    let recursive = set.contains('r') || set.contains('R');
    let force = set.contains('f');
    let mut out = Output::default();
    for operand in operands {
        let path = cwd.join(operand);
        if recursive && std::fs::canonicalize(&path).is_ok_and(|real| real.parent().is_none()) {
            out.fail(
                "rm",
                &format!("it is dangerous to operate recursively on '{operand}'"),
                1,
            );
            continue;
        }
        let removed = match std::fs::symlink_metadata(&path) {
            Ok(meta) if meta.is_dir() && recursive => std::fs::remove_dir_all(&path),
            Ok(meta) if meta.is_dir() => Err(std::io::ErrorKind::IsADirectory.into()),
            Ok(_) => std::fs::remove_file(&path),
            Err(error) => Err(error),
        };
        match removed {
            Ok(()) => {}
            Err(error) if force && error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => out.fail(
                "rm",
                &format!("cannot remove '{operand}': {}", reason(&error)),
                1,
            ),
        }
    }
    Some(out)
}

pub(super) fn rmdir(args: &[String], cwd: &Path) -> Option<Output> {
    let (_, operands) = flags(args, "")?;
    let mut out = Output::default();
    for operand in operands {
        if let Err(error) = std::fs::remove_dir(cwd.join(operand)) {
            out.fail(
                "rmdir",
                &format!("failed to remove '{operand}': {}", reason(&error)),
                1,
            );
        }
    }
    Some(out)
}

pub(super) fn touch(args: &[String], cwd: &Path) -> Option<Output> {
    let (_, operands) = flags(args, "")?;
    let mut out = Output::default();
    for operand in operands {
        let touched = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(cwd.join(operand))
            .and_then(|file| file.set_modified(std::time::SystemTime::now()));
        if let Err(error) = touched {
            out.fail(
                "touch",
                &format!("cannot touch '{operand}': {}", reason(&error)),
                1,
            );
        }
    }
    Some(out)
}

/// Copy `from` to `to`, directories whole.
fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    if std::fs::metadata(from)?.is_dir() {
        std::fs::create_dir_all(to)?;
        for entry in std::fs::read_dir(from)? {
            let entry = entry?;
            copy_tree(&entry.path(), &to.join(entry.file_name()))?;
        }
        Ok(())
    } else {
        std::fs::copy(from, to).map(|_| ())
    }
}

/// The sources and where each goes: into the last operand when it is a
/// directory, else onto it (one source only).
fn moves<'a>(
    name: &str,
    operands: &[&'a String],
    cwd: &Path,
    out: &mut Output,
) -> Vec<(&'a String, std::path::PathBuf)> {
    let Some((target, sources)) = operands.split_last() else {
        out.fail(name, "missing file operand", 1);
        return Vec::new();
    };
    if sources.is_empty() {
        out.fail(
            name,
            &format!("missing destination file operand after '{target}'"),
            1,
        );
        return Vec::new();
    }
    let target_path = cwd.join(target);
    if target_path.is_dir() {
        sources
            .iter()
            .map(|source| {
                let file = Path::new(source.as_str())
                    .file_name()
                    .map_or_else(|| target_path.clone(), |file| target_path.join(file));
                (*source, file)
            })
            .collect()
    } else if let [source] = sources {
        vec![(*source, target_path)]
    } else {
        out.fail(name, &format!("target '{target}': Not a directory"), 1);
        Vec::new()
    }
}

pub(super) fn cp(args: &[String], cwd: &Path) -> Option<Output> {
    let (set, operands) = flags(args, "rR")?;
    let recursive = set.contains('r') || set.contains('R');
    let mut out = Output::default();
    for (source, target) in moves("cp", &operands, cwd, &mut out) {
        let from = cwd.join(source);
        if !recursive && from.is_dir() {
            out.fail(
                "cp",
                &format!("-r not specified; omitting directory '{source}'"),
                1,
            );
            continue;
        }
        if let Err(error) = copy_tree(&from, &target) {
            out.fail(
                "cp",
                &format!("cannot copy '{source}': {}", reason(&error)),
                1,
            );
        }
    }
    Some(out)
}

pub(super) fn mv(args: &[String], cwd: &Path) -> Option<Output> {
    let (_, operands) = flags(args, "")?;
    let mut out = Output::default();
    for (source, target) in moves("mv", &operands, cwd, &mut out) {
        if let Err(error) = std::fs::rename(cwd.join(source), &target) {
            out.fail(
                "mv",
                &format!("cannot move '{source}': {}", reason(&error)),
                1,
            );
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::super::captured;
    use super::*;

    fn argv(words: &[&str]) -> Vec<String> {
        words.iter().map(ToString::to_string).collect()
    }

    fn stdout(text: &str) -> Output {
        Output {
            stdout: text.as_bytes().to_vec(),
            ..Output::default()
        }
    }

    #[test]
    fn file_commands_change_the_tree_and_list_it() {
        let dir = tempfile::tempdir().unwrap();
        let cwd = dir.path();
        let steps: Vec<Option<Output>> = [
            &["mkdir", "-p", "a/b"][..],
            &["touch", "a/b/f", "g"],
            &["cp", "-r", "a", "c"],
            &["mv", "g", "a"],
            &["ls", "a", "c/b", "g"],
            &["rm", "a/b"],
            &["rm", "-rf", "a/b", "missing"],
            &["rmdir", "c"],
            &["ls", "-la"],
        ]
        .iter()
        .map(|words| captured(&argv(words), cwd, b""))
        .collect();
        assert_eq!(
            steps,
            vec![
                Some(Output::default()),
                Some(Output::default()),
                Some(Output::default()),
                Some(Output::default()),
                Some(Output {
                    stdout: b"a:\nb\ng\n\nc/b:\nf\n".to_vec(),
                    stderr: b"ls: cannot access 'g': No such file or directory\n".to_vec(),
                    status: 2,
                }),
                Some(Output {
                    stderr: b"rm: cannot remove 'a/b': Is a directory\n".to_vec(),
                    status: 1,
                    ..Output::default()
                }),
                Some(Output::default()),
                Some(Output {
                    stderr: b"rmdir: failed to remove 'c': Directory not empty\n".to_vec(),
                    status: 1,
                    ..Output::default()
                }),
                None,
            ]
        );
        assert_eq!(
            captured(&argv(&["ls", "-a"]), cwd, b""),
            Some(stdout(".\n..\na\nc\n"))
        );
    }
}
