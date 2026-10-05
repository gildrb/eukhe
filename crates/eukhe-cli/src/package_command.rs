//! Package command validation and help, ported from
//! `package-manager-cli.ts` (`handlePackageCommand`, `parsePackageCommand`,
//! `printPackageCommandHelp`).

use eukhe_core::packages::{PackageManager, ProgressEvent, ProgressEventKind, UserOrProject};

use crate::config::{get_agent_dir, APP_NAME, CONFIG_DIR_NAME};

/// Result of running a package command: printed output is handled here, and the
/// exit code is reported for the caller to propagate.
#[derive(Debug, Clone)]
pub struct PackageCommandOutcome {
    pub exit_code: Option<i32>,
}

const HANDLED_OK: PackageCommandOutcome = PackageCommandOutcome { exit_code: None };

fn fail(message: &str, hint: Option<&str>) -> PackageCommandOutcome {
    // handlePackageCommand prints its errors without the "Error: " prefix.
    eprintln!("{message}");
    if let Some(hint) = hint {
        eprintln!("{hint}");
    }
    PackageCommandOutcome { exit_code: Some(1) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PackageCommand {
    Install,
    Remove,
    Update,
    List,
}

impl PackageCommand {
    fn usage(self) -> String {
        match self {
            PackageCommand::Install => format!("{APP_NAME} package install <source> [--local]"),
            PackageCommand::Remove => format!("{APP_NAME} package remove <source> [--local]"),
            PackageCommand::Update => format!("{APP_NAME} package update [source]"),
            PackageCommand::List => format!("{APP_NAME} package list"),
        }
    }
}

#[derive(Debug, Default)]
struct PackageCommandOptions {
    local: bool,
    help: bool,
    invalid_option: Option<String>,
    invalid_argument: Option<String>,
    source: Option<String>,
}

fn parse_package_command(args: &[String]) -> Option<PackageCommandOptions> {
    let command = match args.first().map(String::as_str) {
        Some("uninstall" | "remove") => Some(PackageCommand::Remove),
        Some("install") => Some(PackageCommand::Install),
        Some("update") => Some(PackageCommand::Update),
        Some("list") => Some(PackageCommand::List),
        _ => None,
    }?;
    let mut options = PackageCommandOptions::default();
    for arg in &args[1..] {
        let arg = arg.as_str();
        match arg {
            "-h" | "--help" => {
                options.help = true;
            }
            "--local" => {
                if matches!(command, PackageCommand::Install | PackageCommand::Remove) {
                    options.local = true;
                } else {
                    options
                        .invalid_option
                        .get_or_insert_with(|| arg.to_string());
                }
            }
            _ if arg.starts_with('-') => {
                options
                    .invalid_option
                    .get_or_insert_with(|| arg.to_string());
            }
            _ => {
                if options.source.is_none() {
                    options.source = Some(arg.to_string());
                } else {
                    options
                        .invalid_argument
                        .get_or_insert_with(|| arg.to_string());
                }
            }
        }
    }
    Some(options)
}

fn print_package_command_help(command: PackageCommand) {
    let usage = command.usage();
    match command {
        PackageCommand::Install => println!(
            "Usage:\n  {usage}\n\nInstall a package and add it to settings.\n\nOptions:\n  --local    Install project-locally ({CONFIG_DIR_NAME}/settings.json)\n\nExamples:\n  {APP_NAME} package install npm:@foo/bar\n  {APP_NAME} package install git:github.com/user/repo\n  {APP_NAME} package install git:git@github.com:user/repo\n  {APP_NAME} package install https://github.com/user/repo\n  {APP_NAME} package install ssh://git@github.com/user/repo\n  {APP_NAME} package install ./local/path\n"
        ),
        PackageCommand::Remove => println!(
            "Usage:\n  {usage}\n\nRemove a package and its source from settings.\n\nOptions:\n  --local    Remove from project settings ({CONFIG_DIR_NAME}/settings.json)\n\nExamples:\n  {APP_NAME} package remove npm:@foo/bar\n"
        ),
        PackageCommand::Update => println!(
            "Usage:\n  {usage}\n\nUpdate installed packages.\n\nCommands:\n  {APP_NAME} package update           Update installed packages\n  {APP_NAME} package update <source>  Update one package\n"
        ),
        PackageCommand::List => println!(
            "Usage:\n  {usage}\n\nList installed packages from user and project settings.\n"
        ),
    }
}

/// Run a package command, mirroring `handlePackageCommand`: validation and
/// help here, the package manager subsystem below.
pub fn handle_package_command(args: &[String]) -> PackageCommandOutcome {
    let Some(options) = parse_package_command(args) else {
        return PackageCommandOutcome { exit_code: None };
    };
    let command = match args.first().map(String::as_str) {
        Some("uninstall" | "remove") => PackageCommand::Remove,
        Some("install") => PackageCommand::Install,
        Some("update") => PackageCommand::Update,
        Some("list") => PackageCommand::List,
        _ => return PackageCommandOutcome { exit_code: None },
    };
    let command_name = match command {
        PackageCommand::Install => "install",
        PackageCommand::Remove => "remove",
        PackageCommand::Update => "update",
        PackageCommand::List => "list",
    };

    if options.help {
        print_package_command_help(command);
        return HANDLED_OK;
    }

    if let Some(invalid_option) = &options.invalid_option {
        if invalid_option == "-l"
            && matches!(command, PackageCommand::Install | PackageCommand::Remove)
        {
            return fail("Option -l was removed. Use \"--local\".", None);
        }
        return fail(
            &format!("Unknown option {invalid_option} for \"{command_name}\"."),
            Some(&format!(
                "Use \"{APP_NAME} --help\" or \"{}\".",
                command.usage()
            )),
        );
    }
    if let Some(invalid_argument) = &options.invalid_argument {
        return fail(
            &format!("Unexpected argument {invalid_argument}."),
            Some(&format!("Usage: {}", command.usage())),
        );
    }
    let source_missing = matches!(command, PackageCommand::Install | PackageCommand::Remove)
        && options.source.is_none();
    if source_missing {
        return fail(
            &format!("Missing {command_name} source."),
            Some(&format!("Usage: {}", command.usage())),
        );
    }

    // Everything past this point runs the package manager subsystem.
    let cwd = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
    let agent_dir = get_agent_dir();
    let mut settings = eukhe_core::settings::SettingsManager::create(&cwd, &agent_dir);
    report_settings_errors(&mut settings, "package command");

    let mut manager = PackageManager::new(cwd, agent_dir, settings);
    manager.set_progress_callback(Box::new(|event: &ProgressEvent| {
        if event.kind == ProgressEventKind::Start {
            if let Some(message) = &event.message {
                println!("{message}");
            }
        }
    }));

    let scope = if options.local {
        UserOrProject::Project
    } else {
        UserOrProject::User
    };

    // The TS `handlePackageCommand` shape: one outcome per case, the exit
    // code the case itself decides.
    match command {
        PackageCommand::Install => {
            let source = options.source.as_deref().expect("checked above");
            match manager.install_and_persist(source, scope) {
                Ok(()) => {
                    println!("Installed {source}");
                    HANDLED_OK
                }
                Err(error) => fail(&format!("Error: {error}"), None),
            }
        }
        PackageCommand::Remove => {
            let source = options.source.as_deref().expect("checked above");
            match manager.remove_and_persist(source, scope) {
                Ok(true) => {
                    println!("Removed {source}");
                    HANDLED_OK
                }
                Ok(false) => {
                    eprintln!("No matching package found for {source}");
                    PackageCommandOutcome { exit_code: Some(1) }
                }
                Err(error) => fail(&format!("Error: {error}"), None),
            }
        }
        PackageCommand::List => {
            print_package_list(&manager.list_configured_packages());
            HANDLED_OK
        }
        PackageCommand::Update => {
            let source = options.source.as_deref();
            if let Err(error) = manager.update(source) {
                return fail(&format!("Error: {error}"), None);
            }
            match source {
                Some(source) => println!("Updated {source}"),
                None => println!("Updated packages"),
            }
            HANDLED_OK
        }
    }
}

/// Print the configured package list (user section, then project section).
fn print_package_list(packages: &[eukhe_core::packages::ConfiguredPackage]) {
    if packages.is_empty() {
        println!("No packages installed.");
        return;
    }
    let user_packages: Vec<_> = packages
        .iter()
        .filter(|package| package.scope == UserOrProject::User)
        .collect();
    let project_packages: Vec<_> = packages
        .iter()
        .filter(|package| package.scope == UserOrProject::Project)
        .collect();
    if !user_packages.is_empty() {
        println!("User packages:");
        for package in &user_packages {
            print_configured_package(package);
        }
    }
    if !project_packages.is_empty() {
        if !user_packages.is_empty() {
            println!();
        }
        println!("Project packages:");
        for package in &project_packages {
            print_configured_package(package);
        }
    }
}

fn print_configured_package(package: &eukhe_core::packages::ConfiguredPackage) {
    let display = if package.filtered {
        format!("{} (filtered)", package.source)
    } else {
        package.source.clone()
    };
    println!("  {display}");
    if let Some(installed_path) = &package.installed_path {
        println!("    {}", installed_path.display());
    }
}

/// Print settings-load warnings exactly once (`Warning (<context>, <scope>
/// settings): <message>`).
pub(crate) fn report_settings_errors(
    settings: &mut eukhe_core::settings::SettingsManager,
    context: &str,
) {
    for error in settings.drain_errors() {
        let scope = match error.scope {
            eukhe_core::settings::SettingsScope::Global => "global",
            eukhe_core::settings::SettingsScope::Project => "project",
        };
        eprintln!("Warning ({context}, {scope} settings): {}", error.message);
    }
}
