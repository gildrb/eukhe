//! The session's Python skills split for the kernel: which skills the
//! kernel installs and pre-imports at bootstrap, and which an untrusted
//! project keeps out.

use crate::kernel::bootstrap::KernelPythonSkill;
use crate::settings::TrustLevel;
use crate::skills::{Skill, SkillKind, SourceScope};

/// The session's Python skills split for the kernel: the ones it installs
/// and pre-imports at bootstrap, and the names of the project skills an
/// untrusted project kept out (their `SKILL.md` text still reaches the
/// prompt).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelPythonSkills {
    pub admitted: Vec<KernelPythonSkill>,
    pub withheld: Vec<String>,
}

/// Kernel-side Python skill modules: a project-scope skill (auto-discovered
/// from `<cwd>/.eukhe/skills` or an ancestor `.agents/skills`, a project
/// `skills` entry, or a project package) runs its build backend on install
/// and its module on import, so it is admitted only for a trusted project.
#[must_use]
pub fn kernel_python_skills(skills: &[Skill], trust: TrustLevel) -> KernelPythonSkills {
    let mut kernel = KernelPythonSkills {
        admitted: Vec::new(),
        withheld: Vec::new(),
    };
    for skill in skills {
        let (SkillKind::Python, Some(python)) = (skill.kind, &skill.python) else {
            continue;
        };
        match (skill.source_info.scope, trust) {
            (SourceScope::Project, TrustLevel::Untrusted) => {
                kernel.withheld.push(skill.name.clone());
            }
            (SourceScope::Project, TrustLevel::Trusted)
            | (SourceScope::User | SourceScope::Temporary, _) => {
                kernel.admitted.push(KernelPythonSkill {
                    name: skill.name.clone(),
                    import_name: python.import_name.clone(),
                    package_path: python.package_path.clone(),
                    pyproject_path: python.pyproject_path.clone(),
                });
            }
        }
    }
    kernel
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{kernel_python_skills, KernelPythonSkills};
    use crate::kernel::bootstrap::KernelPythonSkill;
    use crate::settings::TrustLevel;
    use crate::skills::{
        Skill, SkillKind, SkillPythonMetadata, SourceInfo, SourceOrigin, SourceScope,
    };

    fn python_skill(name: &str, scope: SourceScope) -> Skill {
        let dir = PathBuf::from(format!("/skills/{name}"));
        Skill {
            name: name.to_string(),
            description: "d".to_string(),
            file_path: dir.join("SKILL.md"),
            base_dir: dir.clone(),
            source_info: SourceInfo {
                path: dir.join("SKILL.md").display().to_string(),
                source: "auto".to_string(),
                scope,
                origin: SourceOrigin::TopLevel,
                base_dir: None,
            },
            disable_model_invocation: false,
            kind: SkillKind::Python,
            python: Some(SkillPythonMetadata {
                import_name: name.replace('-', "_"),
                package_path: dir.clone(),
                pyproject_path: dir.join("pyproject.toml"),
            }),
        }
    }

    fn kernel_skill(name: &str) -> KernelPythonSkill {
        let dir = PathBuf::from(format!("/skills/{name}"));
        KernelPythonSkill {
            name: name.to_string(),
            import_name: name.replace('-', "_"),
            package_path: dir.clone(),
            pyproject_path: dir.join("pyproject.toml"),
        }
    }

    /// An untrusted project's Python skill (auto-discovered from
    /// `<cwd>/.eukhe/skills`) never reaches the kernel's install/import;
    /// user and explicitly passed skills still do.
    #[test]
    fn untrusted_project_python_skills_stay_out_of_the_kernel() {
        let skills = [
            python_skill("user-tool", SourceScope::User),
            python_skill("repo-tool", SourceScope::Project),
            python_skill("flag-tool", SourceScope::Temporary),
        ];
        assert_eq!(
            kernel_python_skills(&skills, TrustLevel::Untrusted),
            KernelPythonSkills {
                admitted: vec![kernel_skill("user-tool"), kernel_skill("flag-tool")],
                withheld: vec!["repo-tool".to_string()],
            }
        );
        assert_eq!(
            kernel_python_skills(&skills, TrustLevel::Trusted),
            KernelPythonSkills {
                admitted: vec![
                    kernel_skill("user-tool"),
                    kernel_skill("repo-tool"),
                    kernel_skill("flag-tool"),
                ],
                withheld: Vec::new(),
            }
        );
    }
}
