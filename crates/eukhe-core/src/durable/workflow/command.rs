//! `/dynamic-workflow [--size small|medium|large] <request>` arguments.

use eukhe_types::workflow::WorkflowSize;

/// The usage line of `/dynamic-workflow`.
pub(crate) const DYNAMIC_WORKFLOW_USAGE: &str =
    "Usage: /dynamic-workflow [--size small|medium|large] <request>";

/// Parsed `/dynamic-workflow` arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DynamicWorkflowArgs {
    /// `None`: the `workflow.size` setting decides.
    pub(crate) size: Option<WorkflowSize>,
    pub(crate) request: String,
}

/// Parse `args`: an optional leading `--size <size>` (or `--size=<size>`),
/// then the request.
///
/// # Errors
///
/// A missing or unknown size, or an empty request.
pub(crate) fn parse_dynamic_workflow_args(args: &str) -> Result<DynamicWorkflowArgs, String> {
    let rest = args.trim();
    let (size, request) = if let Some(after) = rest.strip_prefix("--size") {
        let after = after.strip_prefix('=').unwrap_or(after).trim_start();
        let end = after.find(char::is_whitespace).unwrap_or(after.len());
        let name = &after[..end];
        if name.is_empty() {
            return Err(DYNAMIC_WORKFLOW_USAGE.to_owned());
        }
        let size = WorkflowSize::parse(name)
            .ok_or_else(|| format!("Unknown workflow size: {name} (small, medium, or large)"))?;
        (Some(size), after[end..].trim())
    } else {
        (None, rest)
    };
    if request.is_empty() {
        return Err(DYNAMIC_WORKFLOW_USAGE.to_owned());
    }
    Ok(DynamicWorkflowArgs {
        size,
        request: request.to_owned(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_size_flag_and_the_request() {
        assert_eq!(
            parse_dynamic_workflow_args("--size large  review the repo"),
            Ok(DynamicWorkflowArgs {
                size: Some(WorkflowSize::Large),
                request: "review the repo".to_owned()
            })
        );
        assert_eq!(
            parse_dynamic_workflow_args("--size=small fix it"),
            Ok(DynamicWorkflowArgs {
                size: Some(WorkflowSize::Small),
                request: "fix it".to_owned()
            })
        );
        assert_eq!(
            parse_dynamic_workflow_args("review --size large"),
            Ok(DynamicWorkflowArgs {
                size: None,
                request: "review --size large".to_owned()
            })
        );
    }

    #[test]
    fn rejects_an_unknown_size_and_an_empty_request() {
        assert_eq!(
            parse_dynamic_workflow_args("--size huge do it"),
            Err("Unknown workflow size: huge (small, medium, or large)".to_owned())
        );
        assert_eq!(
            parse_dynamic_workflow_args("--size medium"),
            Err(DYNAMIC_WORKFLOW_USAGE.to_owned())
        );
        assert_eq!(
            parse_dynamic_workflow_args("   "),
            Err(DYNAMIC_WORKFLOW_USAGE.to_owned())
        );
    }
}
