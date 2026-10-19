//! The color tokens of a theme: every color a surface paints has one.

/// One color token of a theme file's `colors` section.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Token {
    Accent,
    Border,
    BorderAccent,
    BorderMuted,
    Success,
    Error,
    Warning,
    Muted,
    Dim,
    Text,
    ThinkingText,
    UserMessageText,
    CustomMessageText,
    CustomMessageLabel,
    RefinementHeader,
    RefinementSummary,
    ToolTitle,
    ToolOutput,
    MdBody,
    MdHeading,
    MdLink,
    MdLinkUrl,
    MdCode,
    MdCodeBlock,
    MdCodeBlockBorder,
    MdQuote,
    MdQuoteBorder,
    MdHr,
    MdListBullet,
    ToolDiffAdded,
    ToolDiffRemoved,
    ToolDiffText,
    ToolDiffContext,
    SyntaxComment,
    SyntaxKeyword,
    SyntaxFunction,
    SyntaxVariable,
    SyntaxString,
    SyntaxNumber,
    SyntaxType,
    SyntaxOperator,
    SyntaxPunctuation,
    ThinkingOff,
    ThinkingMinimal,
    ThinkingLow,
    ThinkingMedium,
    ThinkingHigh,
    ThinkingXhigh,
    BashMode,
    SelectedBg,
    UserMessageBg,
    CustomMessageBg,
    ToolPendingBg,
    ToolSuccessBg,
    ToolErrorBg,
    ToolDiffAddedBg,
    ToolDiffRemovedBg,
    ToolPanelBg,
    Background,
    Foreground,
}

/// What a token paints, which decides what the terminal default (`""`)
/// stands for: ink takes the theme's foreground, a surface its background.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Layer {
    Ink,
    Surface,
}

/// Whether a theme file must write a token. An optional token a file
/// leaves out takes its documented fallback ([`crate::Palette`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Presence {
    Required,
    Optional,
}

impl Token {
    /// Every token, in declaration order: `ALL[token as usize] == token`.
    pub const ALL: [Token; 60] = [
        Token::Accent,
        Token::Border,
        Token::BorderAccent,
        Token::BorderMuted,
        Token::Success,
        Token::Error,
        Token::Warning,
        Token::Muted,
        Token::Dim,
        Token::Text,
        Token::ThinkingText,
        Token::UserMessageText,
        Token::CustomMessageText,
        Token::CustomMessageLabel,
        Token::RefinementHeader,
        Token::RefinementSummary,
        Token::ToolTitle,
        Token::ToolOutput,
        Token::MdBody,
        Token::MdHeading,
        Token::MdLink,
        Token::MdLinkUrl,
        Token::MdCode,
        Token::MdCodeBlock,
        Token::MdCodeBlockBorder,
        Token::MdQuote,
        Token::MdQuoteBorder,
        Token::MdHr,
        Token::MdListBullet,
        Token::ToolDiffAdded,
        Token::ToolDiffRemoved,
        Token::ToolDiffText,
        Token::ToolDiffContext,
        Token::SyntaxComment,
        Token::SyntaxKeyword,
        Token::SyntaxFunction,
        Token::SyntaxVariable,
        Token::SyntaxString,
        Token::SyntaxNumber,
        Token::SyntaxType,
        Token::SyntaxOperator,
        Token::SyntaxPunctuation,
        Token::ThinkingOff,
        Token::ThinkingMinimal,
        Token::ThinkingLow,
        Token::ThinkingMedium,
        Token::ThinkingHigh,
        Token::ThinkingXhigh,
        Token::BashMode,
        Token::SelectedBg,
        Token::UserMessageBg,
        Token::CustomMessageBg,
        Token::ToolPendingBg,
        Token::ToolSuccessBg,
        Token::ToolErrorBg,
        Token::ToolDiffAddedBg,
        Token::ToolDiffRemovedBg,
        Token::ToolPanelBg,
        Token::Background,
        Token::Foreground,
    ];

    /// The token's key in a theme file's `colors` section (also its CSS
    /// custom property in the HTML export, `--<name>`).
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Token::Accent => "accent",
            Token::Border => "border",
            Token::BorderAccent => "borderAccent",
            Token::BorderMuted => "borderMuted",
            Token::Success => "success",
            Token::Error => "error",
            Token::Warning => "warning",
            Token::Muted => "muted",
            Token::Dim => "dim",
            Token::Text => "text",
            Token::ThinkingText => "thinkingText",
            Token::UserMessageText => "userMessageText",
            Token::CustomMessageText => "customMessageText",
            Token::CustomMessageLabel => "customMessageLabel",
            Token::RefinementHeader => "refinementHeader",
            Token::RefinementSummary => "refinementSummary",
            Token::ToolTitle => "toolTitle",
            Token::ToolOutput => "toolOutput",
            Token::MdBody => "mdBody",
            Token::MdHeading => "mdHeading",
            Token::MdLink => "mdLink",
            Token::MdLinkUrl => "mdLinkUrl",
            Token::MdCode => "mdCode",
            Token::MdCodeBlock => "mdCodeBlock",
            Token::MdCodeBlockBorder => "mdCodeBlockBorder",
            Token::MdQuote => "mdQuote",
            Token::MdQuoteBorder => "mdQuoteBorder",
            Token::MdHr => "mdHr",
            Token::MdListBullet => "mdListBullet",
            Token::ToolDiffAdded => "toolDiffAdded",
            Token::ToolDiffRemoved => "toolDiffRemoved",
            Token::ToolDiffText => "toolDiffText",
            Token::ToolDiffContext => "toolDiffContext",
            Token::SyntaxComment => "syntaxComment",
            Token::SyntaxKeyword => "syntaxKeyword",
            Token::SyntaxFunction => "syntaxFunction",
            Token::SyntaxVariable => "syntaxVariable",
            Token::SyntaxString => "syntaxString",
            Token::SyntaxNumber => "syntaxNumber",
            Token::SyntaxType => "syntaxType",
            Token::SyntaxOperator => "syntaxOperator",
            Token::SyntaxPunctuation => "syntaxPunctuation",
            Token::ThinkingOff => "thinkingOff",
            Token::ThinkingMinimal => "thinkingMinimal",
            Token::ThinkingLow => "thinkingLow",
            Token::ThinkingMedium => "thinkingMedium",
            Token::ThinkingHigh => "thinkingHigh",
            Token::ThinkingXhigh => "thinkingXhigh",
            Token::BashMode => "bashMode",
            Token::SelectedBg => "selectedBg",
            Token::UserMessageBg => "userMessageBg",
            Token::CustomMessageBg => "customMessageBg",
            Token::ToolPendingBg => "toolPendingBg",
            Token::ToolSuccessBg => "toolSuccessBg",
            Token::ToolErrorBg => "toolErrorBg",
            Token::ToolDiffAddedBg => "toolDiffAddedBg",
            Token::ToolDiffRemovedBg => "toolDiffRemovedBg",
            Token::ToolPanelBg => "toolPanelBg",
            Token::Background => "background",
            Token::Foreground => "foreground",
        }
    }

    /// The token a `colors` key names.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Token> {
        Token::ALL.into_iter().find(|token| token.name() == name)
    }

    #[must_use]
    pub fn layer(self) -> Layer {
        match self {
            Token::SelectedBg
            | Token::UserMessageBg
            | Token::CustomMessageBg
            | Token::ToolPendingBg
            | Token::ToolSuccessBg
            | Token::ToolErrorBg
            | Token::ToolDiffAddedBg
            | Token::ToolDiffRemovedBg
            | Token::ToolPanelBg
            | Token::Background => Layer::Surface,
            Token::Accent
            | Token::Border
            | Token::BorderAccent
            | Token::BorderMuted
            | Token::Success
            | Token::Error
            | Token::Warning
            | Token::Muted
            | Token::Dim
            | Token::Text
            | Token::ThinkingText
            | Token::UserMessageText
            | Token::CustomMessageText
            | Token::CustomMessageLabel
            | Token::RefinementHeader
            | Token::RefinementSummary
            | Token::ToolTitle
            | Token::ToolOutput
            | Token::MdBody
            | Token::MdHeading
            | Token::MdLink
            | Token::MdLinkUrl
            | Token::MdCode
            | Token::MdCodeBlock
            | Token::MdCodeBlockBorder
            | Token::MdQuote
            | Token::MdQuoteBorder
            | Token::MdHr
            | Token::MdListBullet
            | Token::ToolDiffAdded
            | Token::ToolDiffRemoved
            | Token::ToolDiffText
            | Token::ToolDiffContext
            | Token::SyntaxComment
            | Token::SyntaxKeyword
            | Token::SyntaxFunction
            | Token::SyntaxVariable
            | Token::SyntaxString
            | Token::SyntaxNumber
            | Token::SyntaxType
            | Token::SyntaxOperator
            | Token::SyntaxPunctuation
            | Token::ThinkingOff
            | Token::ThinkingMinimal
            | Token::ThinkingLow
            | Token::ThinkingMedium
            | Token::ThinkingHigh
            | Token::ThinkingXhigh
            | Token::BashMode
            | Token::Foreground => Layer::Ink,
        }
    }

    #[must_use]
    pub fn presence(self) -> Presence {
        match self {
            Token::RefinementHeader
            | Token::RefinementSummary
            | Token::MdBody
            | Token::Background
            | Token::Foreground => Presence::Optional,
            Token::Accent
            | Token::Border
            | Token::BorderAccent
            | Token::BorderMuted
            | Token::Success
            | Token::Error
            | Token::Warning
            | Token::Muted
            | Token::Dim
            | Token::Text
            | Token::ThinkingText
            | Token::UserMessageText
            | Token::CustomMessageText
            | Token::CustomMessageLabel
            | Token::ToolTitle
            | Token::ToolOutput
            | Token::MdHeading
            | Token::MdLink
            | Token::MdLinkUrl
            | Token::MdCode
            | Token::MdCodeBlock
            | Token::MdCodeBlockBorder
            | Token::MdQuote
            | Token::MdQuoteBorder
            | Token::MdHr
            | Token::MdListBullet
            | Token::ToolDiffAdded
            | Token::ToolDiffRemoved
            | Token::ToolDiffText
            | Token::ToolDiffContext
            | Token::SyntaxComment
            | Token::SyntaxKeyword
            | Token::SyntaxFunction
            | Token::SyntaxVariable
            | Token::SyntaxString
            | Token::SyntaxNumber
            | Token::SyntaxType
            | Token::SyntaxOperator
            | Token::SyntaxPunctuation
            | Token::ThinkingOff
            | Token::ThinkingMinimal
            | Token::ThinkingLow
            | Token::ThinkingMedium
            | Token::ThinkingHigh
            | Token::ThinkingXhigh
            | Token::BashMode
            | Token::SelectedBg
            | Token::UserMessageBg
            | Token::CustomMessageBg
            | Token::ToolPendingBg
            | Token::ToolSuccessBg
            | Token::ToolErrorBg
            | Token::ToolDiffAddedBg
            | Token::ToolDiffRemovedBg
            | Token::ToolPanelBg => Presence::Required,
        }
    }
}

// The palette indexes by discriminant: `ALL` lists the enum in
// declaration order.
const _: () = {
    let mut index = 0;
    while index < Token::ALL.len() {
        assert!(Token::ALL[index] as usize == index);
        index += 1;
    }
};
