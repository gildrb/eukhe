//! The shapes the code preview reads. They run in the compiled Bend core
//! (`bend/preview_shapes.bend`, entry `bend/ffi_shape.bend`;
//! `laws/preview_shapes.bend`), not as Rust regexes.

use crate::text_shapes::TextShape;

/// One shape of the code preview. Its discriminant is its global shape id
/// (130 plus its index in `bend/preview_shapes.bend` `table`); above each,
/// the regex it replaces, as the source spelled it: `{S}` the JS `\s` class
/// (`[\t\n\x0B\f\r \u{00A0}\u{1680}\u{2000}-\u{200A}\u{2028}\u{2029}\u{202F}\u{205F}\u{3000}\u{FEFF}]`),
/// `{W}` the JS `\w` class (`[A-Za-z0-9_]`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum PreviewShape {
    /// `{S}+`
    WhitespaceRun = 130,
    /// `[A-Za-z0-9+/]{80,}={0,2}`
    Blob = 131,
    /// `\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(["'])[^"']*\2`
    SecretQuoted = 132,
    /// `(?i)\b((?={W}*(?:token|key|secret|password))[A-Za-z_]{W}*){S}*={S}*(?!<redacted>)(?!["'])\S+`
    SecretBare = 133,
    /// `(?i)\b(authorization:\s*(?:bearer\s+)?)[^\s"']+`
    Authorization = 134,
    /// `(["'])sk-[^"']+\1`
    SkKey = 135,
    /// `(["']).{160,}\1`
    LongString = 136,
    /// `^{S}*!`
    Magic = 137,
    /// `^{S}*cd{S}+([^&;|]+)(?:&&|;){S}*`
    CdPrefix = 138,
    /// `^{S}*#`
    Comment = 139,
    /// `^{S}*set{S}+[-+][A-Za-z]*(?:{S}+[-+]?{W}+)*(?:{S}+pipefail)?{S}*$`
    SetLine = 140,
    /// `^(?:export{S}+{W}+=|source{S}+\S+|\.{S}+\S+)`
    EnvLine = 141,
    /// `"([^"]*)"|'([^']*)'|(\S+)`
    ShellWord = 142,
    /// `^\./`
    DotSlash = 143,
    /// `(?:^|/)vitest/dist/cli\.js$`
    VitestCli = 144,
    /// `\S*node_modules/\.bin/`
    BinPrefix = 145,
    /// `\s*(?:&&|;)\s*`
    ChainSeparator = 146,
    /// `<<-?\s*['"]?([A-Za-z_][A-Za-z0-9_]*)['"]?`
    Heredoc = 147,
    /// `\b(?:uv{S}+run{S}+)?python3?\b`
    PythonRun = 148,
    /// `(?<![\w.])(?:bash|sh)\b` (only asked whether it fits: the fit
    /// starts at the char before the word)
    ShellRun = 149,
    /// `\bnode\b`
    NodeRun = 150,
    /// `\b(?:cat|tee)\b.*(?:>|\s)(\S+)\s*<<-?`
    CatWrite = 151,
    /// `\bapply_patch\b`
    ApplyPatch = 152,
    /// `\b(?:rm|mv|cp|git{S}+(?:add|commit)|npm{S}+install|sed{S}+-i|perl{S}+-pi|tee|cat{S}*>|apply_patch)\b`
    Mutation = 153,
    /// `^{S}*(?:import{S}+\S|from{S}+\S+{S}+import{S}+)`
    ImportLine = 154,
    /// `^{S}*`
    Indent = 155,
    /// `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
    Call = 156,
    /// `^{S}*(?:await{S}+)?(?:print|len|str|repr|int|float|list|dict|set|tuple){S}*\(`
    LowCall = 157,
    /// `^print\((.*)\)$`
    PrintCall = 158,
    /// `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(?:Path|pathlib\.Path)\((["'])([^"']+)\2\)`
    PathAssign = 159,
    /// `^{S}*([A-Za-z_][A-Za-z0-9_]*){S}*={S}*(["'])([^"']+)\2`
    StringAssign = 160,
    /// `^(?:await\s+)?([A-Za-z_][A-Za-z0-9_]*)\.(write_text|write_bytes|read_text|read_bytes|mkdir|unlink|rename|replace|touch)\s*\(`
    FileOp = 161,
    /// ``subprocess\.(?:run|check_call|check_output|Popen)\(\s*(["`])([^"`]+)\1``
    SubprocessString = 162,
    /// `subprocess\.(?:run|check_call|check_output|Popen)\(\s*\[([^\]]+)\]`
    SubprocessList = 163,
    /// `["']([^"']+)["']`
    Quoted = 164,
    /// `^{S}*(?:async{S}+def|def|class){S}+`
    DefLine = 165,
    /// `^{S}*@`
    Decorator = 166,
    /// `^{S}*(?:if|elif|else|for|while|with|try|except|finally)\b.*:\s*$`
    Compound = 167,
    /// `:\s*$`
    ColonEnd = 168,
    /// `^[)\]},;\s]+(?:#.*)?$`
    Closers = 169,
    /// `^{S}*if{S}+__name__{S}*=={S}*['"]__main__['"]{S}*:`
    MainGuard = 170,
    /// `^{S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*\.(?:write_text|write_bytes|mkdir|unlink|rename|replace|touch|append|extend|update|add|remove|discard|close|commit|execute|run){S}*\(`
    MethodCall = 171,
    /// `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?(?:Path|pathlib\.Path|json\.loads|json\.dumps|str|int|float|list|dict|set|tuple){S}*\(`
    ValueAssign = 172,
    /// `^{S}*[A-Za-z_][A-Za-z0-9_]*(?:{S}*:\s*[^=]+)?{S}*={S}*(?:await{S}+)?[A-Za-z_][A-Za-z0-9_.]*{S}*\(`
    CallAssign = 173,
    /// `{S}*(?:[A-Za-z_][A-Za-z0-9_]*{S}*={S}*)?(?:await{S}+)?bash{S}*\({S}*[rR]?("""|'''|"|')`
    BashCall = 174,
    /// `^({S}*);{S}*`
    Semicolon = 175,
    /// The `%%bash` cell magic after blank lines (a port of TS
    /// `^(?:[ \t]*\r?\n)*[ \t]*%%bash\b[^\r\n]*(?:\r?\n|$)`; a lone CR after
    /// the magic line ends the fit unread)
    BashMagic = 176,
}

impl TextShape for PreviewShape {
    fn id(self) -> u32 {
        self as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The redaction step through the core: `$1` expands to the captured
    /// name, and every fit is replaced.
    #[test]
    fn replace_all_expands_captures() {
        let text = "api_token = \"abc\" x secret_key='d'";
        assert_eq!(
            PreviewShape::SecretQuoted.replace_all(text, "$1=<redacted>"),
            "api_token=<redacted> x secret_key=<redacted>"
        );
    }

    /// Spans from the core count chars; the slices land on the right bytes
    /// after multi-byte chars.
    #[test]
    fn spans_land_after_multibyte_chars() {
        assert_eq!(
            PreviewShape::ChainSeparator.split("é && ü; x"),
            vec!["é", "ü", "x"]
        );
    }
}
