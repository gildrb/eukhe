//! The pasted authorization input of the localhost-callback logins
//! (Anthropic, Codex, MCP): one parser for every shape a user can copy
//! out of a browser or a terminal, plus the user-facing texts of the
//! paste retry loop. A browser on another machine cannot reach the
//! localhost callback, so the user copies the address of the failed
//! page; terminal and browser copies add quotes, angle brackets,
//! surrounding whitespace, and line breaks inside a wrapped address.

use std::fmt;

/// Characters a terminal, chat, or browser copy wraps an address in
/// (ASCII quotes, backticks, angle brackets, and typographic quotes).
const WRAPPERS: [char; 9] = [
    '"', '\'', '`', '<', '>', '\u{201C}', '\u{201D}', '\u{2018}', '\u{2019}',
];

/// The query keys that mark a paste as a redirect's parameters.
const REDIRECT_KEYS: [&str; 3] = ["code", "state", "error"];

/// One parsed paste: the authorization code and the echoed `state`
/// (`None` when the paste carries none, e.g. a bare code).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PastedAuthorization {
    pub code: String,
    pub state: Option<String>,
}

/// A code whose echoed state matched the login's own (a paste without
/// a state takes the login's state).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedAuthorization {
    pub code: String,
    pub state: String,
}

/// Why a paste (or a browser redirect) cannot complete the login. Every
/// variant is retryable: the user pastes again or signs in again.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RedirectInputError {
    /// The input carries no authorization code.
    MissingCode,
    /// The echoed state is not this login's.
    StateMismatch,
    /// The authorization server answered an OAuth error (`error=`).
    Provider {
        error: String,
        description: Option<String>,
    },
}

impl fmt::Display for RedirectInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RedirectInputError::MissingCode => formatter.write_str(
                "That address has no authorization code. Paste the full address of the page \
                 your browser ended on.",
            ),
            RedirectInputError::StateMismatch => formatter.write_str(
                "That address is from a different login attempt (state mismatch). Paste the \
                 address from the browser tab this login opened.",
            ),
            RedirectInputError::Provider { error, description } => {
                write!(formatter, "The sign-in page reported an error: {error}")?;
                if let Some(description) = description {
                    write!(formatter, " ({description})")?;
                }
                formatter.write_str(
                    ". Open the login link again and sign in, then paste the new address.",
                )
            }
        }
    }
}

impl std::error::Error for RedirectInputError {}

impl PastedAuthorization {
    /// Check the echoed state against the login's own.
    ///
    /// # Errors
    ///
    /// Returns [`RedirectInputError::StateMismatch`] when the paste echoes
    /// another login's state.
    pub fn verify_state(
        self,
        expected_state: &str,
    ) -> Result<VerifiedAuthorization, RedirectInputError> {
        match self.state {
            Some(state) if state != expected_state => Err(RedirectInputError::StateMismatch),
            Some(state) => Ok(VerifiedAuthorization {
                code: self.code,
                state,
            }),
            None => Ok(VerifiedAuthorization {
                code: self.code,
                state: expected_state.to_string(),
            }),
        }
    }
}

/// One pasted token as typed: whitespace anywhere (a wrapped terminal
/// line breaks it, a copy adds a trailing newline) and invisible
/// zero-width characters dropped, then wrapping quotes, backticks, or
/// angle brackets trimmed. Codes, addresses, and API keys never contain
/// either.
#[must_use]
pub fn clean_paste(input: &str) -> String {
    let compact: String = input
        .chars()
        .filter(|character| {
            !character.is_whitespace()
                && !matches!(
                    character,
                    '\u{200B}' | '\u{200C}' | '\u{200D}' | '\u{2060}' | '\u{FEFF}'
                )
        })
        .collect();
    compact
        .trim_matches(|character| WRAPPERS.contains(&character))
        .to_string()
}

/// Parse one pasted authorization input: a callback address (any host,
/// port, or path; with or without a scheme, a trailing slash, a
/// fragment, or extra parameters; code and state in the query or the
/// fragment), a `code=..&state=..` query string, a `code#state` pair,
/// or a bare code, cleaned by [`clean_paste`] first; query values are
/// percent-decoded.
///
/// # Errors
///
/// Returns [`RedirectInputError::MissingCode`] when no code is present
/// and [`RedirectInputError::Provider`] when the redirect carries an
/// OAuth `error`.
pub fn parse_redirect_input(input: &str) -> Result<PastedAuthorization, RedirectInputError> {
    let cleaned = clean_paste(input);
    let value = cleaned.as_str();
    if let Some((_, rest)) = value.split_once('?') {
        // An address with a query (`localhost:1/callback?code=..`, the
        // scheme optional); the fragment is the fallback carrier.
        let (query, fragment) = rest.split_once('#').unwrap_or((rest, ""));
        return from_params(&[query.trim_end_matches('/'), fragment]);
    }
    if let Some((_, address_rest)) = value.split_once("://") {
        // An address without a query: only a fragment can carry the code.
        let fragment = address_rest
            .split_once('#')
            .map_or("", |(_, fragment)| fragment);
        return from_params(&[fragment]);
    }
    let (head, fragment) = value.split_once('#').unwrap_or((value, ""));
    let carries_params = |text: &str| {
        text.split('&').any(|pair| {
            pair.split_once('=')
                .is_some_and(|(key, _)| REDIRECT_KEYS.contains(&key))
        })
    };
    if carries_params(head) {
        // `code=..&state=..` (a fragment after it is page noise).
        return from_params(&[head.trim_end_matches('/')]);
    }
    if carries_params(fragment) {
        // A scheme-less address whose fragment carries the redirect.
        return from_params(&[fragment]);
    }
    if head.is_empty() {
        return Err(RedirectInputError::MissingCode);
    }
    Ok(PastedAuthorization {
        code: head.to_string(),
        state: (!fragment.is_empty()).then(|| fragment.to_string()),
    })
}

/// The redirect parameters of the given carriers (the query first, then
/// the fragment): an OAuth error wins, then the code and its state.
fn from_params(carriers: &[&str]) -> Result<PastedAuthorization, RedirectInputError> {
    let get = |name: &str| {
        carriers.iter().find_map(|carrier| {
            url::form_urlencoded::parse(carrier.as_bytes())
                .find(|(key, value)| key == name && !value.is_empty())
                .map(|(_, value)| value.into_owned())
        })
    };
    if let Some(error) = get("error") {
        return Err(RedirectInputError::Provider {
            error,
            description: get("error_description"),
        });
    }
    let code = get("code").ok_or(RedirectInputError::MissingCode)?;
    Ok(PastedAuthorization {
        code,
        state: get("state"),
    })
}

/// The notice of a failed token exchange: the real reason, then the two
/// ways forward (the same login stays open with its verifier and state).
#[must_use]
pub fn exchange_retry_notice(error: &str) -> String {
    format!(
        "Login did not complete: {}. Paste the address again, or open the login link again \
         and sign in.",
        error.trim().trim_end_matches('.')
    )
}

/// The progress line of a login whose callback port could not be bound:
/// the paste is the only way back from the browser.
pub(crate) fn port_busy_line(port: u16, detail: &str) -> String {
    format!(
        "Port {port} is busy, so the browser cannot hand the login back automatically: paste \
         the address of the page your browser ends on. ({detail})"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn every_copied_address_shape_parses() {
        let cases = [
            (
                "http://localhost:53692/callback?code=abc&state=st",
                "abc",
                Some("st"),
            ),
            (
                "http://127.0.0.1:1455/auth/callback?code=abc&state=st",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback/?code=abc&state=st",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback?code=abc&state=st/",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback?code=abc&state=st#_",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback?x=1&code=abc&y=2&state=st",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback?code=a%2Bb%20c&state=s%26t",
                "a+b c",
                Some("s&t"),
            ),
            (
                "localhost:53692/callback?code=abc&state=st",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/callback#code=abc&state=st",
                "abc",
                Some("st"),
            ),
            (
                "  \"http://localhost:53692/callback?code=abc&state=st\"\n",
                "abc",
                Some("st"),
            ),
            (
                "<http://localhost:53692/callback?code=abc&state=st>",
                "abc",
                Some("st"),
            ),
            (
                "'http://localhost:53692/callback?code=abc&state=st'",
                "abc",
                Some("st"),
            ),
            (
                "\u{201C}http://localhost:53692/callback?code=abc&state=st\u{201D}",
                "abc",
                Some("st"),
            ),
            (
                "http://localhost:53692/call\nback?code=ab\r\nc&sta\tte=st",
                "abc",
                Some("st"),
            ),
            ("code=abc&state=st", "abc", Some("st")),
            ("state=st&code=abc", "abc", Some("st")),
            ("http://localhost:53692/callback?code=abc", "abc", None),
            ("abc#st", "abc", Some("st")),
            ("  abc#st\n", "abc", Some("st")),
            ("abc", "abc", None),
            ("abc==", "abc==", None),
            ("`abc`", "abc", None),
        ];
        for (input, code, state) in cases {
            assert_eq!(
                parse_redirect_input(input),
                Ok(PastedAuthorization {
                    code: code.to_string(),
                    state: state.map(str::to_string),
                }),
                "{input:?}"
            );
        }
    }

    #[test]
    fn inputs_without_a_code_say_so() {
        for input in [
            "",
            "   \n",
            "\"\"",
            "http://localhost:53692/callback",
            "http://localhost:53692/callback?state=st",
            "http://localhost:53692/callback?code=&state=st",
            "#st",
            "state=st",
        ] {
            assert_eq!(
                parse_redirect_input(input),
                Err(RedirectInputError::MissingCode),
                "{input:?}"
            );
        }
    }

    #[test]
    fn an_oauth_error_redirect_reports_its_description() {
        let error = parse_redirect_input(
            "http://localhost:53692/callback?error=access_denied&error_description=The+user+said+no&state=st",
        )
        .unwrap_err();
        assert_eq!(
            error,
            RedirectInputError::Provider {
                error: "access_denied".to_string(),
                description: Some("The user said no".to_string()),
            }
        );
        assert_eq!(
            error.to_string(),
            "The sign-in page reported an error: access_denied (The user said no). Open the \
             login link again and sign in, then paste the new address."
        );
        assert_eq!(
            parse_redirect_input("error=server_error"),
            Err(RedirectInputError::Provider {
                error: "server_error".to_string(),
                description: None,
            })
        );
    }

    #[test]
    fn the_state_check_matches_or_substitutes() {
        let echoed = PastedAuthorization {
            code: "abc".to_string(),
            state: Some("st".to_string()),
        };
        assert_eq!(
            echoed.clone().verify_state("st"),
            Ok(VerifiedAuthorization {
                code: "abc".to_string(),
                state: "st".to_string(),
            })
        );
        assert_eq!(
            echoed.verify_state("other"),
            Err(RedirectInputError::StateMismatch)
        );
        let bare = PastedAuthorization {
            code: "abc".to_string(),
            state: None,
        };
        assert_eq!(
            bare.verify_state("st"),
            Ok(VerifiedAuthorization {
                code: "abc".to_string(),
                state: "st".to_string(),
            })
        );
    }

    /// One generated paste shape around a code and an optional state.
    #[derive(Debug, Clone)]
    enum Shape {
        /// A callback address: host, port, path, a trailing slash on the
        /// path, extra parameters, the carrier (query or fragment), a
        /// trailing slash after the query, and a fragment suffix.
        Address {
            scheme: bool,
            host: &'static str,
            port: u16,
            path: &'static str,
            path_slash: bool,
            extra: Vec<(String, String)>,
            in_fragment: bool,
            query_slash: bool,
            fragment: Option<String>,
        },
        /// A bare `code=..&state=..` query string.
        Query { extra: Vec<(String, String)> },
        /// `code#state` (or the bare code without a state).
        Pair,
    }

    fn encode(pairs: &[(String, String)]) -> String {
        url::form_urlencoded::Serializer::new(String::new())
            .extend_pairs(
                pairs
                    .iter()
                    .map(|(key, value)| (key.as_str(), value.as_str())),
            )
            .finish()
    }

    fn render(shape: &Shape, code: &str, state: Option<&str>) -> String {
        let mut pairs: Vec<(String, String)> = vec![("code".to_string(), code.to_string())];
        if let Some(state) = state {
            pairs.push(("state".to_string(), state.to_string()));
        }
        match shape {
            Shape::Address {
                scheme,
                host,
                port,
                path,
                path_slash,
                extra,
                in_fragment,
                query_slash,
                fragment,
            } => {
                let mut all = extra.clone();
                all.extend(pairs);
                let mut text = format!(
                    "{}{host}:{port}{path}{}",
                    if *scheme { "http://" } else { "" },
                    if *path_slash { "/" } else { "" }
                );
                if *in_fragment {
                    text.push('#');
                    text.push_str(&encode(&all));
                } else {
                    text.push('?');
                    text.push_str(&encode(&all));
                    if *query_slash {
                        text.push('/');
                    }
                    if let Some(fragment) = fragment {
                        text.push('#');
                        text.push_str(fragment);
                    }
                }
                text
            }
            Shape::Query { extra } => {
                let mut all = pairs;
                all.extend(extra.iter().cloned());
                encode(&all)
            }
            Shape::Pair => match state {
                Some(state) => format!("{code}#{state}"),
                None => code.to_string(),
            },
        }
    }

    fn url_safe() -> impl Strategy<Value = String> {
        "[A-Za-z0-9_-]{1,48}"
    }

    /// Any non-empty value: URL-safe tokens and arbitrary unicode (the
    /// address and query shapes percent-encode it).
    fn any_value() -> impl Strategy<Value = String> {
        prop_oneof![
            url_safe(),
            any::<String>().prop_filter("non-empty", |value| !value.is_empty())
        ]
    }

    fn extra_params() -> impl Strategy<Value = Vec<(String, String)>> {
        proptest::collection::vec(
            (
                "[a-z]{1,8}".prop_filter("not a redirect key", |key| {
                    !matches!(
                        key.as_str(),
                        "code" | "state" | "error" | "error_description"
                    )
                }),
                url_safe(),
            ),
            0..3,
        )
    }

    fn address_shape() -> impl Strategy<Value = Shape> {
        (
            any::<bool>(),
            prop::sample::select(vec!["localhost", "127.0.0.1"]),
            1u16..,
            prop::sample::select(vec!["/callback", "/auth/callback", ""]),
            any::<bool>(),
            extra_params(),
            any::<bool>(),
            any::<bool>(),
            proptest::option::of("[a-z0-9_]{0,8}"),
        )
            .prop_map(
                |(
                    scheme,
                    host,
                    port,
                    path,
                    path_slash,
                    extra,
                    in_fragment,
                    query_slash,
                    fragment,
                )| {
                    Shape::Address {
                        scheme,
                        host,
                        port,
                        path,
                        path_slash,
                        extra,
                        in_fragment,
                        query_slash,
                        fragment,
                    }
                },
            )
    }

    /// A paste case: the shape with its code and state (the pair shape
    /// takes URL-safe values: nothing encodes them).
    fn case() -> impl Strategy<Value = (Shape, String, Option<String>)> {
        prop_oneof![
            (
                address_shape(),
                any_value(),
                proptest::option::of(any_value())
            ),
            (
                extra_params().prop_map(|extra| Shape::Query { extra }),
                any_value(),
                proptest::option::of(any_value())
            ),
            (
                Just(Shape::Pair),
                url_safe(),
                proptest::option::of(url_safe())
            ),
        ]
    }

    /// The copy noise: surrounding whitespace, a wrapping pair, and line
    /// breaks or spaces inserted inside.
    fn wrap(
        text: &str,
        lead: &str,
        trail: &str,
        pair: (&str, &str),
        breaks: &[(usize, &str)],
    ) -> String {
        let mut body = text.to_string();
        let mut positions: Vec<(usize, &str)> = breaks
            .iter()
            .map(|(index, noise)| (index % (body.len() + 1), *noise))
            .filter(|(index, _)| body.is_char_boundary(*index))
            .collect();
        positions.sort_by_key(|(index, _)| std::cmp::Reverse(*index));
        for (index, noise) in positions {
            body.insert_str(index, noise);
        }
        format!("{lead}{}{body}{}{trail}", pair.0, pair.1)
    }

    proptest! {
        #[test]
        fn the_parser_recovers_the_code_and_state_from_any_copy(
            (shape, code, state) in case(),
            lead in prop::sample::select(vec!["", " ", "\n", "\t", "\r\n  "]),
            trail in prop::sample::select(vec!["", " ", "\n", "\t", " \r\n"]),
            pair in prop::sample::select(vec![("", ""), ("\"", "\""), ("'", "'"), ("<", ">"), ("`", "`"), ("\u{201C}", "\u{201D}")]),
            breaks in proptest::collection::vec(
                (any::<usize>(), prop::sample::select(vec!["\n", "\r\n", " ", "\t"])),
                0..4,
            ),
        ) {
            let text = render(&shape, &code, state.as_deref());
            let input = wrap(&text, lead, trail, pair, &breaks);
            prop_assert_eq!(
                parse_redirect_input(&input),
                Ok(PastedAuthorization { code, state })
            );
        }
    }
}
