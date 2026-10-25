//! The pasted authorization input of the localhost-callback logins (the
//! subscription logins' paste prompt and the MCP logins): one parser for
//! every shape a user can copy out of a browser or a terminal, plus the
//! user-facing texts of the paste retry loop. A browser on another machine
//! cannot reach the localhost callback, so the user copies the address of
//! the failed page; terminal and browser copies add quotes, angle brackets,
//! surrounding whitespace, and line breaks inside a wrapped address. Every
//! decision and text is the compiled core's
//! (`eukhe_bend::rules::redirect_input`, `laws/redirect_input.bend`).

use std::fmt;

use eukhe_bend::rules::redirect_input as rules;

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

impl From<rules::Fail> for RedirectInputError {
    fn from(fail: rules::Fail) -> Self {
        match fail {
            rules::Fail::MissingCode => RedirectInputError::MissingCode,
            rules::Fail::StateMismatch => RedirectInputError::StateMismatch,
            rules::Fail::Provider { error, description } => {
                RedirectInputError::Provider { error, description }
            }
        }
    }
}

impl fmt::Display for RedirectInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&rules::text(&match self {
            RedirectInputError::MissingCode => rules::Fail::MissingCode,
            RedirectInputError::StateMismatch => rules::Fail::StateMismatch,
            RedirectInputError::Provider { error, description } => rules::Fail::Provider {
                error: error.clone(),
                description: description.clone(),
            },
        }))
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
        let (code, state) = rules::verify(&self.code, self.state.as_deref(), expected_state)?;
        Ok(VerifiedAuthorization { code, state })
    }
}

/// One pasted token as typed: whitespace anywhere (a wrapped terminal
/// line breaks it, a copy adds a trailing newline) and invisible
/// zero-width characters dropped, then wrapping quotes, backticks, or
/// angle brackets trimmed. Codes, addresses, and API keys never contain
/// either.
#[must_use]
pub fn clean_paste(input: &str) -> String {
    rules::clean(input)
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
    let pasted = rules::parse(input)?;
    Ok(PastedAuthorization {
        code: pasted.code,
        state: pasted.state,
    })
}

/// The notice of a failed token exchange: the real reason, then the two
/// ways forward (the same login stays open with its verifier and state).
#[must_use]
pub fn exchange_retry_notice(error: &str) -> String {
    rules::notice(error)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

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
