//! `TypeBox`'s format registry (`format/*`): the checks behind the JSON Schema
//! `format` keyword. Unknown formats pass, as in `Format.Test`.

use unicode_normalization::UnicodeNormalization;

use super::idna;
use super::regexp::{static_regexp, JsRegExp};
use crate::utils::js::utf16_len;

static_regexp!(DATE, r"^(\d\d\d\d)-(\d\d)-(\d\d)$", "");
static_regexp!(
    DURATION,
    r"^P((\d+Y(\d+M(\d+D)?)?|\d+M(\d+D)?|\d+D)(T(\d+H(\d+M(\d+S)?)?|\d+M(\d+S)?|\d+S))?|T(\d+H(\d+M(\d+S)?)?|\d+M(\d+S)?|\d+S)|\d+W)$",
    ""
);
static_regexp!(
    EMAIL,
    r#"^(?:[a-z0-9!#$%&'*+/=?^_`{|}~-]+(?:\.[a-z0-9!#$%&'*+/=?^_`{|}~-]+)*|"(?:[^"\\]|\\[\x20-\x7e])*")@(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?(?:\.[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?)*|\[(?:IPv6:[a-f0-9:]+|(?:25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])(?:\.(?:25[0-5]|2[0-4][0-9]|1[0-9]{2}|[1-9]?[0-9])){3})\])$"#,
    "i"
);
static_regexp!(
    IDN_EMAIL,
    r#"^(?:[A-Za-z0-9!#$%&'*+\/=?^_`{|}~\u{0080}-\u{10FFFF}-]+(?:\.[A-Za-z0-9!#$%&'*+\/=?^_`{|}~\u{0080}-\u{10FFFF}-]+)*|"(?:[^"\\]|\\.)*")@[\p{L}\p{N}](?:[\p{L}\p{N}-]{0,62})(?<!-)(?:\.[\p{L}\p{N}](?:[\p{L}\p{N}-]{0,62})(?<!-))*$"#,
    "iu"
);
static_regexp!(
    IPV4,
    r"^(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)$",
    ""
);
static_regexp!(
    IPV6,
    r"^(?:(?:(?:[0-9a-f]{1,4}:){6}|::(?:[0-9a-f]{1,4}:){5}|(?:[0-9a-f]{1,4})?::(?:[0-9a-f]{1,4}:){4}|(?:(?:[0-9a-f]{1,4}:)?[0-9a-f]{1,4})?::(?:[0-9a-f]{1,4}:){3}|(?:(?:[0-9a-f]{1,4}:){0,2}[0-9a-f]{1,4})?::(?:[0-9a-f]{1,4}:){2}|(?:(?:[0-9a-f]{1,4}:){0,3}[0-9a-f]{1,4})?::[0-9a-f]{1,4}:|(?:(?:[0-9a-f]{1,4}:){0,4}[0-9a-f]{1,4})?::)(?:[0-9a-f]{1,4}:[0-9a-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[0-9a-f]{1,4}:){0,5}[0-9a-f]{1,4})?::[0-9a-f]{1,4}|(?:(?:[0-9a-f]{1,4}:){0,6}[0-9a-f]{1,4})?::)$",
    "i"
);
static_regexp!(IRI_IPV_FUTURE_MATCH, r"\[[vV][0-9a-fA-F]+\.[^\]]+\]", "");
static_regexp!(IRI_INVALID_IRI_CHARS, r"[\x00-\x20<>\^`{|}\\]", "");
static_regexp!(IRI_INVALID_PERCENT_ENCODING, r"%(?![0-9a-fA-F]{2})", "");
static_regexp!(
    IRI_REFERENCE_INVALID_IRI_CHARS,
    r"[\x00-\x20\x7F\\]|%(?![0-9a-fA-F]{2})",
    ""
);
static_regexp!(
    IRI_REFERENCE_MALFORMED_SCHEME,
    r"^[a-zA-Z][a-zA-Z0-9+\-.]*\/\/",
    ""
);
static_regexp!(JSON_POINTER, r"^(?:\/(?:[^~/]|~0|~1)*)*$", "");
static_regexp!(
    JSON_POINTER_URI_FRAGMENT,
    r"^#(?:\/(?:[a-z0-9_\-.!$&'()*+,;:=@]|%[0-9a-f]{2}|~0|~1)*)*$",
    "i"
);
static_regexp!(
    RELATIVE_JSON_POINTER,
    r"^(?:0|[1-9][0-9]*)(?:#|(?:\/(?:[^~/]|~0|~1)*)*)$",
    ""
);
static_regexp!(
    TIME,
    r"^(\d\d):(\d\d):(\d\d)(?:\.\d+)?(?:([Zz])|([+-])(\d\d):(\d\d))?$",
    ""
);
static_regexp!(
    URI,
    r"^[a-z][a-z0-9+\-.]*:(?:\/\/(?:(?:[-a-z0-9._~!$&'()*+,;=:]|%[0-9a-f]{2})*@)?(?:\[(?:(?:(?:[\da-f]{1,4}:){6}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|::(?:[\da-f]{1,4}:){5}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:[\da-f]{1,4})?::(?:[\da-f]{1,4}:){4}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,1}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){3}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,2}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){2}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,3}[\da-f]{1,4})?::[\da-f]{1,4}:(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,4}[\da-f]{1,4})?::(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,5}[\da-f]{1,4})?::[\da-f]{1,4}|(?:(?:[\da-f]{1,4}:){0,6}[\da-f]{1,4})?::)|v[0-9a-f]+\.[-a-z0-9._~!$&'()*+,;=:]+)\]|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)|(?:[-a-z0-9._~!$&'()*+,;=]|%[0-9a-f]{2})*)(?::\d*)?(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*|\/(?:(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?|(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?(?:\?(?:[-a-z0-9._~!$&'()*+,;=:@/?]|%[0-9a-f]{2})*)?(?:#(?:[-a-z0-9._~!$&'()*+,;=:@/?]|%[0-9a-f]{2})*)?$",
    "i"
);
static_regexp!(
    URI_REFERENCE,
    r"^(?:[a-z][a-z0-9+\-.]*:(?:\/\/(?:(?:[-a-z0-9._~!$&'()*+,;=:]|%[0-9a-f]{2})*@)?(?:\[(?:(?:(?:[\da-f]{1,4}:){6}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|::(?:[\da-f]{1,4}:){5}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:[\da-f]{1,4})?::(?:[\da-f]{1,4}:){4}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,1}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){3}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,2}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){2}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,3}[\da-f]{1,4})?::[\da-f]{1,4}:(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,4}[\da-f]{1,4})?::(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,5}[\da-f]{1,4})?::[\da-f]{1,4}|(?:(?:[\da-f]{1,4}:){0,6}[\da-f]{1,4})?::)|v[0-9a-f]+\.[-a-z0-9._~!$&'()*+,;=:]+)\]|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)|(?:[-a-z0-9._~!$&'()*+,;=]|%[0-9a-f]{2})*)(?::\d*)?(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*|\/(?:(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?|(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?|(?:\/\/(?:(?:[-a-z0-9._~!$&'()*+,;=:]|%[0-9a-f]{2})*@)?(?:\[(?:(?:(?:[\da-f]{1,4}:){6}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|::(?:[\da-f]{1,4}:){5}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:[\da-f]{1,4})?::(?:[\da-f]{1,4}:){4}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,1}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){3}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,2}[\da-f]{1,4})?::(?:[\da-f]{1,4}:){2}(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,3}[\da-f]{1,4})?::[\da-f]{1,4}:(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,4}[\da-f]{1,4})?::(?:[\da-f]{1,4}:[\da-f]{1,4}|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d))|(?:(?:[\da-f]{1,4}:){0,5}[\da-f]{1,4})?::[\da-f]{1,4}|(?:(?:[\da-f]{1,4}:){0,6}[\da-f]{1,4})?::)|v[0-9a-f]+\.[-a-z0-9._~!$&'()*+,;=:]+)\]|(?:(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)\.){3}(?:25[0-5]|2[0-4]\d|1\d\d|[1-9]?\d)|(?:[-a-z0-9._~!$&'()*+,;=]|%[0-9a-f]{2})*)(?::\d*)?(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*|\/(?:(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?|(?:[-a-z0-9._~!$&'()*+,;=@]|%[0-9a-f]{2})+(?:\/(?:[-a-z0-9._~!$&'()*+,;=:@]|%[0-9a-f]{2})*)*)?)(?:\?(?:[-a-z0-9._~!$&'()*+,;=:@/?]|%[0-9a-f]{2})*)?(?:#(?:[-a-z0-9._~!$&'()*+,;=:@/?]|%[0-9a-f]{2})*)?$",
    "i"
);
static_regexp!(
    URI_TEMPLATE,
    r#"^(?:(?:[^\x00-\x20"<>%\\^`{|}\x7f]|%[0-9a-f]{2})|\{[+#./;?&=,!@|]?(?:[a-z0-9_]|%[0-9a-f]{2})+(?:\.(?:[a-z0-9_]|%[0-9a-f]{2})+)*(?::[1-9]\d{0,3}|\*)?(?:,(?:[a-z0-9_]|%[0-9a-f]{2})+(?:\.(?:[a-z0-9_]|%[0-9a-f]{2})+)*(?::[1-9]\d{0,3}|\*)?)*\})*$"#,
    "i"
);
static_regexp!(UUID, r"^[0-9a-f]{8}-(?:[0-9a-f]{4}-){3}[0-9a-f]{12}$", "i");

/// `Format.Test(format, value)`: unregistered formats pass.
pub(crate) fn test(format: &str, value: &str) -> bool {
    match format {
        "date-time" => is_date_time(value),
        "date" => is_date(value),
        "duration" => DURATION.test(value),
        "email" => EMAIL.test(value),
        "hostname" => idna::is_hostname(value),
        "idn-email" => IDN_EMAIL.test(&value.nfc().collect::<String>()),
        "idn-hostname" => idna::is_idn_hostname(value),
        "ipv4" => IPV4.test(value),
        "ipv6" => IPV6.test(value),
        "iri-reference" => is_iri_reference(value),
        "iri" => is_iri(value),
        "json-pointer-uri-fragment" => JSON_POINTER_URI_FRAGMENT.test(value),
        "json-pointer" => JSON_POINTER.test(value),
        "regex" => JsRegExp::unicode(value).is_ok(),
        "relative-json-pointer" => RELATIVE_JSON_POINTER.test(value),
        "time" => is_time(value),
        "uri-reference" => URI_REFERENCE.test(value),
        "uri-template" => URI_TEMPLATE.test(value),
        "uri" => URI.test(value),
        "url" => url::Url::parse(value).is_ok(),
        "uuid" => UUID.test(value),
        _ => true,
    }
}

const DAYS: [u32; 13] = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

fn is_leap_year(year: u32) -> bool {
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

/// `+match` of a `\d\d...` group.
fn digits(group: Option<&str>) -> u32 {
    group.and_then(|text| text.parse().ok()).unwrap_or(0)
}

fn is_date(value: &str) -> bool {
    let Some(groups) = DATE.captures(value) else {
        return false;
    };
    let year = digits(groups.get(1).copied().flatten());
    let month = digits(groups.get(2).copied().flatten());
    let day = digits(groups.get(3).copied().flatten());
    let limit = if month == 2 && is_leap_year(year) {
        29
    } else {
        DAYS.get(month as usize).copied().unwrap_or(0)
    };
    (1..=12).contains(&month) && day >= 1 && day <= limit
}

fn is_date_time(value: &str) -> bool {
    let parts: Vec<&str> = value.split(['T', 't']).collect();
    parts.len() == 2 && is_date(parts[0]) && is_time(parts[1])
}

/// `IsTime(value, strictTimeZone = true)`.
fn is_time(value: &str) -> bool {
    let Some(groups) = TIME.captures(value) else {
        return false;
    };
    let group = |index: usize| groups.get(index).copied().flatten();
    if group(4).is_none() && group(5).is_none() {
        return false;
    }
    let hour = digits(group(1));
    let minute = digits(group(2));
    let second = digits(group(3));
    if hour > 23 || minute > 59 || second > 60 {
        return false;
    }
    if group(5).is_some() && (digits(group(6)) > 23 || digits(group(7)) > 59) {
        return false;
    }
    if second < 60 {
        return true;
    }
    let sign: i64 = if group(5) == Some("-") { -1 } else { 1 };
    let offset = i64::from(digits(group(6)) * 60 + digits(group(7)));
    let total_utc_minutes = i64::from(hour * 60 + minute) - sign * offset;
    (total_utc_minutes % 1440 + 1440) % 1440 == 1439
}

const IPV_FUTURE_MATCH_MAX_LENGTH: usize = 2048;

fn is_iri(value: &str) -> bool {
    if IRI_INVALID_IRI_CHARS.test(value) || IRI_INVALID_PERCENT_ENCODING.test(value) {
        return false;
    }
    let narrowed = match IRI_IPV_FUTURE_MATCH.find_range(value) {
        Some(range) if utf16_len(value) < IPV_FUTURE_MATCH_MAX_LENGTH => {
            format!("{}[::1]{}", &value[..range.start], &value[range.end..])
        }
        _ => value.to_owned(),
    };
    url::Url::parse(&narrowed).is_ok()
}

fn is_iri_reference(value: &str) -> bool {
    !IRI_REFERENCE_INVALID_IRI_CHARS.test(value)
        && !IRI_REFERENCE_MALFORMED_SCHEME.test(value)
        && url::Url::parse("http://example.com")
            .and_then(|base| base.join(value))
            .is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_patterns_compile() {
        for regexp in [
            &DATE,
            &DURATION,
            &EMAIL,
            &IDN_EMAIL,
            &IPV4,
            &IPV6,
            &IRI_IPV_FUTURE_MATCH,
            &IRI_INVALID_IRI_CHARS,
            &IRI_INVALID_PERCENT_ENCODING,
            &IRI_REFERENCE_INVALID_IRI_CHARS,
            &IRI_REFERENCE_MALFORMED_SCHEME,
            &JSON_POINTER,
            &JSON_POINTER_URI_FRAGMENT,
            &RELATIVE_JSON_POINTER,
            &TIME,
            &URI,
            &URI_REFERENCE,
            &URI_TEMPLATE,
            &UUID,
        ] {
            let _ = regexp.test("");
        }
    }

    #[test]
    fn formats_follow_typebox() {
        let cases: [(&str, &str, bool); 24] = [
            ("date", "2020-02-29", true),
            ("date", "2021-02-29", false),
            ("date-time", "2020-12-12T20:20:40+00:00", true),
            ("date-time", "2020-12-12t20:20:40z", true),
            ("date-time", "2020-12-12T20:20:40", false),
            ("time", "23:59:60Z", true),
            ("time", "22:59:60Z", false),
            ("time", "23:59:60+01:00", false),
            ("time", "22:59:60-01:00", true),
            ("duration", "P1Y2M", true),
            ("email", "a@b.co", true),
            ("email", "a@", false),
            ("ipv4", "192.168.0.1", true),
            ("ipv6", "::1", true),
            ("uuid", "123e4567-e89b-12d3-a456-426614174000", true),
            ("uri", "https://example.com/a?b#c", true),
            ("uri", "relative/path", false),
            ("uri-reference", "relative/path", true),
            ("url", "https://example.com", true),
            ("url", "not a url", false),
            ("regex", "(a", false),
            ("json-pointer", "/a~1b", true),
            ("iri", "http://[vF.addr]/x", true),
            ("unknown-format", "anything", true),
        ];
        for (format, value, expected) in cases {
            assert_eq!(test(format, value), expected, "{format} {value}");
        }
    }
}
