//! Interruptible client-side retries for provider HTTP requests.
//!
//! Mirrors the pinned `OpenAI`/Anthropic SDK retry policy while making the
//! backoff sleep abortable; review when either SDK is upgraded.

use std::future::Future;

use eukhe_chord::context::AbortSignal;
use reqwest::header::HeaderMap;

use super::diagnostics::{ErrorObject, Thrown};
use super::js::{js_parse_float, number_to_js_string};
use super::now_ms;
use super::sleep::timer_duration;

const DEFAULT_MAX_RETRY_DELAY_MS: f64 = 60_000.0;

/// Options of [`retry_provider_request`].
#[derive(Debug, Clone, Default)]
pub struct ProviderRetryOptions {
    /// Retries after the first attempt. Default 0.
    pub max_retries: Option<u32>,
    /// Cap on a server-requested delay; above it the request fails at once.
    /// Default 60 000; 0 disables the cap.
    pub max_retry_delay_ms: Option<f64>,
    pub signal: Option<AbortSignal>,
    /// HTTP statuses that fail at once although the default policy would retry them.
    pub no_retry_statuses: Vec<u16>,
}

/// A provider SDK error (`status` and `headers` properties present, `status`
/// undefined or a number, `headers` undefined or `Headers`).
struct ProviderError<'a> {
    status: Option<f64>,
    headers: Option<&'a HeaderMap>,
    message: &'a str,
}

fn as_provider_error(error: &Thrown) -> Option<ProviderError<'_>> {
    let object = error.downcast_ref::<ErrorObject>()?;
    let status = match object.status.as_ref()? {
        None => None,
        Some(value) => Some(value.as_f64()?),
    };
    let headers = object.headers.as_ref()?.as_ref();
    Some(ProviderError {
        status,
        headers,
        message: &object.message,
    })
}

fn header(headers: Option<&HeaderMap>, name: &str) -> Option<String> {
    let values: Vec<String> = headers?
        .get_all(name)
        .iter()
        .map(|value| {
            value
                .as_bytes()
                .iter()
                .map(|&byte| char::from(byte))
                .collect()
        })
        .collect();
    (!values.is_empty()).then(|| values.join(", "))
}

fn is_retryable_provider_error(error: &ProviderError<'_>) -> bool {
    match header(error.headers, "x-should-retry").as_deref() {
        Some("true") => return true,
        Some("false") => return false,
        _ => {}
    }
    // HTTP statuses are whole numbers; compare them as integers.
    #[allow(clippy::cast_possible_truncation)]
    match error
        .status
        .map(|status| (status as i64, status.fract() == 0.0))
    {
        None => true,
        Some((status, whole)) => (whole && matches!(status, 408 | 409 | 429)) || status >= 500,
    }
}

fn validate_server_retry_delay_ms(
    delay_ms: f64,
    max_retry_delay_ms: Option<f64>,
    provider_error_message: &str,
) -> Result<f64, Thrown> {
    let max_delay_ms = max_retry_delay_ms.unwrap_or(DEFAULT_MAX_RETRY_DELAY_MS);
    if max_delay_ms > 0.0 && delay_ms > max_delay_ms {
        return Err(ErrorObject::new(format!(
            "Server requested {}s retry delay (max: {}s). {provider_error_message}",
            number_to_js_string((delay_ms / 1000.0).ceil()),
            number_to_js_string((max_delay_ms / 1000.0).ceil()),
        ))
        .thrown());
    }
    Ok(delay_ms)
}

fn get_retry_delay_ms(
    error: &ProviderError<'_>,
    retry_index: u32,
    max_retry_delay_ms: Option<f64>,
) -> Result<f64, Thrown> {
    if let Some(retry_after_ms) =
        header(error.headers, "retry-after-ms").filter(|value| !value.is_empty())
    {
        let value = js_parse_float(&retry_after_ms);
        if value.is_finite() {
            return validate_server_retry_delay_ms(value, max_retry_delay_ms, error.message);
        }
    }

    if let Some(retry_after) =
        header(error.headers, "retry-after").filter(|value| !value.is_empty())
    {
        let seconds = js_parse_float(&retry_after);
        let delay_ms = if seconds.is_nan() {
            // `Date.parse(retryAfter) - Date.now()`.
            #[allow(clippy::cast_precision_loss)]
            let now = now_ms() as f64;
            parse_http_date(&retry_after).map_or(f64::NAN, |date| date - now)
        } else {
            seconds * 1000.0
        };
        if delay_ms.is_finite() {
            return validate_server_retry_delay_ms(delay_ms, max_retry_delay_ms, error.message);
        }
    }

    let exponent = i32::try_from(retry_index).unwrap_or(i32::MAX);
    let exponential_delay = (0.5 * 2f64.powi(exponent)).min(8.0) * 1000.0;
    Ok(exponential_delay * (1.0 - rand::random::<f64>() * 0.25))
}

/// `Date.parse` of an HTTP-date (RFC 9110: IMF-fixdate, obsolete RFC 850,
/// or asctime), the formats a `Retry-After` date takes, in Unix milliseconds.
pub(crate) fn parse_http_date(text: &str) -> Option<f64> {
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let month_number = |name: &str| {
        MONTHS
            .iter()
            .position(|month| month.eq_ignore_ascii_case(name))
    };
    let parts: Vec<&str> = text
        .split([' ', ','])
        .filter(|part| !part.is_empty())
        .collect();
    let (day, month, year, time) = match parts.as_slice() {
        // IMF-fixdate: `Sun, 06 Nov 1994 08:49:37 GMT`; asctime: `Sun Nov  6 08:49:37 1994`.
        [_, day, month, year, time, "GMT"] | [_, month, day, time, year] => (
            day.parse().ok()?,
            month_number(month)?,
            year.parse::<i64>().ok()?,
            *time,
        ),
        // RFC 850: `Sunday, 06-Nov-94 08:49:37 GMT`.
        [_, date, time, "GMT"] => {
            let mut fields = date.split('-');
            let day = fields.next()?.parse().ok()?;
            let month = month_number(fields.next()?)?;
            let year: i64 = fields.next()?.parse().ok()?;
            (
                day,
                month,
                if year < 50 { 2000 + year } else { 1900 + year },
                *time,
            )
        }
        _ => return None,
    };
    let mut clock = time.split(':').map(str::parse::<i64>);
    let (hours, minutes, seconds) = (
        clock.next()?.ok()?,
        clock.next()?.ok()?,
        clock.next()?.ok()?,
    );
    if clock.next().is_some()
        || !(1..=31).contains(&day)
        || hours > 23
        || minutes > 59
        || seconds > 59
    {
        return None;
    }
    let month = i64::try_from(month).ok()? + 1;
    let days = days_from_civil(year, month, day);
    let millis = (((days * 24 + hours) * 60 + minutes) * 60 + seconds) * 1000;
    // Millisecond timestamps of real dates are far below 2^53.
    #[allow(clippy::cast_precision_loss)]
    Some(millis as f64)
}

/// Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's algorithm).
fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let month_index = (month + 9) % 12;
    let day_of_year = (153 * month_index + 2) / 5 + day - 1;
    let day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    era * 146_097 + day_of_era - 719_468
}

fn create_abort_error() -> Thrown {
    ErrorObject::named("AbortError", "Request aborted").thrown()
}

/// Sleep `ms` (at least 0) unless `signal` aborts.
async fn abortable_sleep(ms: f64, signal: Option<&AbortSignal>) -> Result<(), Thrown> {
    let duration = timer_duration(ms.max(0.0));
    let Some(signal) = signal else {
        tokio::time::sleep(duration).await;
        return Ok(());
    };
    if signal.aborted() {
        return Err(create_abort_error());
    }
    let token = signal.cancellation_token();
    tokio::select! {
        biased;
        () = token.cancelled() => Err(create_abort_error()),
        () = tokio::time::sleep(duration) => Ok(()),
    }
}

/// Reproduce the retry behavior of the `OpenAI` and Anthropic SDKs with an
/// interruptible backoff sleep (their built-in timers ignore the request
/// signal, so callers run the SDK request with no retries and wrap it here).
/// Server-requested delays above `max_retry_delay_ms` fail at once.
///
/// # Errors
///
/// The last request error; an `AbortError` ("Request aborted") when the
/// signal aborts; the retry-delay cap error.
pub async fn retry_provider_request<T, F, Fut>(
    mut request: F,
    options: &ProviderRetryOptions,
) -> Result<T, Thrown>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, Thrown>>,
{
    let max_retries = options.max_retries.unwrap_or(0);
    let mut retries_remaining = max_retries;
    loop {
        let error = match request().await {
            Ok(value) => return Ok(value),
            Err(error) => error,
        };
        if options.signal.as_ref().is_some_and(AbortSignal::aborted) {
            return Err(create_abort_error());
        }
        let Some(provider_error) = as_provider_error(&error) else {
            return Err(error);
        };
        if retries_remaining == 0 || !is_retryable_provider_error(&provider_error) {
            return Err(error);
        }
        if provider_error.status.is_some_and(|status| {
            options
                .no_retry_statuses
                .iter()
                .any(|&listed| f64::from(listed).total_cmp(&status).is_eq())
        }) {
            return Err(error);
        }
        let retry_index = max_retries - retries_remaining;
        retries_remaining -= 1;
        let delay = get_retry_delay_ms(&provider_error, retry_index, options.max_retry_delay_ms)?;
        abortable_sleep(delay, options.signal.as_ref()).await?;
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU32, Ordering};
    use std::sync::Arc;

    use eukhe_chord::context::AbortController;
    use reqwest::header::{HeaderName, HeaderValue};
    use serde_json::json;

    use super::*;
    use crate::utils::diagnostics::error_name;

    fn provider_error(status: Option<u16>, headers: &[(&str, &str)]) -> Thrown {
        let mut map = HeaderMap::new();
        for (name, value) in headers {
            map.insert(
                HeaderName::from_bytes(name.as_bytes()).unwrap(),
                HeaderValue::from_str(value).unwrap(),
            );
        }
        ErrorObject {
            status: Some(status.map(|status| json!(status))),
            headers: Some(Some(map)),
            ..ErrorObject::new(format!(
                "Provider error: {}",
                status.map_or_else(|| "undefined".to_owned(), |status| status.to_string())
            ))
        }
        .thrown()
    }

    /// A request that fails with `errors` in order, then succeeds with "ok".
    fn request(
        errors: Vec<Thrown>,
        calls: Arc<AtomicU32>,
    ) -> impl FnMut() -> std::future::Ready<Result<&'static str, Thrown>> {
        move || {
            let index = calls.fetch_add(1, Ordering::SeqCst) as usize;
            std::future::ready(errors.get(index).cloned().map_or(Ok("ok"), Err))
        }
    }

    #[tokio::test(start_paused = true)]
    async fn retries_retryable_provider_errors() {
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(1),
            ..ProviderRetryOptions::default()
        };
        let start = tokio::time::Instant::now();
        let result = retry_provider_request(
            request(
                vec![provider_error(Some(429), &[("retry-after-ms", "1000")])],
                calls.clone(),
            ),
            &options,
        )
        .await;
        assert_eq!(result.unwrap(), "ok");
        assert_eq!(calls.load(Ordering::SeqCst), 2);
        assert_eq!(start.elapsed(), std::time::Duration::from_millis(1000));
    }

    #[tokio::test]
    async fn does_not_retry_errors_the_provider_marks_as_non_retryable() {
        let error = provider_error(Some(429), &[("x-should-retry", "false")]);
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(2),
            ..ProviderRetryOptions::default()
        };
        let result = retry_provider_request(
            request(
                vec![error.clone(), error.clone(), error.clone()],
                calls.clone(),
            ),
            &options,
        )
        .await;
        assert!(Arc::ptr_eq(&result.unwrap_err(), &error));
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn does_not_retry_statuses_listed_in_no_retry_statuses() {
        let error = provider_error(Some(504), &[("retry-after-ms", "0")]);
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(2),
            no_retry_statuses: vec![504],
            ..ProviderRetryOptions::default()
        };
        let result = retry_provider_request(
            request(
                vec![error.clone(), error.clone(), error.clone()],
                calls.clone(),
            ),
            &options,
        )
        .await;
        assert!(Arc::ptr_eq(&result.unwrap_err(), &error));
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn rejects_a_provider_requested_retry_delay_above_the_limit() {
        let error = provider_error(Some(429), &[("retry-after", "277403")]);
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(1),
            max_retry_delay_ms: Some(1000.0),
            ..ProviderRetryOptions::default()
        };
        let result =
            retry_provider_request(request(vec![error.clone(), error], calls.clone()), &options)
                .await;
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Server requested 277403s retry delay (max: 1s)"));
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test(start_paused = true)]
    async fn allows_disabling_the_provider_requested_retry_delay_cap() {
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(1),
            max_retry_delay_ms: Some(0.0),
            ..ProviderRetryOptions::default()
        };
        let start = tokio::time::Instant::now();
        let result = retry_provider_request(
            request(
                vec![provider_error(Some(429), &[("retry-after", "2")])],
                calls.clone(),
            ),
            &options,
        )
        .await;
        assert_eq!(result.unwrap(), "ok");
        assert_eq!(calls.load(Ordering::SeqCst), 2);
        assert_eq!(start.elapsed(), std::time::Duration::from_millis(2000));
    }

    #[tokio::test]
    async fn aborts_a_provider_requested_retry_delay() {
        let controller = AbortController::new();
        let error = provider_error(Some(429), &[("retry-after", "277403")]);
        let calls = Arc::new(AtomicU32::new(0));
        let options = ProviderRetryOptions {
            max_retries: Some(2),
            max_retry_delay_ms: Some(0.0),
            signal: Some(controller.signal()),
            no_retry_statuses: Vec::new(),
        };
        let run = retry_provider_request(
            request(vec![error.clone(), error.clone(), error], calls.clone()),
            &options,
        );
        let abort = async {
            while calls.load(Ordering::SeqCst) == 0 {
                tokio::task::yield_now().await;
            }
            controller.abort(None);
        };
        let (result, ()) = tokio::join!(run, abort);
        assert_eq!(error_name(result.unwrap_err().as_ref()), "AbortError");
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn parses_http_dates() {
        let imf = parse_http_date("Sun, 06 Nov 1994 08:49:37 GMT").unwrap();
        assert!((imf - 784_111_777_000.0).abs() < f64::EPSILON);
        let rfc850 = parse_http_date("Sunday, 06-Nov-94 08:49:37 GMT").unwrap();
        assert!((rfc850 - imf).abs() < f64::EPSILON);
        let asctime = parse_http_date("Sun Nov  6 08:49:37 1994").unwrap();
        assert!((asctime - imf).abs() < f64::EPSILON);
        assert_eq!(parse_http_date("soon"), None);
    }
}
