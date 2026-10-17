//! The `DeepSeek` dialect: the account balance (`GET /user/balance`).

use eukhe_types::pi_ai::JsonValue;

use super::http::{api_key, header_source, send, unexpected, unversioned_root, Body, Call};
use super::{AccountUsage, Balance};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

const LABEL: &str = "DeepSeek";

/// The account's balances.
pub(crate) async fn usage(
    model: &Model,
    options: &ProviderRequestOptions,
) -> Result<AccountUsage, Thrown> {
    let key = api_key(model, options)?;
    let body = send(
        model,
        options,
        Call {
            label: LABEL,
            url: format!("{}/user/balance", unversioned_root(&model.base_url)),
            defaults: header_source([("authorization", format!("Bearer {key}"))]),
            body: Body::Get,
        },
    )
    .await?;
    let text = |info: &JsonValue, field: &str| -> Result<String, Thrown> {
        info.get(field)
            .and_then(JsonValue::as_str)
            .map(str::to_owned)
            .ok_or_else(|| unexpected(LABEL, "balance"))
    };
    let balances = body
        .get("balance_infos")
        .and_then(JsonValue::as_array)
        .ok_or_else(|| unexpected(LABEL, "balance"))?
        .iter()
        .map(|info| {
            Ok(Balance {
                currency: text(info, "currency")?,
                total: text(info, "total_balance")?,
                granted: text(info, "granted_balance")?,
                topped_up: text(info, "topped_up_balance")?,
            })
        })
        .collect::<Result<Vec<_>, Thrown>>()?;
    Ok(AccountUsage::Balance {
        available: body
            .get("is_available")
            .and_then(JsonValue::as_bool)
            .ok_or_else(|| unexpected(LABEL, "balance"))?,
        balances,
    })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::capabilities::mock_server::{headers, model, options, serve, Recorded, Reply};

    #[tokio::test]
    async fn usage_reads_the_balance_endpoint() {
        let (root, server) = serve(vec![Reply::ok(json!({
            "is_available": true,
            "balance_infos": [{
                "currency": "USD",
                "total_balance": "110.00",
                "granted_balance": "10.00",
                "topped_up_balance": "100.00"
            }]
        }))])
        .await;
        let model = model("deepseek", "openai-completions", "deepseek-chat", &root);
        let usage = usage(&model, &options("ds-key")).await.expect("usage");
        assert_eq!(
            usage,
            AccountUsage::Balance {
                available: true,
                balances: vec![Balance {
                    currency: "USD".to_owned(),
                    total: "110.00".to_owned(),
                    granted: "10.00".to_owned(),
                    topped_up: "100.00".to_owned(),
                }],
            }
        );
        assert_eq!(
            server.await.expect("server"),
            vec![Recorded {
                method: "GET".to_owned(),
                path: "/user/balance".to_owned(),
                headers: headers([
                    ("accept", "application/json"),
                    ("authorization", "Bearer ds-key"),
                ]),
                body: None,
            }]
        );
    }
}
