//! The runtime socket ([`TungsteniteWebSocket`]) against a local WebSocket
//! server: the Rust counterpart of the runtime `WebSocket` the TS tests
//! replace with mocks.

use eukhe_types::pi_ai::{IndexMap, JsonObject, StopReason, Transport};
use futures::{SinkExt, StreamExt};
use serde_json::json;
use tokio::net::TcpListener;
use tokio_tungstenite::tungstenite::handshake::server::{Request, Response};
use tokio_tungstenite::tungstenite::Message;

use super::super::stream;
use super::super::tungstenite_socket::TungsteniteWebSocket;
use super::super::websocket::{WebSocketData, WebSocketEvent};
use super::support::{first_text, hello_events, isolate, mock_token, model_with, say_hello};
use crate::types::{ProviderStreamOptions, StreamOptions};

#[tokio::test]
#[allow(clippy::result_large_err)] // The handshake callback type is tungstenite's.
async fn runtime_socket_opens_exchanges_messages_and_reports_the_close() {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let server = tokio::spawn(async move {
        let (tcp, _) = listener.accept().await.expect("accept");
        let mut seen_header = None;
        let mut socket =
            tokio_tungstenite::accept_hdr_async(tcp, |request: &Request, response: Response| {
                seen_header = request
                    .headers()
                    .get("x-test")
                    .and_then(|value| value.to_str().ok())
                    .map(str::to_owned);
                Ok(response)
            })
            .await
            .expect("handshake");
        let frame = socket.next().await.expect("frame").expect("message");
        socket.send(frame).await.expect("echo");
        socket.close(None).await.expect("close");
        seen_header
    });

    let mut headers = IndexMap::new();
    headers.insert("x-test".to_owned(), "yes".to_owned());
    let socket =
        TungsteniteWebSocket::connect(&format!("ws://{address}/"), headers, None).expect("socket");
    let mut listener = socket.listen();
    assert_eq!(listener.next().await, WebSocketEvent::Open);
    assert_eq!(socket.ready_state(), Some(1));
    socket.send("ping".to_owned()).expect("send");
    assert_eq!(
        listener.next().await,
        WebSocketEvent::Message(WebSocketData::Text("ping".to_owned()))
    );
    assert!(matches!(
        listener.next().await,
        WebSocketEvent::Close {
            code: Some(1005),
            ..
        }
    ));
    assert_eq!(socket.ready_state(), Some(3));
    assert_eq!(server.await.expect("server").as_deref(), Some("yes"));
}

#[tokio::test]
async fn runtime_socket_connect_failure_is_an_error_event() {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    drop(listener);
    let url = format!("ws://{address}/");
    let socket = TungsteniteWebSocket::connect(&url, IndexMap::new(), None).expect("socket");
    let mut listener = socket.listen();
    assert_eq!(
        listener.next().await,
        WebSocketEvent::Error {
            message: Some(format!(
                "WebSocket connection to '{url}' failed: Failed to connect"
            )),
        }
    );
}

#[tokio::test]
async fn streams_over_the_runtime_websocket() {
    let _isolation = isolate().await;
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let server = tokio::spawn(async move {
        let (tcp, _) = listener.accept().await.expect("accept");
        let mut socket = tokio_tungstenite::accept_async(tcp)
            .await
            .expect("handshake");
        let Some(Ok(Message::Text(frame))) = socket.next().await else {
            panic!("expected a text frame");
        };
        let mut events = hello_events();
        events.push(json!({
            "type": "response.completed",
            "response": { "id": "resp_1", "status": "completed", "usage": { "input_tokens": 1, "output_tokens": 1, "total_tokens": 2 } },
        }));
        for event in events {
            socket
                .send(Message::text(event.to_string()))
                .await
                .expect("send");
        }
        serde_json::from_str::<serde_json::Value>(frame.as_str()).expect("json frame")
    });
    let model = model_with(json!({ "baseUrl": format!("http://{address}") }));
    let mut options = StreamOptions {
        transport: Some(Transport::Websocket),
        ..StreamOptions::default()
    };
    options.request.api_key = Some(mock_token("acc_test"));

    let result = stream(
        &model,
        &say_hello(),
        ProviderStreamOptions {
            stream: options,
            extra: JsonObject::new(),
        },
    )
    .result()
    .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    let frame = server.await.expect("server");
    assert_eq!(frame["type"], json!("response.create"));
    assert_eq!(frame["model"], json!("gpt-5.1-codex"));
}
