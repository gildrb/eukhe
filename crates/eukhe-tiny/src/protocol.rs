//! The worker protocol: one JSON object a line over the worker's Unix
//! socket. A client writes a [`Request`] line; the worker answers each with
//! exactly one [`Response`] line, in order. Prompt construction and output
//! parsing stay in the client, so any worker that speaks these messages
//! serves any client.

use std::io;

use serde::{Deserialize, Serialize};
use tokio::io::{AsyncBufRead, AsyncBufReadExt};

/// The longest request or response line either side reads: 256 MiB, about
/// 20 minutes of 16 kHz audio as JSON samples.
pub(crate) const MAX_LINE_BYTES: usize = 256 << 20;

/// One line of the protocol, as [`read_line`] reads it.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Line {
    /// A line, without its `\n` (or `\r\n`).
    Text(String),
    /// A line over the limit, read past without keeping it; the next line
    /// follows.
    TooLong,
    /// The peer closed before another byte.
    End,
}

/// Reads the next line of at most `limit` bytes. The bytes of a longer
/// line are consumed and dropped, so memory stays bounded and the stream
/// stays in step. A last line without `\n` counts as a line.
///
/// # Errors
///
/// The reader fails, or the line is not UTF-8
/// ([`io::ErrorKind::InvalidData`]).
pub(crate) async fn read_line<R: AsyncBufRead + Unpin>(
    reader: &mut R,
    limit: usize,
) -> io::Result<Line> {
    let mut line = Vec::new();
    let mut too_long = false;
    let mut read_any = false;
    loop {
        let available = reader.fill_buf().await?;
        if available.is_empty() {
            break;
        }
        read_any = true;
        let (length, ended) = match available.iter().position(|byte| *byte == b'\n') {
            Some(at) => (at, true),
            None => (available.len(), false),
        };
        if !too_long {
            if line.len() + length > limit {
                too_long = true;
                line = Vec::new();
            } else {
                line.extend_from_slice(&available[..length]);
            }
        }
        reader.consume(length + usize::from(ended));
        if ended {
            break;
        }
    }
    if !read_any {
        return Ok(Line::End);
    }
    if too_long {
        return Ok(Line::TooLong);
    }
    if line.last() == Some(&b'\r') {
        line.pop();
    }
    String::from_utf8(line)
        .map(Line::Text)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

/// A message from a client to the worker.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Request {
    /// Answered with [`Reply::Pong`]: the worker's launch tag.
    Ping,
    /// Loads the model now (the first inference loads it otherwise).
    Load,
    /// Text generation (a text model).
    Chat(ChatRequest),
    /// Speech to text (a speech-to-text model).
    Transcribe(TranscribeRequest),
    /// Text to speech (a text-to-speech model).
    Speak(SpeakRequest),
    /// The worker unlinks its socket, answers [`Reply::Bye`] and exits.
    Shutdown,
}

/// The speaker of one chat message.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ChatRole {
    System,
    User,
    Assistant,
}

/// One message of a chat prompt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChatMessage {
    pub role: ChatRole,
    pub content: String,
}

/// A greedy completion of a chat prompt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChatRequest {
    pub messages: Vec<ChatMessage>,
    /// Text the assistant turn starts with (empty: none). The reply holds
    /// only what the model wrote after it.
    pub prefill: String,
    /// Generation ends before the first of these strings.
    pub stop: Vec<String>,
    /// Generation ends after this many new tokens.
    pub max_tokens: u32,
}

/// Why a completion ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StopReason {
    /// The model wrote its end-of-sequence token.
    Eos,
    /// The output reached one of the stop strings.
    Stop,
    /// The output reached `max_tokens`.
    Length,
}

/// The completion: the text after the prefill, before any stop string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChatReply {
    pub text: String,
    pub stop: StopReason,
}

/// Mono audio samples in `-1.0..=1.0`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Audio {
    pub sample_rate: u32,
    pub samples: Vec<f32>,
}

/// Speech to text of one clip.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TranscribeRequest {
    pub audio: Audio,
    /// An ISO 639-1 code (`en`), or empty: the model detects the language.
    pub language: String,
}

/// The text of a clip and its language (ISO 639-1).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Transcript {
    pub text: String,
    pub language: String,
}

/// Text to speech.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SpeakRequest {
    pub text: String,
    /// A voice id of the model (Kokoro: `af_heart`); empty: its default.
    pub voice: String,
    /// The speaking rate, `1.0` normal.
    pub speed: f32,
}

/// The answer to one request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Response {
    Ok { reply: Reply },
    Err { error: WorkerFailure },
}

/// What a request produced.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Reply {
    Pong { tag: String },
    Loaded,
    Chat(ChatReply),
    Transcript(Transcript),
    Speech(Audio),
    Bye,
}

/// Why the worker could not serve a request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum WorkerFailure {
    /// The model's files are missing or fail to load (or the runtime library).
    #[error("model load failed: {message}")]
    Load { message: String },
    /// The model does not do this kind of request (chat on a TTS model).
    #[error("the model does not serve {op}")]
    Unsupported { op: String },
    /// Inference failed.
    #[error("inference failed: {message}")]
    Inference { message: String },
    /// The request line was not a [`Request`].
    #[error("bad request: {message}")]
    BadRequest { message: String },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn a_line_over_the_limit_is_skipped_and_the_next_one_read() {
        let mut input: &[u8] = b"short\r\nxxxxxxxxxxxxxxxxxxxx\nnext\nlast";
        let mut lines = Vec::new();
        loop {
            let line = read_line(&mut input, 10).await.unwrap();
            let end = line == Line::End;
            lines.push(line);
            if end {
                break;
            }
        }
        assert_eq!(
            lines,
            vec![
                Line::Text("short".to_owned()),
                Line::TooLong,
                Line::Text("next".to_owned()),
                Line::Text("last".to_owned()),
                Line::End,
            ]
        );
    }
}
