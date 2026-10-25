//! Where a built-in storage scan starts (`bend/scan.bend`, entry
//! `bend/ffi_scan.bend`; `laws/scan.bend`): the order a scan runs in,
//! whether it continues after its cursor's id, and the refusal of a bad
//! cursor or of a query that asks for another order. Each function encodes
//! what the caller read of the cursor, calls [`Entry::Scan`] and decodes the
//! answer.

use crate::wire::{Reader, Writer};
use crate::{call, Entry, Error};

/// The order of a scan (`Sc.Order`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Order {
    Ascending,
    Descending,
}

/// What a cursor's `after` field is (`Sc.After`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum After {
    /// The cursor has no `after`.
    Absent,
    /// `after` is not a safe integer.
    NotSafe,
    /// `after` is a safe integer (the caller keeps it).
    Safe,
}

/// What a cursor's `order` field is (`Sc.Mark`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mark {
    /// The cursor has no `order`.
    Absent,
    /// `"ascending"`.
    Ascending,
    /// `"descending"`.
    Descending,
    /// Anything else.
    Other,
}

/// A cursor, as the caller read it (`Sc.Cursor`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cursor {
    pub after: After,
    pub mark: Mark,
}

/// Where a scan starts (`Sc.Start`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Start {
    /// In `order`, after the cursor's id when `after`, else from the start.
    Begin { order: Order, after: bool },
    /// The request is refused with this text.
    Refused(String),
}

/// The cursor id of a backend scan (`Sc.Id`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Id {
    /// No id: the scan starts from the beginning.
    Absent,
    /// The cursor's `after` id.
    After,
    /// The cursor is refused with this text.
    Refused(String),
}

fn put_after(request: &mut Writer, after: After) {
    request.tag(match after {
        After::Absent => 0,
        After::NotSafe => 1,
        After::Safe => 2,
    });
}

fn put_order(request: &mut Writer, order: Order) {
    request.tag(match order {
        Order::Ascending => 0,
        Order::Descending => 1,
    });
}

/// Where a scan starts (`Sc.start`): without a cursor at the beginning, in
/// `asked` (else `fallback`); with one, after its id in its own order (in
/// `fallback` when it names none), unless a field is bad or `asked` is
/// another order.
///
/// # Errors
///
/// Only from an inconsistent build (see [`crate::expect_core`]).
pub fn start(
    asked: Option<Order>,
    cursor: Option<Cursor>,
    fallback: Order,
) -> Result<Start, Error> {
    let mut request = Writer::new();
    request.tag(0);
    match asked {
        None => request.tag(0),
        Some(Order::Ascending) => request.tag(1),
        Some(Order::Descending) => request.tag(2),
    };
    match cursor {
        None => {
            request.tag(0);
        }
        Some(Cursor { after, mark }) => {
            request.tag(1);
            put_after(&mut request, after);
            request.tag(match mark {
                Mark::Absent => 0,
                Mark::Ascending => 1,
                Mark::Descending => 2,
                Mark::Other => 3,
            });
        }
    }
    put_order(&mut request, fallback);
    let reply = call(Entry::Scan, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let start = match reply.tag_of(2, "a scan start")? {
        0 => {
            let order = match reply.tag_of(2, "an order")? {
                0 => Order::Ascending,
                _ => Order::Descending,
            };
            Start::Begin {
                order,
                after: reply.bool()?,
            }
        }
        _ => Start::Refused(reply.str()?.to_string()),
    };
    reply.end()?;
    Ok(start)
}

/// The cursor id of a backend scan (`Sc.cursor_id`), from the cursor's
/// `after` field (`None`: no cursor).
///
/// # Errors
///
/// As [`start`].
pub fn cursor_id(after: Option<After>) -> Result<Id, Error> {
    let mut request = Writer::new();
    request.tag(1);
    match after {
        None => {
            request.tag(0);
        }
        Some(after) => {
            request.tag(1);
            put_after(&mut request, after);
        }
    }
    let reply = call(Entry::Scan, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let id = match reply.tag_of(3, "a cursor id")? {
        0 => Id::Absent,
        1 => Id::After,
        _ => Id::Refused(reply.str()?.to_string()),
    };
    reply.end()?;
    Ok(id)
}

#[cfg(test)]
mod tests {
    use super::{cursor_id, start, After, Cursor, Id, Mark, Order, Start};

    #[test]
    fn the_codec_carries_each_question_through_the_core() {
        assert_eq!(
            start(
                Some(Order::Descending),
                Some(Cursor {
                    after: After::Safe,
                    mark: Mark::Ascending
                }),
                Order::Ascending
            )
            .unwrap(),
            Start::Refused(
                "The cursor continues a ascending scan; the query asks for descending".to_string()
            )
        );
        assert_eq!(
            start(None, None, Order::Descending).unwrap(),
            Start::Begin {
                order: Order::Descending,
                after: false
            }
        );
        assert_eq!(cursor_id(Some(After::Safe)).unwrap(), Id::After);
    }
}
