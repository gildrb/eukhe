use super::*;
use crossterm::event::{MouseButton, MouseEvent as CtMouse, MouseEventKind as CtMouseKind};

fn esc_press() -> Event {
    Event::Key(KeyEvent::new(KeyCode::Esc, KeyModifiers::NONE))
}

fn char_press(c: char) -> Event {
    Event::Key(KeyEvent::new(KeyCode::Char(c), KeyModifiers::NONE))
}

/// The guard's view of a reader run: one feed per event on a 1 ms
/// clock, then one deadline flush.
fn run_guard(events: Vec<Event>) -> Vec<Event> {
    let mut guard = SequenceGuard::default();
    let mut now = Instant::now();
    let mut out = Vec::new();
    for event in events {
        out.extend(guard.feed(event, now));
        now += Duration::from_millis(1);
    }
    now += HOLD;
    out.extend(guard.flush_expired(now));
    out
}

fn sgr(button: u8, x: u16, y: u16, press: bool) -> String {
    format!("\x1b[<{button};{x};{y}{}", if press { 'M' } else { 'm' })
}

/// The SGR reports a real terminal emits with `?1002` + `?1006`
/// tracking: buttons, drags, releases, wheel, hover motion.
fn report_corpus() -> Vec<String> {
    vec![
        sgr(0, 13, 2, true),   // left press
        sgr(32, 14, 2, true),  // left drag
        sgr(0, 14, 2, false),  // left release
        sgr(64, 20, 5, true),  // wheel up
        sgr(65, 20, 5, true),  // wheel down
        sgr(0, 100, 30, true), // three-digit coordinates
        sgr(35, 7, 9, true),   // hover motion
        sgr(1, 3, 4, true),    // middle press
    ]
}

/// What leaked as key presses: events the editor would insert or act
/// on. A mouse report must never produce one.
fn leaks(outputs: &[Event]) -> Vec<Event> {
    outputs
        .iter()
        .filter(|event| matches!(event, Event::Key(_)))
        .cloned()
        .collect()
}

/// Every byte-offset split of one mouse report: a split at the `ESC`
/// byte commits the `Esc` and types the body, which the guard
/// reassembles and consumes whole (no output at all) -- except a wheel
/// report, which it decodes into the scroll event crossterm's own parse
/// produces; any later split is held across reads by crossterm itself,
/// which parses the whole report and the guard passes that mouse event
/// through unchanged.
fn assert_every_split_is_consumed_or_passed(stream: &[u8]) {
    let whole = read_projection(stream, &[]);
    assert!(
        matches!(whole.as_slice(), [Event::Mouse(_)]),
        "{stream:?} parses as one mouse event: {whole:?}"
    );
    assert_eq!(run_guard(whole.clone()), whole, "{stream:?} unsplit");
    let wheel = matches!(
        whole.as_slice(),
        [Event::Mouse(CtMouse {
            kind: CtMouseKind::ScrollUp | CtMouseKind::ScrollDown,
            ..
        })]
    );
    for split in 1..stream.len() {
        let events = read_projection(stream, &[split]);
        let outputs = run_guard(events.clone());
        let expected = if split == 1 && !wheel {
            Vec::new()
        } else {
            whole.clone()
        };
        assert_eq!(
            outputs, expected,
            "report {stream:?} split at {split}: {events:?} became {outputs:?}"
        );
    }
}

// -- the read-boundary defect and its repair ------------------------

/// The events crossterm 0.28.1's reader produces for a byte stream
/// split into OS reads after each `split_after` offset. Its
/// `Parser::advance` (event/source/unix/mio.rs) parses byte-by-byte,
/// holds an incomplete sequence across reads, clears on a parse
/// error, and passes `more = read_count == TTY_BUFFER_SIZE` -- so a
/// partial read ending on `ESC` parses `parse_event(b"\x1b",
/// more=false)` and commits an `Esc` press (event/sys/unix/parse.rs).
/// The model covers the forms this lane feeds it.
fn read_projection(stream: &[u8], split_after: &[usize]) -> Vec<Event> {
    let mut ends: Vec<usize> = split_after
        .iter()
        .copied()
        .filter(|&e| e > 0 && e < stream.len())
        .collect();
    ends.sort_unstable();
    ends.dedup();
    ends.push(stream.len());

    let mut events = Vec::new();
    let mut buf: Vec<u8> = Vec::new();
    let mut start = 0;
    for &end in &ends {
        let chunk = &stream[start..end];
        start = end;
        for (idx, &b) in chunk.iter().enumerate() {
            let more = idx + 1 < chunk.len();
            buf.push(b);
            match model_parse(&buf, more) {
                ModelParse::Event(event) => {
                    events.push(event);
                    buf.clear();
                }
                ModelParse::Invalid => buf.clear(),
                ModelParse::More => {}
            }
        }
    }
    events
}

enum ModelParse {
    Event(Event),
    More,
    Invalid,
}

/// crossterm 0.28.1's byte parser, the forms the projection corpus
/// reaches (plain bytes, SGR/X10 mouse, CSI keys, kitty CSI-u).
fn model_parse(buf: &[u8], more: bool) -> ModelParse {
    if buf[0] != 0x1b {
        if buf[0] >= 0x80 {
            // `parse_utf8_char`: an incomplete code point keeps
            // buffering (never an event), a complete one is the
            // character (SHIFT only on uppercase, like
            // `char_code_to_event`).
            return match std::str::from_utf8(buf) {
                Ok(text) => {
                    let ch = text.chars().next().expect("non-empty");
                    let modifiers = if ch.is_uppercase() {
                        KeyModifiers::SHIFT
                    } else {
                        KeyModifiers::NONE
                    };
                    ModelParse::Event(Event::Key(KeyEvent::new(KeyCode::Char(ch), modifiers)))
                }
                Err(error) if error.error_len().is_none() => ModelParse::More,
                Err(_) => ModelParse::Invalid,
            };
        }
        // The control rows of `parse_event`, then
        // `char_code_to_event` (uppercase bytes carry SHIFT).
        return match buf[0] {
            b'\r' => ModelParse::Event(Event::Key(KeyCode::Enter.into())),
            b'\t' => ModelParse::Event(Event::Key(KeyCode::Tab.into())),
            0x7f => ModelParse::Event(Event::Key(KeyCode::Backspace.into())),
            c @ 0x01..=0x1a => ModelParse::Event(Event::Key(KeyEvent::new(
                KeyCode::Char((c - 0x1 + b'a') as char),
                KeyModifiers::CONTROL,
            ))),
            c @ 0x1c..=0x1f => ModelParse::Event(Event::Key(KeyEvent::new(
                KeyCode::Char((c - 0x1c + b'4') as char),
                KeyModifiers::CONTROL,
            ))),
            0x00 => ModelParse::Event(Event::Key(KeyEvent::new(
                KeyCode::Char(' '),
                KeyModifiers::CONTROL,
            ))),
            c => {
                let ch = char::from_u32(u32::from(c)).expect("ascii corpus");
                let modifiers = if ch.is_uppercase() {
                    KeyModifiers::SHIFT
                } else {
                    KeyModifiers::NONE
                };
                ModelParse::Event(Event::Key(KeyEvent::new(KeyCode::Char(ch), modifiers)))
            }
        };
    }
    if buf.len() == 1 {
        // The defect: a lone `ESC` at a partial-read tail commits.
        return if more {
            ModelParse::More
        } else {
            ModelParse::Event(Event::Key(KeyCode::Esc.into()))
        };
    }
    match buf[1] {
        0x1b => ModelParse::Event(Event::Key(KeyCode::Esc.into())),
        b'[' => {
            if buf.len() == 2 {
                return ModelParse::More;
            }
            let payload = &buf[2..];
            let last = *payload.last().expect("non-empty");
            if payload[0] == b'M' {
                // X10: `ESC [ M Cb Cx Cy`.
                if buf.len() < 6 {
                    return ModelParse::More;
                }
                let kind = model_kind(buf[3].wrapping_sub(32), true).expect("corpus buttons");
                return ModelParse::Event(Event::Mouse(CtMouse {
                    kind,
                    column: u16::from(buf[4]) - 32 - 1,
                    row: u16::from(buf[5]) - 32 - 1,
                    modifiers: KeyModifiers::NONE,
                }));
            }
            if !(0x40..=0x7e).contains(&last) {
                return ModelParse::More;
            }
            if payload[0] == b'<' {
                if last != b'M' && last != b'm' {
                    return ModelParse::More;
                }
                let Ok(text) = std::str::from_utf8(&payload[1..payload.len() - 1]) else {
                    return ModelParse::Invalid;
                };
                let fields: Vec<&str> = text.split(';').collect();
                let (Ok(cb), Ok(x), Ok(y)) = (
                    fields[0].parse::<u8>(),
                    fields[1].parse::<u16>(),
                    fields[2].parse::<u16>(),
                ) else {
                    return ModelParse::Invalid;
                };
                let kind = model_kind(cb, last == b'M').expect("corpus buttons");
                let modifiers = model_modifiers(cb);
                return ModelParse::Event(Event::Mouse(CtMouse {
                    kind,
                    column: x - 1,
                    row: y - 1,
                    modifiers,
                }));
            }
            if payload[0] == b'[' {
                // `ESC [ [ <fin>`: parse_csi holds the three-byte
                // prefix for the fourth byte, then F1-F5 (any other
                // final byte is a parse error it drops whole).
                if buf.len() == 3 {
                    return ModelParse::More;
                }
                return match last {
                    val @ b'A'..=b'E' => {
                        ModelParse::Event(Event::Key(KeyCode::F(1 + val - b'A').into()))
                    }
                    _ => ModelParse::Invalid,
                };
            }
            match last {
                b'A' => ModelParse::Event(Event::Key(KeyCode::Up.into())),
                b'B' => ModelParse::Event(Event::Key(KeyCode::Down.into())),
                b'C' => ModelParse::Event(Event::Key(KeyCode::Right.into())),
                b'D' => ModelParse::Event(Event::Key(KeyCode::Left.into())),
                // rxvt mouse (`parse_csi_rxvt_mouse`): `cb ; cx ; cy`
                // behind a digit-led CSI, `M` at the end.
                b'M' if payload[0].is_ascii_digit() => {
                    let text = std::str::from_utf8(&payload[..payload.len() - 1])
                        .expect("corpus is ascii");
                    let mut fields = text.split(';');
                    let cb = fields
                        .next()
                        .and_then(|field| field.parse::<u8>().ok())
                        .and_then(|cb| cb.checked_sub(32))
                        .expect("corpus buttons");
                    let x: u16 = fields
                        .next()
                        .expect("corpus coordinates")
                        .parse()
                        .expect("corpus coordinates");
                    let y: u16 = fields
                        .next()
                        .expect("corpus coordinates")
                        .parse()
                        .expect("corpus coordinates");
                    let kind = model_kind(cb, true).expect("corpus buttons");
                    ModelParse::Event(Event::Mouse(CtMouse {
                        kind,
                        column: x - 1,
                        row: y - 1,
                        modifiers: model_modifiers(cb),
                    }))
                }
                b'u' => {
                    let text = std::str::from_utf8(&payload[..payload.len() - 1])
                        .expect("corpus is ascii");
                    let mut fields = text.split(';');
                    let codepoint: u32 = fields.next().expect("non-empty").parse().expect("corpus");
                    // `parse_csi_u_encoded_key_code`: the modifier
                    // mask rides the second field (the shift-enter
                    // corpus, `CSI 13;2u`).
                    let mut modifiers = KeyModifiers::empty();
                    if let Some(mods) = fields.next() {
                        let mask: u8 = mods
                            .split(':')
                            .next()
                            .unwrap_or_default()
                            .parse()
                            .expect("corpus");
                        modifiers = parse_modifiers(mask);
                    }
                    if (57399..=57426).contains(&codepoint) {
                        // translate_functional_key_code: the keypad
                        // block decodes to its characters, Enter, and
                        // navigation, with the KEYPAD state.
                        let code = match codepoint {
                            c @ 57399..=57408 => KeyCode::Char(
                                char::from_u32(c - 57399 + u32::from(b'0')).expect("digits"),
                            ),
                            57409 => KeyCode::Char('.'),
                            57410 => KeyCode::Char('/'),
                            57411 => KeyCode::Char('*'),
                            57412 => KeyCode::Char('-'),
                            57413 => KeyCode::Char('+'),
                            57414 => KeyCode::Enter,
                            57415 => KeyCode::Char('='),
                            57416 => KeyCode::Char(','),
                            57417 => KeyCode::Left,
                            57418 => KeyCode::Right,
                            57419 => KeyCode::Up,
                            57420 => KeyCode::Down,
                            57421 => KeyCode::PageUp,
                            57422 => KeyCode::PageDown,
                            57423 => KeyCode::Home,
                            57424 => KeyCode::End,
                            57425 => KeyCode::Insert,
                            57426 => KeyCode::Delete,
                            _ => unreachable!("the keypad range is checked above"),
                        };
                        return ModelParse::Event(Event::Key(KeyEvent::new_with_kind_and_state(
                            code,
                            KeyModifiers::NONE,
                            KeyEventKind::Press,
                            KeyEventState::KEYPAD,
                        )));
                    }
                    match codepoint {
                        27 => ModelParse::Event(Event::Key(KeyEvent::new(KeyCode::Esc, modifiers))),
                        // `\r` maps to Enter before the char row
                        // (crossterm's own match), so the corpus's
                        // `CSI 13;2u` projects Enter+SHIFT.
                        13 => {
                            ModelParse::Event(Event::Key(KeyEvent::new(KeyCode::Enter, modifiers)))
                        }
                        c => ModelParse::Event(Event::Key(KeyEvent::new(
                            KeyCode::Char(char::from_u32(c).expect("corpus")),
                            modifiers,
                        ))),
                    }
                }
                b'~' if payload == b"200~" || payload == b"201~" => ModelParse::Invalid,
                _ => ModelParse::Invalid,
            }
        }
        // crossterm's ESC branch re-parses the remaining bytes and
        // adds ALT: control bytes keep their control forms, ASCII and
        // UTF-8 characters are their key.
        _ => {
            let inner = &buf[1..];
            if inner[0] >= 0x80 {
                return match std::str::from_utf8(inner) {
                    Ok(text) => {
                        let ch = text.chars().next().expect("non-empty");
                        let mut modifiers = KeyModifiers::ALT;
                        if ch.is_uppercase() {
                            modifiers |= KeyModifiers::SHIFT;
                        }
                        ModelParse::Event(Event::Key(KeyEvent::new(KeyCode::Char(ch), modifiers)))
                    }
                    Err(error) if error.error_len().is_none() => ModelParse::More,
                    Err(_) => ModelParse::Invalid,
                };
            }
            let (code, modifiers) = match inner[0] {
                b'\r' => (KeyCode::Enter, KeyModifiers::ALT),
                b'\t' => (KeyCode::Tab, KeyModifiers::ALT),
                0x7f => (KeyCode::Backspace, KeyModifiers::ALT),
                c @ 0x01..=0x1a => (
                    KeyCode::Char((c - 0x1 + b'a') as char),
                    KeyModifiers::CONTROL | KeyModifiers::ALT,
                ),
                c @ 0x1c..=0x1f => (
                    KeyCode::Char((c - 0x1c + b'4') as char),
                    KeyModifiers::CONTROL | KeyModifiers::ALT,
                ),
                0x00 => (
                    KeyCode::Char(' '),
                    KeyModifiers::CONTROL | KeyModifiers::ALT,
                ),
                c => {
                    let ch = char::from_u32(u32::from(c)).expect("ascii corpus");
                    let mut modifiers = KeyModifiers::ALT;
                    if ch.is_uppercase() {
                        modifiers |= KeyModifiers::SHIFT;
                    }
                    (KeyCode::Char(ch), modifiers)
                }
            };
            ModelParse::Event(Event::Key(KeyEvent::new(code, modifiers)))
        }
    }
}

/// crossterm's `parse_cb`: the X10/SGR button byte to event kind. An SGR
/// release (`m`) turns a press report into a release.
fn model_kind(cb: u8, press: bool) -> Option<CtMouseKind> {
    let button = (cb & 0b0000_0011) | ((cb & 0b1100_0000) >> 4);
    let dragging = cb & 0b0010_0000 != 0;
    let kind = match (button, dragging) {
        (0, false) => CtMouseKind::Down(MouseButton::Left),
        (1, false) => CtMouseKind::Down(MouseButton::Middle),
        (2, false) => CtMouseKind::Down(MouseButton::Right),
        (0, true) => CtMouseKind::Drag(MouseButton::Left),
        (1, true) => CtMouseKind::Drag(MouseButton::Middle),
        (2, true) => CtMouseKind::Drag(MouseButton::Right),
        (3, false) => CtMouseKind::Up(MouseButton::Left),
        (3..=5, true) => CtMouseKind::Moved,
        (4, false) => CtMouseKind::ScrollUp,
        (5, false) => CtMouseKind::ScrollDown,
        (6, false) => CtMouseKind::ScrollLeft,
        (7, false) => CtMouseKind::ScrollRight,
        _ => return None,
    };
    Some(match (kind, press) {
        (CtMouseKind::Down(button), false) => CtMouseKind::Up(button),
        (kind, _) => kind,
    })
}

/// crossterm's `parse_cb` modifier bits: shift, alt (meta), control.
fn model_modifiers(cb: u8) -> KeyModifiers {
    let mut modifiers = KeyModifiers::empty();
    if cb & 0b0000_0100 != 0 {
        modifiers |= KeyModifiers::SHIFT;
    }
    if cb & 0b0000_1000 != 0 {
        modifiers |= KeyModifiers::ALT;
    }
    if cb & 0b0001_0000 != 0 {
        modifiers |= KeyModifiers::CONTROL;
    }
    modifiers
}

/// The live defect this port fixes (run 2026-09-22, raw-pty probe):
/// crossterm's `char_code_to_event` adds SHIFT to uppercase bytes, so
/// the report's final `M` arrives as `Char('M', SHIFT)` -- a rejected
/// continuation dropped the whole held sequence and leaked the `M`.
#[test]
fn a_report_final_m_arriving_shifted_is_still_consumed() {
    let events = vec![
        esc_press(),
        char_press('['),
        char_press('<'),
        char_press('0'),
        char_press(';'),
        char_press('1'),
        char_press('3'),
        char_press(';'),
        char_press('2'),
        Event::Key(KeyEvent::new(KeyCode::Char('M'), KeyModifiers::SHIFT)),
    ];
    assert_eq!(run_guard(events), Vec::new());
}

/// THE RACE, MADE DETERMINISTIC: a read ending right after the `ESC`
/// byte of a drag report makes crossterm commit an `Esc` press and
/// then type the report's body -- the "random escape sequences" Kevin
/// sees while selecting. Through the guard the same bytes are consumed
/// whole. Every byte-offset split of every report form is the fuzz:
/// never text, never a stray `Esc`.
#[test]
fn the_committed_esc_split_never_leaks_a_report() {
    for report in report_corpus() {
        assert_every_split_is_consumed_or_passed(report.as_bytes());
    }
}

/// A drag stream with one committed-`ESC` boundary inside one report:
/// that report is consumed and the rest pass through as the mouse
/// events crossterm parsed, so no stray text interrupts the stream.
#[test]
fn a_drag_burst_with_one_bad_boundary_never_leaks() {
    let stream: String = [
        sgr(0, 13, 2, true),
        sgr(32, 14, 2, true),
        sgr(32, 15, 3, true),
        sgr(32, 16, 3, true),
        sgr(0, 16, 3, false),
    ]
    .concat();
    // The boundary lands after the drag report's `ESC`.
    let second_start = stream.find("\x1b[<32;14;2").expect("drag report in stream");
    let events = read_projection(stream.as_bytes(), &[second_start + 1]);
    let outputs = run_guard(events);
    let mut expected = read_projection(stream.as_bytes(), &[]);
    assert_eq!(expected.len(), 5, "one mouse event per report");
    expected.remove(1);
    assert_eq!(outputs, expected);
}

/// The same split, doubled: the report body itself spans three reads
/// and is still consumed whole.
#[test]
fn a_report_split_across_three_reads_is_consumed() {
    let report = sgr(32, 20, 5, true);
    let mid = report.find(';').expect("field separator");
    let events = read_projection(report.as_bytes(), &[1, mid, mid + 3]);
    assert_eq!(run_guard(events), Vec::new());
}

/// A wheel report split anywhere -- the committed-`ESC` boundary, the
/// body across three reads, modifier bits, both wheel directions, a
/// release-final `m` -- reaches the reader as the scroll event the
/// unsplit read parses to, and never as text.
#[test]
fn a_split_wheel_report_decodes_to_the_scroll_event() {
    for report in [
        sgr(64, 20, 5, true),
        sgr(65, 1, 1, true),
        // Wheel up with shift and control; wheel down with alt, released.
        sgr(0b0101_0100, 120, 40, true),
        sgr(0b0100_1001, 7, 9, false),
    ] {
        let whole = read_projection(report.as_bytes(), &[]);
        assert!(
            matches!(
                whole.as_slice(),
                [Event::Mouse(CtMouse {
                    kind: CtMouseKind::ScrollUp | CtMouseKind::ScrollDown,
                    ..
                })]
            ),
            "{report:?} parses as a wheel event: {whole:?}"
        );
        let mid = report.find(';').expect("field separator");
        for splits in [vec![1], vec![1, mid], vec![1, mid, mid + 2]] {
            let events = read_projection(report.as_bytes(), &splits);
            assert_eq!(run_guard(events), whole, "{report:?} split at {splits:?}");
        }
    }
}

/// A wheel report and a key in one stream, the report split at its
/// `ESC`: the scroll event and then the key, in order.
#[test]
fn a_split_wheel_report_keeps_the_stream_order() {
    let stream = format!("{}x", sgr(65, 3, 4, true));
    let events = read_projection(stream.as_bytes(), &[1]);
    assert_eq!(run_guard(events), read_projection(stream.as_bytes(), &[]));
}

// -- held Esc behavior ----------------------------------------------

#[test]
fn a_held_esc_flushes_as_the_key_press_at_the_deadline() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    assert!(guard
        .flush_expired((now + HOLD).checked_sub(Duration::from_millis(1)).unwrap())
        .is_empty());
    assert_eq!(guard.flush_expired(now + HOLD), vec![esc_press()]);
}

#[test]
fn esc_then_a_character_within_the_window_is_the_alt_combo() {
    // crossterm's single-read parse of `\x1ba`: alt+a.
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    let mut expected = KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE);
    expected.modifiers |= KeyModifiers::ALT;
    assert_eq!(
        guard.feed(char_press('a'), now + Duration::from_millis(1)),
        vec![Event::Key(expected)]
    );
}

#[test]
fn esc_then_an_unrelated_key_flushes_the_esc_first() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    let left = Event::Key(KeyEvent::new(KeyCode::Left, KeyModifiers::NONE));
    assert_eq!(
        guard.feed(left.clone(), now + Duration::from_millis(1)),
        vec![esc_press(), left]
    );
}

#[test]
fn esc_then_a_parsed_mouse_event_flushes_the_esc_and_passes_the_event() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    let wheel = Event::Mouse(CtMouse {
        kind: CtMouseKind::ScrollUp,
        column: 3,
        row: 4,
        modifiers: KeyModifiers::NONE,
    });
    assert_eq!(
        guard.feed(wheel.clone(), now + Duration::from_millis(1)),
        vec![esc_press(), wheel],
        "the held Esc flushes first, the event passes unchanged"
    );
}

#[test]
fn a_half_assembled_sequence_is_dropped_at_the_deadline_never_typed() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    for (offset, c) in ['[', '<', '6', '4'].iter().enumerate() {
        assert!(guard
            .feed(
                char_press(*c),
                now + Duration::from_millis(offset as u64 + 1)
            )
            .is_empty());
    }
    assert!(guard
        .flush_expired(now + HOLD + Duration::from_millis(4))
        .is_empty());
}

#[test]
fn a_non_keyboard_event_flushes_the_held_esc_first() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    let resize = Event::Resize(80, 24);
    let outputs = guard.feed(resize.clone(), now + Duration::from_millis(1));
    assert_eq!(outputs, vec![esc_press(), resize]);
}

#[test]
fn poll_deadline_parks_when_nothing_is_held() {
    let guard = SequenceGuard::default();
    assert_eq!(guard.poll_deadline(Instant::now()), None);
}

#[test]
fn poll_deadline_is_the_remaining_hold() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    assert_eq!(
        guard.poll_deadline(now + Duration::from_millis(6)),
        Some(Duration::from_millis(4))
    );
    assert_eq!(guard.poll_deadline(now + HOLD), Some(Duration::ZERO));
}

// -- reassembled key sequences --------------------------------------

#[test]
fn a_split_arrow_key_arrives_as_the_key() {
    let outputs = run_guard(read_projection(b"\x1b[A", &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(KeyCode::Up, KeyModifiers::NONE))]
    );
}

#[test]
fn a_split_modified_nav_key_keeps_its_modifiers() {
    let outputs = run_guard(read_projection(b"\x1b[1;5A", &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(
            KeyCode::Up,
            KeyModifiers::CONTROL
        ))]
    );
}

#[test]
fn a_split_kitty_esc_press_stays_the_escape_key() {
    let outputs = run_guard(read_projection(b"\x1b[27u", &[1]));
    assert_eq!(leaks(&outputs), vec![esc_press()]);
}

#[test]
fn a_split_csi_u_printable_arrives_as_the_character() {
    let outputs = run_guard(read_projection(b"\x1b[97u", &[1]));
    assert_eq!(leaks(&outputs), vec![char_press('a')]);
}

#[test]
fn every_split_of_an_x10_mouse_report_is_consumed_or_passed() {
    // `ESC [ M Cb Cx Cy` with Cb=0x20 (left press), Cx=0x21, Cy=0x22.
    assert_every_split_is_consumed_or_passed(&[0x1b_u8, b'[', b'M', 0x20, 0x21, 0x22]);
}

/// An OSC reply split at its `ESC` byte is consumed whole -- no
/// `52;c;<base64>` text in the editor.
#[test]
fn a_split_osc_reply_is_consumed_whole() {
    let outputs = run_guard(read_projection(b"\x1b]52;c;YWJj\x07", &[1]));
    assert_eq!(outputs, Vec::new());
}

/// A bracketed-paste marker split at its `ESC` byte is consumed; the
/// pasted text still flows as the characters it is.
#[test]
fn a_split_bracketed_paste_marker_is_consumed_and_the_text_flows() {
    let outputs = run_guard(read_projection(b"\x1b[200~hi", &[1]));
    assert_eq!(outputs, vec![char_press('h'), char_press('i')]);
}

/// A paste-end marker split the same way is consumed too.
#[test]
fn a_split_bracketed_paste_end_marker_is_consumed() {
    let outputs = run_guard(read_projection(b"\x1b[201~", &[1]));
    assert!(leaks(&outputs).is_empty());
}

// -- the review fixes: expiry, rxvt, keypad CSI-u, UTF-8 ALT ------

/// A continuation arriving after the hold expired is a fresh input,
/// never an Alt combo: the held `Esc` flushes first (TS's timer fired
/// before the event landed, and TS never lets a late keystroke join
/// a flushed buffer).
#[test]
fn an_expired_hold_flushes_the_esc_before_the_next_key() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    assert_eq!(
        guard.feed(char_press('a'), now + HOLD + Duration::from_millis(1)),
        vec![esc_press(), char_press('a')]
    );
}

/// A half-assembled sequence at its deadline drops whole and the late
/// keystroke passes as text: TS's timer flushes the raw remainder and
/// its parser drops the escape form.
#[test]
fn an_expired_half_assembled_sequence_drops_and_the_key_types() {
    let mut guard = SequenceGuard::default();
    let now = Instant::now();
    assert!(guard.feed(esc_press(), now).is_empty());
    assert!(guard
        .feed(char_press('['), now + Duration::from_millis(1))
        .is_empty());
    assert_eq!(
        guard.feed(char_press('x'), now + HOLD + Duration::from_millis(2)),
        vec![char_press('x')]
    );
}

/// rxvt mouse reports (`ESC [ cb ; cx ; cy ; M`, mode 1015): every
/// split is consumed or passes as crossterm's own parse, never typing
/// its body.
#[test]
fn every_split_of_an_rxvt_report_is_consumed_or_passed() {
    // `cb ; cx ; cy` fields are the X10 button byte plus 32
    // (parse_csi_rxvt_mouse): 32 is a plain left press, 64 the
    // motion-bit drag form.
    assert_every_split_is_consumed_or_passed(b"\x1b[32;30;40;M");
    assert_every_split_is_consumed_or_passed(b"\x1b[64;30;40;M");
    // Malformed fields are consumed the same way.
    let outputs = run_guard(read_projection(b"\x1b[0;0;0M", &[1]));
    assert_eq!(outputs, Vec::new());
}

/// A split kitty keypad report decodes as the key the unsplit parse
/// delivers (`CSI 57399u` is keypad-0, `CSI 57414u` keypad Enter)
/// with the KEYPAD state crossterm stamps on it -- not swallowed by
/// the private-use blanket.
#[test]
fn a_split_keypad_csi_u_arrives_as_the_key() {
    let outputs = run_guard(read_projection(b"\x1b[57399u", &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new_with_kind_and_state(
            KeyCode::Char('0'),
            KeyModifiers::NONE,
            KeyEventKind::Press,
            KeyEventState::KEYPAD,
        ))]
    );
    let outputs = run_guard(read_projection(b"\x1b[57414u", &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new_with_kind_and_state(
            KeyCode::Enter,
            KeyModifiers::NONE,
            KeyEventKind::Press,
            KeyEventState::KEYPAD,
        ))]
    );
    // The rest of the functional range stays consumed (TS drops it
    // too, and no surface dispatches it).
    let outputs = run_guard(read_projection(b"\x1b[57427u", &[1]));
    assert_eq!(outputs, Vec::new());
}

/// The legacy function-key form `ESC [ [ A` splits at its `ESC`
/// exactly the way TS's own `StdinBuffer` splits it: the buffer
/// completes the three-byte prefix `\x1b[[` at its
/// `isCompleteCsiSequence` boundary (the final byte `[` is in the
/// 0x40-0x7e range), TS's `parseKey` drops the prefix, and the
/// trailing byte types as text -- so the split path stays TS-exact.
/// crossterm's unsplit parse holds the prefix for a fourth byte and
/// delivers F1; that TS/crossterm divergence is the products' own,
/// and this guard does not widen it either way.
#[test]
fn a_split_legacy_function_key_form_stays_ts_exact() {
    let outputs = run_guard(read_projection(b"\x1b[[A", &[1]));
    assert_eq!(
        outputs,
        vec![Event::Key(KeyEvent::new(
            KeyCode::Char('A'),
            KeyModifiers::SHIFT
        ))]
    );
}

/// `ESC` + a multi-byte character is the character with ALT: the
/// guard must reassemble the whole UTF-8 bytes, not drop the combo
/// for not being an ASCII single byte (crossterm never splits a
/// character across events, so the tail is always one character).
#[test]
fn a_split_alt_modified_character_keeps_the_alt() {
    // Alt+é: `\x1b` then the two UTF-8 bytes of é.
    let outputs = run_guard(read_projection("\x1b\u{e9}".as_bytes(), &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(
            KeyCode::Char('\u{e9}'),
            KeyModifiers::ALT
        ))]
    );
    // Alt+É arrives SHIFT-modified (crossterm adds SHIFT to
    // uppercase characters).
    let outputs = run_guard(read_projection("\x1b\u{c9}".as_bytes(), &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(
            KeyCode::Char('\u{c9}'),
            KeyModifiers::ALT | KeyModifiers::SHIFT
        ))]
    );
}

/// `ESC` + a 0x1c-0x1f control byte is Ctrl+4..7 with ALT
/// (crossterm reports those bytes as `Char('4'..='7')` with
/// CONTROL): the guard's reverse map must know that row.
#[test]
fn a_split_alt_ctrl_digit_reconstructs_the_combo() {
    let outputs = run_guard(read_projection(b"\x1b\x1c", &[1]));
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(
            KeyCode::Char('4'),
            KeyModifiers::CONTROL | KeyModifiers::ALT
        ))]
    );
}

/// A split kitty shift+enter (`CSI 13;2u`) reassembles into exactly
/// the Enter+SHIFT event the unsplit parse delivers, at every read
/// boundary -- the operator's 2026-09-24 shift+enter directive rides
/// the same seam every kitty key does.
#[test]
fn a_split_kitty_shift_enter_arrives_as_the_shift_enter_key() {
    for split in [1usize, 2, 5, 8] {
        let events = read_projection(b"\x1b[13;2u", &[split]);
        let outputs = run_guard(events.clone());
        assert_eq!(
            leaks(&outputs),
            vec![Event::Key(KeyEvent::new(
                KeyCode::Enter,
                KeyModifiers::SHIFT
            ))],
            "split at {split}: {events:?} as {outputs:?}"
        );
    }
    // The unsplit form passes through untouched (the guard is
    // invisible): crossterm's own parse of `CSI 13;2u` is the same
    // event.
    let outputs = run_guard(vec![Event::Key(KeyEvent::new(
        KeyCode::Enter,
        KeyModifiers::SHIFT,
    ))]);
    assert_eq!(
        leaks(&outputs),
        vec![Event::Key(KeyEvent::new(
            KeyCode::Enter,
            KeyModifiers::SHIFT
        ))]
    );
}

/// The composed seam: a split kitty shift+enter reassembles through
/// the guard, decodes to the `shift+enter` key id, and lands in the
/// editor as a newline -- never a submit.
#[test]
fn a_split_shift_enter_inserts_a_newline_in_the_editor() {
    let outputs = run_guard(read_projection(b"\x1b[13;2u", &[1]));
    let key = leaks(&outputs)
        .into_iter()
        .find_map(|event| match event {
            Event::Key(key) => Some(key),
            _ => None,
        })
        .expect("the shift+enter key");
    let id = crate::keys::key_event_to_id(&key).expect("the key id");
    assert_eq!(id, "shift+enter");
    let mut editor = crate::editor::Editor::new();
    editor.handle_input("a");
    editor.handle_input(&id);
    assert_eq!(editor.get_lines(), vec!["a", ""]);
    // The newline press carries only its Changed event -- a submit
    // never rides along.
    assert!(
        editor
            .take_events()
            .into_iter()
            .all(|event| !matches!(event, crate::editor::EditorEvent::Submitted(_))),
        "the newline press never submits"
    );
}
