//! The render surface: the frame composer (splash, search prompt,
//! sectioned list, hints), the row builders, the notice/list/row
//! renderers, the cell/truncate helpers, and the inline-terminal/
//! headless renderer (moved with their concern).
use super::{
    build_layout, mpsc, pad_line, section_title, str_width, truncate_text, AgentsStep,
    AgentsViewMode, AgentsViewRow, AgentsViewUiMode, Composer, Duration, Line, Result, RowKind,
    RowLayout, Section, Theme, ThemeColor, UiInput, Value,
};
use crate::glyphs;
use crate::inline_term::{InlineFrame, InlineTerminal, LiveCursor};

impl AgentsViewMode {
    /// Compose one frame (splash, search prompt, sectioned list, hints):
    /// the live area, as tall as its content and never taller than
    /// `height`.
    pub(super) fn render_frame(
        &mut self,
        width: usize,
        height: usize,
    ) -> (Vec<Line>, Option<(usize, usize)>) {
        // The frame height feeds the page step (TS reads
        // `ui.terminal.rows` live at key time instead).
        self.last_height = height;
        let mut lines: Vec<Line> = Vec::new();
        // TS `getAgentCountsText` rides the splash as extra metadata. Like
        // TS `countRowsBySection`, it counts agent-kind rows only -- nested
        // subagent and summary rows never inflate the header.
        let count_agents = |section: Section| {
            self.rows
                .iter()
                .filter(|row| row.kind == RowKind::Agent && row.section == section)
                .count()
        };
        let (running, idle, inactive) = (
            count_agents(Section::Running),
            count_agents(Section::Idle),
            count_agents(Section::Inactive),
        );
        let mut extra_metadata = vec![(
            "agents".to_string(),
            format!("{running} running, {idle} idle, {inactive} inactive"),
        )];
        if let Some(root) = &self.scope_root {
            extra_metadata.push(("depth".to_string(), root.child_depth.to_string()));
        }
        let theme = &self.theme;
        let chrome = crate::chrome::ChromeState {
            version: self.options.version.clone(),
            cwd: self.options.cwd.to_string_lossy().to_string(),
            extra_metadata,
            splash_hide_cwd: self.scope_active,
            ..Default::default()
        };
        // `render_splash` already trails one blank row (TS renderContent's
        // `headerLines.push("")`), so the incident notice rides directly
        // under it (TS `renderContent`'s `headerLines.push("",
        // ...noticeLines)`): the warning line and its pointer stay above
        // the scope label and the search prompt.
        lines.extend(crate::chrome::render_splash(&chrome, theme, width));
        lines.extend(self.render_incident_notice(width));
        // The scoped view's back label (`< back - <title> > subagents`),
        // dim, over the full width under the splash.
        if self.scope_active {
            if let Some(scope) = &self.options.scope {
                let title = scope
                    .session_name
                    .clone()
                    .filter(|name| !name.trim().is_empty())
                    .unwrap_or_else(|| "Untitled agent".to_string());
                let label = truncate_text(
                    &format!(
                        "{} back{}{title} {} subagents",
                        glyphs::LEFT,
                        glyphs::SEP,
                        glyphs::RIGHT
                    ),
                    width,
                );
                let mut row = vec![crate::Span::styled(label, theme.fg_style(ThemeColor::Dim))];
                row = crate::width::pad_line(row, width);
                lines.push(row);
                lines.push(vec![]);
            }
        }

        // TS `renderPrompt`: the composer's header lines go above the box,
        // before the cursor row is taken; the box's own rows follow, and
        // the cursor rides inside them. The prompt's editor mutates its
        // own scroll state, so the theme borrow above ends here and the
        // frame re-borrows it for the list below.
        let (header, prompt_rows, box_cursor) = self.render_prompt(width);
        lines.extend(header);
        let prompt_start = lines.len();
        lines.extend(prompt_rows);
        let cursor = box_cursor.map(|(row, col)| (prompt_start + row, col));
        lines.push(vec![]);

        // The notice panel (a multi-line refusal from the previous run)
        // takes its rows between the list and the hint line, so the list
        // window shrinks while the full text stays visible. A budget that
        // cannot hold the borders and one content row (a degenerate pane)
        // falls back to the hint-line status with the notice's first line.
        let budget = height.saturating_sub(lines.len() + 1);
        // The panel is built and the notice's borrow ends here (render_list
        // below takes the mode mutably).
        let notice_panel = self
            .notice
            .as_deref()
            .filter(|_| budget >= 4)
            .map(|notice| self.render_notice(notice, width, budget));
        // Owned: the fallback's borrow of the notice must end before the
        // mutable list render below.
        let status_fallback: Option<String> = notice_panel
            .is_none()
            .then(|| {
                self.notice
                    .as_deref()
                    .and_then(|notice| notice.lines().next())
            })
            .flatten()
            .map(str::to_string);
        let notice_height = notice_panel.as_ref().map_or(0, Vec::len);
        let list_rows = height.saturating_sub(lines.len() + 1 + notice_height);
        lines.extend(self.render_list(width, list_rows));
        if let Some(panel) = notice_panel {
            lines.extend(panel);
        }
        lines.push(self.render_hints(width, status_fallback.as_deref()));
        lines.truncate(height);
        (lines, cursor)
    }

    /// The prompt block (TS `renderPrompt`, :2917-2926): the search
    /// composer renders the transparent editor shape (the muted `> `
    /// prefix, the dim "Search sessions" placeholder) over the plain
    /// surface; the rename composer renders the real editor box (TS
    /// `Editor.render` with the background) -- the warning header block
    /// inside it, the draft in the text color, the dim placeholder
    /// while empty. Returns the lines above the box, the box's rows,
    /// and the cursor's row within the box and its column.
    fn render_prompt(&mut self, width: usize) -> (Vec<Line>, Vec<Line>, Option<(usize, usize)>) {
        let theme = &self.theme;
        match &mut self.composer {
            Composer::Search => {
                let mut prompt: Line = vec![crate::Span::styled(
                    " >  ".to_string(),
                    theme.fg_style(ThemeColor::Muted),
                )];
                let head = truncate_text(&self.query, width.saturating_sub(5).max(1));
                prompt.push(crate::Span::styled(head, theme.fg_style(ThemeColor::Muted)));
                if self.query.is_empty() {
                    prompt.push(crate::Span::styled(
                        " ".to_string(),
                        theme.fg_style(ThemeColor::Muted),
                    ));
                    prompt.push(crate::Span::styled(
                        "Search sessions".to_string(),
                        theme.fg_style(ThemeColor::Dim),
                    ));
                }
                (
                    Vec::new(),
                    vec![prompt],
                    // The cursor caps at the same width the query
                    // displays (`truncate_text` keeps width - 5, the
                    // editor box's own cap): a longer query would
                    // otherwise park the caret past the last rendered
                    // cell, where the terminal frame skips it.
                    Some((0, 4 + str_width(&self.query).min(width.saturating_sub(5)))),
                )
            }
            // The reply composer's real editor box (the rename box's
            // shape): the target's header line rides INSIDE the box, the
            // placeholder names the action by the target's state, and
            // the cursor comes from the box. An open completion renders
            // its overlay panel above the box -- the chat's stacking (TS
            // draws the same dropdown through the editor's TUI overlay,
            // editor.ts `showOverlay`, anchored over the box).
            Composer::Reply(reply) => {
                let overlay = crate::view::editor_surface::overlay(&reply.editor, theme, width);
                let header = reply.header_line(theme);
                let placeholder = reply.placeholder();
                let surface = crate::view::editor_surface::render(
                    &mut reply.editor,
                    theme,
                    width,
                    u16::try_from(self.last_height).unwrap_or(u16::MAX),
                    Some(header),
                    Some(placeholder),
                );
                (overlay, surface.rows, surface.cursor)
            }
            // The rename composer's real editor box (TS `CustomEditor.render`
            // over `Editor.render`): the warning header rides INSIDE the box
            // (the header block under the top row, TS `getHeaderLine` via
            // `renderHeaderContentLine`), the draft renders through the
            // editor's own surface, and the cursor comes from the box --
            // the #3117 SF1 2-row shape closes.
            Composer::Rename(rename) => {
                let header =
                    vec![theme.fg(ThemeColor::Warning, "Rename agent session".to_string())];
                let surface = crate::view::editor_surface::render(
                    &mut rename.editor,
                    theme,
                    width,
                    u16::try_from(self.last_height).unwrap_or(u16::MAX),
                    Some(header),
                    Some("Name this agent session"),
                );
                (Vec::new(), surface.rows, surface.cursor)
            }
        }
    }

    /// The notice panel: the notice's own lines wrapped to the pane's
    /// inner width inside a bordered box, with the dismissal row last. The
    /// content fits the budget (the borders and the dismissal row are the
    /// fixed three); an overflow names the cap instead of silently
    /// cutting the refusal.
    pub(super) fn render_notice(&self, notice: &str, width: usize, budget: usize) -> Vec<Line> {
        let theme = &self.theme;
        let inner = width.saturating_sub(4).max(1);
        let mut content: Vec<Line> = Vec::new();
        for line in notice.split('\n') {
            if line.trim().is_empty() {
                content.push(vec![]);
                continue;
            }
            content.extend(crate::width::wrap_text(line, inner));
        }
        // The fixed rows: the borders and the dismissal row. The notice's
        // content fits what is left; an overflow names the cap (the marker
        // wraps with the same width, so a narrow pane never overflows the
        // border).
        let cap = budget.saturating_sub(3).max(1);
        if content.len() > cap {
            // One row of room carries the marker alone: a truncated
            // refusal never renders without the indication.
            if cap == 1 {
                content.clear();
            } else {
                content.truncate(cap - 1);
            }
            content.extend(crate::width::wrap_text(
                &format!(
                    "{} the notice continues {} a taller pane shows it whole",
                    glyphs::ELLIPSIS,
                    glyphs::DASH
                ),
                inner,
            ));
            content.truncate(cap);
        }
        content.push(vec![crate::Span::styled(
            "any key dismisses".to_string(),
            theme.fg_style(ThemeColor::Dim),
        )]);
        let border = || {
            let row = vec![
                crate::Span::styled(
                    glyphs::TABLE_CROSS.to_string(),
                    theme.fg_style(ThemeColor::Dim),
                ),
                crate::Span::styled(
                    glyphs::TABLE_H.repeat(width.saturating_sub(2)),
                    theme.fg_style(ThemeColor::Dim),
                ),
                crate::Span::styled(
                    glyphs::TABLE_CROSS.to_string(),
                    theme.fg_style(ThemeColor::Dim),
                ),
            ];
            crate::width::pad_line(row, width)
        };
        let mut panel = Vec::with_capacity(content.len() + 2);
        panel.push(border());
        for line in content {
            let mut row = vec![crate::Span::styled(
                format!("{} ", glyphs::TABLE_V),
                theme.fg_style(ThemeColor::Dim),
            )];
            row.extend(line);
            let used: usize = row.iter().map(|s| str_width(&s.content)).sum();
            row.push(crate::Span::raw(" ".repeat(width.saturating_sub(used + 2))));
            row.push(crate::Span::styled(
                format!(" {}", glyphs::TABLE_V),
                theme.fg_style(ThemeColor::Dim),
            ));
            panel.push(crate::width::pad_line(row, width));
        }
        panel.push(border());
        panel
    }

    /// The sectioned session list (TS `renderSessionRows`): the rows group
    /// into section blocks behind their headings, and the window follows
    /// the selection: the slice centers on the selected row and names the
    /// clipped overflow in `^ N more` / `v N more` rows, so a roster
    /// rebuild (spawn churn, activity re-sorts) never moves the user's
    /// position out of the window. Nested rows (summary rows and expanded
    /// subagents) render inside their top-level agent's section block,
    /// and the headings count top-level agents only (TS
    /// `getDisplayRowsForSection` / `countRowsBySection`).
    pub(super) fn render_list(&self, width: usize, max_rows: usize) -> Vec<Line> {
        /// One rendered display entry of the sectioned list (TS
        /// `DisplayItem`): the spacer between section blocks, a section
        /// heading, or one row.
        enum DisplayItem<'a> {
            Spacer,
            Heading(Section),
            Row(&'a AgentsViewRow),
        }
        if max_rows == 0 {
            return Vec::new();
        }
        if self.rows.is_empty() {
            let text = if self.query.trim().is_empty() {
                "No sessions yet."
            } else {
                "No sessions match your search."
            };
            return vec![vec![self.theme.fg(ThemeColor::Dim, text.to_string())]];
        }
        let layout = build_layout(&self.rows, width);
        // The display-item sequence (TS `displayItems`): each non-empty
        // section contributes a spacer (when not first), its heading, then
        // its rows.
        let counts: Vec<(Section, usize)> = [Section::Running, Section::Idle, Section::Inactive]
            .into_iter()
            .map(|section| {
                (
                    section,
                    self.rows
                        .iter()
                        .filter(|row| row.kind == RowKind::Agent && row.section == section)
                        .count(),
                )
            })
            .collect();
        let mut display: Vec<DisplayItem> = Vec::new();
        // While a query is active the list is a ranked picker: one flat,
        // relevance-ordered run of hits (per-row icons carry the status),
        // not status section blocks. Without a query the sectioned
        // layout stays TS-identical.
        if self.query.trim().is_empty() {
            for (section, count) in &counts {
                if *count == 0 {
                    continue;
                }
                if !display.is_empty() {
                    display.push(DisplayItem::Spacer);
                }
                display.push(DisplayItem::Heading(*section));
                let mut include = false;
                for row in &self.rows {
                    if row.depth == 0 {
                        include = row.kind == RowKind::Agent && row.section == *section;
                    }
                    if include {
                        display.push(DisplayItem::Row(row));
                    }
                }
            }
        } else {
            display.extend(self.rows.iter().map(DisplayItem::Row));
        }
        // The window (TS `renderSessionRows`): reserve the column header
        // and its spacer, center the slice on the selected row, and name
        // the clipped overflow in the more rows. The selected row's
        // display index drives the window, so a rebuild that re-sorts the
        // rows keeps the selection in view instead of snapping the
        // window back to the top of the list.
        let header_rows = max_rows.saturating_sub(1).min(2);
        let visible_rows = max_rows - header_rows;
        let selected_identity = self
            .rows
            .get(self.selected)
            .map(|row| row.identity.as_str());
        let selected_display_index = display
            .iter()
            .position(
                |item| matches!(item, DisplayItem::Row(row) if Some(row.identity.as_str()) == selected_identity),
            )
            .map_or(-1, |index| index as isize);
        let anchor = selected_display_index - (visible_rows / 2) as isize;
        let upper = display.len() as isize - visible_rows as isize;
        let start = anchor.min(upper).max(0) as usize;
        let show_leading = start > 0 && visible_rows > 1;
        let show_trailing = start + visible_rows < display.len() && visible_rows > 2;
        let content_rows = visible_rows - usize::from(show_leading) - usize::from(show_trailing);
        let slice_start = if selected_display_index >= start as isize + content_rows as isize {
            (selected_display_index + 1 - content_rows as isize) as usize
        } else {
            start
        };
        let slice_end = (slice_start + content_rows).min(display.len());
        let mut lines: Vec<Line> = Vec::with_capacity(max_rows);
        if header_rows > 0 {
            lines.push(vec![crate::Span::styled(
                layout.legend.clone(),
                self.theme
                    .fg_style(ThemeColor::Text)
                    .add_modifier(crate::style::Modifier::BOLD),
            )]);
        }
        if header_rows > 1 {
            lines.push(Vec::new());
        }
        let more = |mark: &str, count: usize| {
            vec![self
                .theme
                .fg(ThemeColor::Dim, format!("  {mark} {count} more"))]
        };
        if show_leading {
            lines.push(more(glyphs::UP, slice_start));
        }
        for item in &display[slice_start..slice_end] {
            match item {
                DisplayItem::Spacer => lines.push(Vec::new()),
                DisplayItem::Heading(section) => {
                    let count = counts
                        .iter()
                        .find(|(count_section, _)| count_section == section)
                        .map_or(0, |(_, count)| *count);
                    lines.push(vec![self.theme.fg(
                        ThemeColor::Muted,
                        truncate_text(&format!("{} ({count})", section_title(*section)), width),
                    )]);
                }
                DisplayItem::Row(row) => lines.push(self.render_row(row, &layout, width)),
            }
        }
        if show_trailing {
            lines.push(more(glyphs::DOWN, display.len() - slice_end));
        }
        lines
    }

    /// One session row (TS `renderRow`): the summary rows render their
    /// `+/- title` cell over the full width; agent rows render icon, title
    /// (nested rows indented), model, cost/age. The selected row
    /// carries the selection background.
    pub(super) fn render_row(&self, row: &AgentsViewRow, layout: &RowLayout, width: usize) -> Line {
        let theme = &self.theme;
        // TS `renderCodeRow`: a muted, truncated program line on the tool-panel
        // background; never selection-painted.
        if row.kind == RowKind::Code {
            let text = format!("{}  {}", "  ".repeat(row.depth), row.title);
            let line = pad_line(
                vec![theme.fg(ThemeColor::Muted, truncate_text(&text, width))],
                width,
            );
            return theme.bg_paint(crate::theme::ThemeBg::ToolPanelBg, line);
        }
        let selected = Some(row.identity.as_str())
            == self.rows.get(self.selected).map(|r| r.identity.as_str());
        if row.kind == RowKind::SubagentSummary {
            // TS: `formatTableCell(`${indent}${marker} ${title}`, width)`.
            let indent = "  ".repeat(row.depth);
            let marker = if row.expanded {
                glyphs::EXPANDED
            } else {
                glyphs::COLLAPSED
            };
            let text = format!("{indent}{marker} {}", row.title);
            // BOTH summary lines bill the descendant tree in the Cost
            // column (the operator's 2026-09-26 ask, then the follow-up:
            // an all-done tree renders no running line, so the inactive
            // line -- the row the operator actually sees then -- carries
            // the same aggregate; TS renders no cost on the summary
            // row): each title spans the Session + Model zone -- every
            // row yields its leading cells to the cost column -- and the
            // aggregate rides the same right-aligned `${:.2}` cell the
            // agent rows print, leaving the Age column blank behind it.
            if crate::agents_view_forest::is_summary_row_identity(&row.identity) {
                let zone = layout.name_width + 2 + layout.model_width;
                let title = crate::agents_view_state::truncate_text(&text, zone);
                let pad = zone.saturating_sub(str_width(&title));
                let line: Line = vec![
                    crate::Span::raw(title),
                    crate::Span::raw(" ".repeat(pad)),
                    crate::Span::styled("  ".to_string(), crate::style::Style::default()),
                    theme.fg(
                        ThemeColor::Dim,
                        layout
                            .details
                            .get(&row.identity)
                            .cloned()
                            .unwrap_or_default(),
                    ),
                ];
                // The summary rows always pad to the full width (their
                // original shape); the finish adds the selection band.
                let line = pad_line(line, width);
                return finish_session_row(theme, line, selected, width);
            }
            let line: Line = vec![crate::Span::raw(crate::agents_view_state::truncate_text(
                &text, width,
            ))];
            let line = pad_line(line, width);
            return finish_session_row(theme, line, selected, width);
        }
        let icon = match row.section {
            Section::Running => glyphs::WORKING[self.pulse % glyphs::WORKING.len()],
            Section::Idle | Section::Inactive => glyphs::BULLET,
        };
        let icon_color = match row.section {
            Section::Running => ThemeColor::Text,
            Section::Idle => ThemeColor::Warning,
            Section::Inactive => ThemeColor::Dim,
        };
        let icon_style = theme
            .fg_style(icon_color)
            .add_modifier(crate::style::Modifier::BOLD);
        // TS `renderRow`: `${"  ".repeat(depth)}${icon} ${title}` padded to
        // the name column, then the model cell, then the dim
        // cost/age details.
        let indent = "  ".repeat(row.depth);
        let indent_width = str_width(&indent);
        let mut line: Line = Vec::new();
        if indent_width > 0 {
            line.push(crate::Span::raw(indent));
        }
        line.push(crate::Span::styled(icon, icon_style));
        line.push(crate::Span::styled(
            " ".to_string(),
            crate::style::Style::default(),
        ));
        // Operator directive (2026-09-29, a sanctioned TS divergence): the
        // row carries its own session's heartbeat count in the dock's
        // vocabulary (TS renders a countdown and rolls descendants' jobs
        // into ancestors); here the count is per-session (the dock's
        // operator scoping), green while any job is active, amber when
        // all are paused.
        let session_id = row
            .summary
            .get("sessionId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        let active_session_id = row.summary.get("activeSessionId").and_then(Value::as_str);
        let jobs: Vec<&crate::heartbeats_picker::HeartbeatJob> = self
            .heartbeats
            .iter()
            .map(|entry| &entry.job)
            .filter(|job| job.in_session(active_session_id, session_id))
            .collect();
        // The badge rides only a name column with room for the row's
        // fixed prefix plus it: a too-narrow column would push the model
        // and cost/age cells right, so the row renders exactly as a
        // badge-less one instead.
        let badge = (!jobs.is_empty())
            .then(|| format!("{} {}", glyphs::HEARTBEAT, jobs.len()))
            .filter(|badge| layout.name_width > 2 + indent_width + str_width(badge));
        let badge_width = badge.as_deref().map_or(0, |badge| str_width(badge) + 1);
        if let Some(badge) = badge {
            let color = if jobs.iter().any(|job| job.is_active()) {
                ThemeColor::Success
            } else {
                ThemeColor::Warning
            };
            line.push(crate::Span::styled(badge, theme.fg_style(color)));
            line.push(crate::Span::styled(
                " ".to_string(),
                crate::style::Style::default(),
            ));
        }
        // TS `formatTableCell(title, nameWidth)`: the name cell (indent +
        // icon + badge + title) clips to the column width, so a long
        // session name can never push the model and cost/age columns
        // off-screen. The icon, its space, and the badge take the
        // leading cells.
        let title = truncate_text(
            &row.title,
            layout
                .name_width
                .saturating_sub(2 + indent_width + badge_width),
        );
        // Session titles render uniformly (no bold for named sessions);
        // explicit product decision -- differs from TS `styleRowTitle`, which
        // bolds explicit session names.
        let pad = layout
            .name_width
            .saturating_sub(str_width(&title) + 2 + indent_width + badge_width);
        line.push(crate::Span::styled(title, theme.fg_style(ThemeColor::Text)));
        line.push(crate::Span::raw(" ".repeat(pad)));
        line.push(crate::Span::styled(
            "  ".to_string(),
            crate::style::Style::default(),
        ));
        line.push(theme.fg(ThemeColor::Muted, cell(&row.model, layout.model_width)));
        line.push(crate::Span::styled(
            "  ".to_string(),
            crate::style::Style::default(),
        ));
        let details = layout
            .details
            .get(&row.identity)
            .cloned()
            .unwrap_or_default();
        line.push(theme.fg(ThemeColor::Dim, details));
        finish_session_row(theme, line, selected, width)
    }

    /// The bottom hint/status line. `status_override` carries the
    /// notice's first line when the degenerate pane skipped the panel.
    pub(super) fn render_hints(&self, width: usize, status_override: Option<&str>) -> Line {
        let theme = &self.theme;
        // Every slot's effective binding label (TS `keyText`), hoisted so
        // the mode branches and the bar slots share one definition.
        let first = |id: &str| {
            self.keybindings
                .first_key(id)
                .map(|key| crate::keybindings::format_key_text(&key))
        };
        if self.exit_armed {
            // TS `renderHints`: the exit hint renders the effective
            // `app.clear` key ("Press Ctrl+C again to exit"); a disabled
            // binding (an empty override) falls back to the plain hint.
            let hint = first("app.clear").map_or_else(
                || "Press again to exit".to_string(),
                |key| format!("Press {key} again to exit"),
            );
            return truncate_line(&vec![theme.fg(ThemeColor::Muted, hint)], width);
        }
        // The armed stop-or-delete confirm: "Press ctrl+x again to
        // stop|delete" (TS `renderHints`'s delete hint, keyed by the
        // armed row's CURRENT live work -- a row that settles between
        // the presses shows the word the confirm now carries).
        if let Some(pending) = &self.pending_delete {
            let stop = self
                .rows
                .iter()
                .find(|row| row.identity == pending.identity)
                .map_or(pending.stop, Self::delete_arm_word);
            let word = if stop { "stop" } else { "delete" };
            let hint = first("app.agents.delete").map_or_else(
                || format!("Press again to {word}"),
                |key| format!("Press {key} again to {word}"),
            );
            return truncate_line(&vec![theme.fg(ThemeColor::Muted, hint)], width);
        }
        // TS `renderHints`: the status renders in its own tone (a
        // failure reads error, a plain report muted). The truncation
        // keeps the style: the row is one span, clipped to the width
        // (`truncate_line` re-wraps plain text and would strip it -- the
        // tone is the row's whole point, the #3117 SF6 divergence).
        if let Some(status) = self.status.as_ref() {
            return vec![theme.fg(status.tone().color(), truncate_text(status.text(), width))];
        }
        // The notice fallback (the degenerate pane's first refusal
        // line) is the error family it always was.
        if let Some(status) = status_override {
            return vec![theme.fg(ThemeColor::Error, truncate_text(status, width))];
        }
        // The reply composer's hints (TS `renderReplyComposerHints`,
        // :2964-2978): the confirm key's word by the target's CURRENT
        // state (steer while it streams, send live, resume & send
        // saved), the queue hint while the draft has text, and cancel
        // over the cancel binding's every key.
        if let Composer::Reply(reply) = &self.composer {
            let current = self.current_reply_summary(&reply.target);
            let live = current
                .get("activeSessionId")
                .and_then(serde_json::Value::as_str)
                .is_some();
            let streaming = live
                && current
                    .get("isStreaming")
                    .and_then(serde_json::Value::as_bool)
                    == Some(true);
            let word = if streaming {
                "steer"
            } else if live {
                "send"
            } else {
                "resume & send"
            };
            let mut hints = vec![format!(
                "{} {word}",
                self.keybindings.key_text("tui.select.confirm")
            )];
            if !reply.editor.get_text().trim().is_empty() {
                hints.push(format!(
                    "{} queue",
                    self.keybindings.key_text("app.message.followUp")
                ));
            }
            hints.push(format!(
                "{} cancel",
                self.keybindings.key_text("tui.select.cancel")
            ));
            let hint = hints.join("   ");
            return truncate_line(&vec![theme.fg(ThemeColor::Muted, hint)], width);
        }
        // The rename composer's hint (TS :2942-2944): save/cancel over
        // the confirm/cancel bindings' every key (`keyText` -- TS shows
        // "Enter save   Esc/Ctrl+C cancel").
        if let Composer::Rename(_) = &self.composer {
            let hint = format!(
                "{} save   {} cancel",
                self.keybindings.key_text("tui.select.confirm"),
                self.keybindings.key_text("tui.select.cancel")
            );
            return truncate_line(&vec![theme.fg(ThemeColor::Muted, hint)], width);
        }
        // TS `renderHints`: every hint slot renders the effective binding
        // (`keyText`, arrows for up/down/left/right), so a user override
        // moves the hint with the handler. The summary row swaps the open
        // action for expand/collapse (TS `renderHints`'s `rightAction`);
        // the scoped view adds the parent-back hint.
        let right_action = match self.rows.get(self.selected) {
            Some(row) if row.kind == RowKind::SubagentSummary => {
                if row.expanded {
                    "collapse"
                } else {
                    "expand"
                }
            }
            _ => "open",
        };
        // The bar lists every effective action key of the view, so a
        // merged binding can never ship without its slot (the
        // operator's completeness directive). Every segment -- including
        // navigate, open, parent, and new -- renders its bindings' first
        // effective keys and drops entirely when its action is unbound
        // (the same contract as the jump and stop-or-delete slots; the
        // bar never advertises a default key the handler does not
        // take).
        // A two-key segment keeps whichever of the pair is bound.
        let pair = |a: &str, b: &str| match (first(a), first(b)) {
            (Some(a), Some(b)) => Some(format!("{a}/{b}")),
            (Some(only), None) | (None, Some(only)) => Some(only),
            (None, None) => None,
        };
        let mut segments = Vec::new();
        if let Some(keys) = pair("tui.select.up", "tui.select.down") {
            segments.push(format!("{keys} navigate"));
        }
        // The jump slot shows the first effective key of each edge
        // binding (the full key sets would overflow the one-line hint);
        // an override that empties either binding drops the slot.
        if let (Some(top), Some(bottom)) = (first("tui.select.top"), first("tui.select.bottom")) {
            segments.push(format!("{top}/{bottom} first/last"));
        }
        if let Some(keys) = pair("tui.select.confirm", "app.agents.open") {
            segments.push(format!("{keys} {right_action}"));
        }
        // The rename, stop-or-delete, program, and parent hints only show with an
        // empty search, and only when the selected row has a target for them.
        if self.query.is_empty() {
            // The multi-key slots render every configured key (dispatch
            // takes the whole set).
            let all =
                |id: &str| Some(self.keybindings.key_text(id)).filter(|keys| !keys.is_empty());
            if let Some(keys) = all("app.agents.rename").filter(|_| self.rename_target().is_some())
            {
                segments.push(format!("{keys} rename"));
            }
            // The reply slot (the operator's completeness directive: TS
            // shows none -- the space arm is undiscoverable without it):
            // only while the selected row is replyable.
            if let Some(keys) = all("app.agents.reply").filter(|_| self.reply_target().is_some()) {
                segments.push(format!("{keys} reply"));
            }
            if let Some(pending) = self.delete_arm_target() {
                if let Some(keys) = all("app.agents.delete") {
                    let word = if pending.stop { "stop" } else { "delete" };
                    segments.push(format!("{keys} {word}"));
                }
            }
            if self
                .program_target()
                .is_some_and(|summary| summary.has_spawn_code)
            {
                if let Some(keys) = all("app.agents.program") {
                    segments.push(format!("{keys} program"));
                }
            }
            if self.scope_active {
                if let Some(back) = first("app.agents.back") {
                    segments.push(format!("{back} parent"));
                }
            }
        }
        if let Some(new) = first("app.agents.new") {
            segments.push(format!("{new} new"));
        }
        let hints = segments.join("   ");
        truncate_line(&vec![theme.fg(ThemeColor::Muted, hints)], width)
    }
}

/// One session row's selection finish: the selected row pads to the
/// full width and carries the selection band; every other row renders
/// as built.
pub(super) fn finish_session_row(theme: &Theme, line: Line, selected: bool, width: usize) -> Line {
    if selected {
        return theme.selection_paint(pad_line(line, width));
    }
    line
}

pub(super) fn cell(value: &str, width: usize) -> String {
    let truncated = truncate_text(value, width);
    format!(
        "{truncated}{}",
        " ".repeat(width.saturating_sub(str_width(&truncated)))
    )
}

pub(super) fn truncate_line(line: &Line, width: usize) -> Line {
    let text = line.iter().map(|s| s.content.as_str()).collect::<String>();
    crate::width::wrap_text(&text, width.max(1))
        .into_iter()
        .next()
        .unwrap_or_default()
}

/// How the view leaves the terminal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Leave {
    /// The chat the view opened takes the terminal over: raw mode stays
    /// on (no echo in the gap), the cursor stays hidden.
    Handoff,
    /// The process is leaving: the one exit restore runs.
    Exit,
}

pub(super) enum Renderer {
    Terminal {
        term: InlineTerminal,
        /// The `showHardwareCursor` setting snapshot the surface mounted
        /// with: the caret is shown at the prompt only when this is set.
        show_hardware_cursor: bool,
    },
    Headless {
        width: u16,
        height: u16,
        frames: Vec<String>,
    },
}

impl Renderer {
    pub(super) fn setup(
        ui: AgentsViewUiMode,
        ui_tx: mpsc::UnboundedSender<UiInput>,
        exit_guard: crate::exit_guard::ExitGuard,
        surface_mounted: &std::sync::Arc<std::sync::atomic::AtomicBool>,
        show_hardware_cursor: bool,
    ) -> Result<Renderer> {
        match ui {
            AgentsViewUiMode::Terminal => {
                // The raw-mode bracket's `cfmakeraw` write clears IXON,
                // which is the kernel's one trigger for lifting a pending
                // Ctrl+S stop (see the flow e2e's launch route).
                crossterm::terminal::enable_raw_mode()?;
                // The terminal state changed: every later setup step is
                // fallible and an error from any of them still owns the
                // release. The flag arms here, not at the end of setup.
                surface_mounted.store(true, std::sync::atomic::Ordering::SeqCst);
                // The enhanced-key modes come up with the raw-mode
                // bracket: pastes arrive as one chunk, the kitty probe
                // runs before the reader thread starts polling.
                crate::enhanced_keys::enable(&mut std::io::stdout())?;
                // One reader thread feeds the view; the reader registry
                // joins the previous surface's reader (the chat it opened)
                // before this one starts polling. The reader also observes
                // Ctrl+C pairs for the exit guard: this thread stays alive
                // when the view loop is wedged in a daemon request, so the
                // force-quit contract holds regardless of loop state.
                // The paste-aware variant: a marker-less multi-line
                // keystroke burst coalesces into one paste (Enter submits
                // in the composers, so a burst typed line by line would
                // submit per line).
                crate::input::spawn_paste_aware_reader(move |input| match input {
                    crate::input::ReaderInput::BurstPaste(text) => {
                        ui_tx.send(UiInput::Paste(text)).is_ok()
                    }
                    crate::input::ReaderInput::Event(event) => match event {
                        crossterm::event::Event::Key(key) => {
                            exit_guard.observe_key(&key);
                            // Kitty Release events and unmappable keys map
                            // to no id; forwarding an empty id would clear
                            // the armed exit hint between the presses of
                            // a double Ctrl+C.
                            let Some(id) = crate::keys::key_event_to_id(&key) else {
                                return true;
                            };
                            ui_tx.send(UiInput::Key(id)).is_ok()
                        }
                        crossterm::event::Event::Paste(text) => {
                            ui_tx.send(UiInput::Paste(text)).is_ok()
                        }
                        crossterm::event::Event::Resize(..) => ui_tx.send(UiInput::Resize).is_ok(),
                        crossterm::event::Event::FocusGained
                        | crossterm::event::Event::FocusLost
                        | crossterm::event::Event::Mouse(_) => true,
                    },
                });
                // The live area starts at the cursor line the previous
                // surface's `clear_live` (or the shell) left at column 0.
                let (_, rows) = crossterm::terminal::size()?;
                Ok(Renderer::Terminal {
                    term: InlineTerminal::new(rows),
                    show_hardware_cursor,
                })
            }
            AgentsViewUiMode::Headless(plan) => {
                let steps = plan.steps;
                tokio::spawn(async move {
                    for step in steps {
                        match step {
                            AgentsStep::Type(text) => {
                                for ch in text.chars() {
                                    if ui_tx.send(UiInput::Key(ch.to_string())).is_err() {
                                        return;
                                    }
                                }
                            }
                            AgentsStep::Key(key) => {
                                if ui_tx.send(UiInput::Key(key)).is_err() {
                                    return;
                                }
                            }
                            AgentsStep::WaitSettle { timeout_ms } => {
                                let _ = ui_tx.send(UiInput::Settled);
                                tokio::time::sleep(Duration::from_millis(timeout_ms)).await;
                            }
                            AgentsStep::WaitRender { needle, timeout_ms } => {
                                if ui_tx
                                    .send(UiInput::WaitRender { needle, timeout_ms })
                                    .is_err()
                                {
                                    return;
                                }
                            }
                        }
                    }
                    let _ = ui_tx.send(UiInput::Done);
                });
                Ok(Renderer::Headless {
                    width: plan.width,
                    height: plan.height,
                    frames: Vec::new(),
                })
            }
        }
    }

    /// Paint one frame into the live area (terminal) or capture its text
    /// (headless).
    pub(super) fn draw(&mut self, mode: &mut AgentsViewMode) -> std::io::Result<()> {
        match self {
            Renderer::Terminal {
                term,
                show_hardware_cursor,
            } => {
                let (width, height) = crossterm::terminal::size()?;
                let (lines, cursor) = mode.render_frame(usize::from(width), usize::from(height));
                // The caret shows at the prompt only with
                // `showHardwareCursor` on; otherwise the cursor stays
                // hidden.
                let cursor = cursor
                    .filter(|_| *show_hardware_cursor)
                    .map(|(row, col)| LiveCursor { row, col });
                term.paint(
                    &mut std::io::stdout().lock(),
                    InlineFrame {
                        history: &[],
                        live: &lines,
                        cursor,
                    },
                )
            }
            Renderer::Headless {
                width,
                height,
                frames,
            } => {
                let (lines, _) = mode.render_frame(usize::from(*width), usize::from(*height));
                let text = frame_text(&lines);
                if frames.last().map(String::as_str) != Some(text.as_str()) {
                    frames.push(text);
                }
                Ok(())
            }
        }
    }

    /// The terminal resized: the live area re-fits the new height and is
    /// erased, so the next frame repaints it whole at the new width.
    pub(super) fn resize(&mut self) -> std::io::Result<()> {
        match self {
            Renderer::Terminal { term, .. } => {
                let (_, rows) = crossterm::terminal::size()?;
                term.set_height(rows);
                term.clear_live(&mut std::io::stdout().lock())
            }
            Renderer::Headless { .. } => Ok(()),
        }
    }

    /// The headless capture's frames (None on a terminal renderer): the
    /// headless plan's render barrier waits on these.
    pub(super) fn headless_frames(&self) -> Option<&[String]> {
        match self {
            Renderer::Headless { frames, .. } => Some(frames),
            Renderer::Terminal { .. } => None,
        }
    }

    /// Teardown. The view is transient: its live area is erased on
    /// every leave, so it leaves no output. A handoff keeps raw mode for
    /// the adopting surface (which starts its live area at the erased
    /// row); an exit runs the one exit restore.
    pub(super) fn finish(self, leave: Leave) -> std::io::Result<Vec<String>> {
        match self {
            Renderer::Terminal { mut term, .. } => {
                let cleared = term.clear_live(&mut std::io::stdout().lock());
                // The view's input reader stands down before the terminal
                // is handed on: the adopting session's mount joins this
                // reader through the registry, and a parked reader would
                // hold crossterm's global event-reader lock.
                crate::input::request_reader_stop();
                match leave {
                    Leave::Handoff => {
                        let _ = crate::enhanced_keys::disable(&mut std::io::stdout());
                    }
                    Leave::Exit => crate::exit_restore::restore_terminal(),
                }
                cleared.map(|()| Vec::new())
            }
            Renderer::Headless { frames, .. } => Ok(frames),
        }
    }
}

/// The plain text of one frame, rows joined by newlines.
pub(super) fn frame_text(lines: &[Line]) -> String {
    lines
        .iter()
        .map(|line| line.iter().map(|s| s.content.as_str()).collect::<String>())
        .collect::<Vec<_>>()
        .join("\n")
}
