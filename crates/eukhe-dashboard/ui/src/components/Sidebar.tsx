// The list of chats: the wordmark, New chat, search, the chats grouped by
// their last activity, and Settings with the theme switch at the bottom.
// A persistent column on desktop; the drawer's content on phones and tablets.

import * as stylex from "@stylexjs/stylex";
import { Moon, Search, Settings, SquarePen, Sun, X } from "lucide-preact";
import { useMemo, useRef, useState } from "react";
import { newChat, setPref } from "../lib/actions.ts";
import { fmt } from "../lib/format.ts";
import { chatHref } from "../lib/router.ts";
import { useStore } from "../lib/store.ts";
import { derivePhase } from "../lib/turn.ts";
import type { SessionRow } from "../lib/types.ts";
import { colors, media, radius, size, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { IconButton, useMedia } from "./controls.tsx";

const DAY = 86_400_000;
export const NEW_CHAT_KEYS = /Mac|iPhone|iPad/.test(navigator.platform) ? "⌘⇧O" : "Ctrl+Shift+O";

/** Chats grouped as chatgpt.com does: Today, Yesterday, Previous 7 days, Previous 30 days, then months. */
function groupRows(rows: SessionRow[], now: number): { label: string; rows: SessionRow[] }[] {
  const startOfToday = new Date(now).setHours(0, 0, 0, 0);
  const groups = new Map<string, SessionRow[]>();
  const sorted = rows.toSorted(
    (a, b) => (Date.parse(b.modified) || 0) - (Date.parse(a.modified) || 0),
  );
  for (const row of sorted) {
    const at = Date.parse(row.modified) || 0;
    let label: string;
    if (at >= startOfToday) label = "Today";
    else if (at >= startOfToday - DAY) label = "Yesterday";
    else if (at >= startOfToday - 7 * DAY) label = "Previous 7 days";
    else if (at >= startOfToday - 30 * DAY) label = "Previous 30 days";
    else label = fmt.month(at);
    const group = groups.get(label);
    if (group) group.push(row);
    else groups.set(label, [row]);
  }
  return [...groups].map(([label, list]) => ({ label, rows: list }));
}

export function Sidebar({
  drawer,
  activeId,
  onClose,
  onChoose,
  onSettings,
}: {
  drawer: boolean;
  activeId: string | null;
  onClose: () => void;
  onChoose: (href: string) => void;
  onSettings: () => void;
}) {
  const sessions = useStore((state) => state.sessions);
  const link = useStore((state) => state.link.status);
  const everOpen = useStore((state) => state.link.everOpen);
  const theme = useStore((state) => state.prefs.theme);
  const session = useStore((state) => state.session);
  const approvals = useStore((state) => state.approvals);
  const [query, setQuery] = useState("");
  const search = useRef<HTMLInputElement>(null);

  const phase = derivePhase({ session, approvals }, Date.now(), fmt).phase;
  const statusWord =
    phase === "approval"
      ? "Needs you"
      : phase === "failed"
        ? "Failed"
        : session?.turn.running
          ? "Running"
          : "";

  const groups = useMemo(() => {
    const needle = query.trim().toLowerCase();
    const rows = needle
      ? sessions.rows.filter((row) => (row.title || "New chat").toLowerCase().includes(needle))
      : sessions.rows;
    return groupRows(rows, Date.now());
  }, [sessions.rows, query]);

  const systemDark = useMedia("(prefers-color-scheme: dark)");
  const dark = theme === "dark" || (theme === "system" && systemDark);

  let empty = "";
  if (!sessions.loaded && !everOpen && link !== "open" && link !== "connecting") {
    empty = "Chats appear when eukhe is reachable.";
  } else if (sessions.loaded && !sessions.rows.length) empty = "No chats yet.";
  else if (sessions.loaded && !groups.length) empty = "No chats match.";

  return (
    <nav aria-label="Chats" {...stylex.props(styles.sidebar)}>
      <div {...stylex.props(styles.head)}>
        <span translate={false} {...stylex.props(ui.title, styles.wordmark)}>
          eukhe
        </span>
        {drawer ? (
          <IconButton label="Close chats" onClick={onClose}>
            <X aria-hidden="true" {...stylex.props(ui.icon)} />
          </IconButton>
        ) : null}
      </div>
      <div {...stylex.props(styles.actions)}>
        <button
          type="button"
          onClick={() => void newChat(drawer ? onChoose : undefined)}
          {...stylex.props(ui.reset, ui.focusRing, styles.row)}
        >
          <SquarePen aria-hidden="true" {...stylex.props(ui.icon)} />
          <span {...stylex.props(styles.rowTitle)}>New chat</span>
          {drawer ? null : (
            <span {...stylex.props(ui.small, ui.tertiary, styles.keys)}>{NEW_CHAT_KEYS}</span>
          )}
        </button>
        <label {...stylex.props(styles.search)}>
          <Search aria-hidden="true" {...stylex.props(ui.iconSmall, ui.tertiary)} />
          <input
            ref={search}
            id="chat-search"
            type="search"
            placeholder="Search chats"
            aria-label="Search chats"
            autoComplete="off"
            value={query}
            onInput={(event) => setQuery(event.currentTarget.value)}
            onKeyDown={(event) => {
              if (event.key === "Escape" && query) {
                event.preventDefault();
                event.stopPropagation();
                setQuery("");
              }
            }}
            {...stylex.props(styles.searchInput)}
          />
        </label>
      </div>
      <div {...stylex.props(styles.list)}>
        {empty ? <p {...stylex.props(ui.small, ui.tertiary, styles.empty)}>{empty}</p> : null}
        {groups.map((group) => (
          <section key={group.label} aria-label={group.label} {...stylex.props(styles.group)}>
            <h2 {...stylex.props(ui.small, ui.tertiary, styles.groupLabel)}>{group.label}</h2>
            <ul {...stylex.props(styles.rows)}>
              {group.rows.map((row) => {
                const current = row.id === activeId;
                const href = chatHref(row.id);
                return (
                  <li key={row.id}>
                    <a
                      href={href}
                      aria-current={current ? "page" : undefined}
                      onClick={(event) => {
                        if (event.metaKey || event.ctrlKey || event.shiftKey || event.button !== 0)
                          return;
                        event.preventDefault();
                        onChoose(href);
                      }}
                      {...stylex.props(
                        ui.focusRing,
                        styles.row,
                        styles.chat,
                        current && styles.current,
                      )}
                    >
                      <span {...stylex.props(ui.ellipsis, styles.rowTitle)}>
                        {row.title || "New chat"}
                      </span>
                      {current && statusWord ? (
                        <span
                          {...stylex.props(
                            ui.small,
                            statusWord === "Needs you" ? styles.needsYou : ui.tertiary,
                          )}
                        >
                          {statusWord}
                        </span>
                      ) : null}
                    </a>
                  </li>
                );
              })}
            </ul>
          </section>
        ))}
      </div>
      <div {...stylex.props(styles.foot)}>
        <button
          type="button"
          onClick={onSettings}
          {...stylex.props(ui.reset, ui.focusRing, styles.row, styles.grow)}
        >
          <Settings aria-hidden="true" {...stylex.props(ui.icon)} />
          <span {...stylex.props(styles.rowTitle)}>Settings</span>
        </button>
        <IconButton
          label={dark ? "Use the light theme" : "Use the dark theme"}
          side="top"
          onClick={() => void setPref("theme", dark ? "light" : "dark")}
        >
          {dark ? (
            <Sun aria-hidden="true" {...stylex.props(ui.icon)} />
          ) : (
            <Moon aria-hidden="true" {...stylex.props(ui.icon)} />
          )}
        </IconButton>
      </div>
    </nav>
  );
}

const styles = stylex.create({
  sidebar: {
    display: "flex",
    flexDirection: "column",
    height: "100%",
    minHeight: 0,
    backgroundColor: colors.sidebar,
    paddingTop: "env(safe-area-inset-top, 0px)",
    paddingBottom: "env(safe-area-inset-bottom, 0px)",
    paddingLeft: "env(safe-area-inset-left, 0px)",
  },
  head: {
    display: "flex",
    alignItems: "center",
    justifyContent: "space-between",
    flexShrink: 0,
    height: size.topbar,
    paddingInlineStart: space.x5,
    paddingInlineEnd: space.x2,
  },
  wordmark: { color: colors.primary },
  actions: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x1,
    flexShrink: 0,
    paddingInline: space.x2,
    paddingBottom: space.x2,
  },
  row: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x3,
    width: "100%",
    minHeight: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    color: colors.primary,
    textDecoration: "none",
    backgroundColor: {
      default: "transparent",
      ":hover": { [media.hover]: colors.hover },
      ":active": colors.hover,
    },
    fontSize: type.text,
    lineHeight: type.textLine,
  },
  rowTitle: { flexGrow: 1, minWidth: 0 },
  keys: { flexShrink: 0 },
  grow: { flexGrow: 1, width: "auto" },
  search: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x2,
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    backgroundColor: colors.surface,
    cursor: "text",
    outline: { default: "none", ":focus-within": `1px solid ${colors.tertiary}` },
  },
  searchInput: {
    flexGrow: 1,
    minWidth: 0,
    height: "100%",
    padding: 0,
    borderWidth: 0,
    backgroundColor: "transparent",
    outline: "none",
    fontSize: { default: type.small, [media.touch]: type.text },
    color: colors.primary,
    "::placeholder": { color: colors.tertiary },
    "::-webkit-search-cancel-button": { display: "none" },
  },
  list: {
    flexGrow: 1,
    minHeight: 0,
    overflowY: "auto",
    overscrollBehavior: "contain",
    paddingInline: space.x2,
    paddingBottom: space.x4,
  },
  empty: { paddingInline: space.x3, paddingBlock: space.x2 },
  group: { paddingTop: space.x4 },
  groupLabel: { paddingInline: space.x3, paddingBottom: space.x1, fontWeight: 500 },
  rows: { listStyle: "none", margin: 0, padding: 0 },
  chat: { color: colors.primary },
  current: { backgroundColor: colors.hover, fontWeight: 500 },
  needsYou: { color: colors.primary, fontWeight: 500 },
  foot: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x1,
    flexShrink: 0,
    padding: space.x2,
    borderTopWidth: "1px",
    borderTopStyle: "solid",
    borderTopColor: colors.hairline,
  },
});
