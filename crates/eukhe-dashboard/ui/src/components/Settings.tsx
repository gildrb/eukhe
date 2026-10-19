// Settings: a dialog with its sections as vertical tabs (desktop and
// tablet), a full-screen view with a list of sections, each opening its
// own view (phone). Deep-linked: #/c/<id>/settings/<section>; Back works.

import * as Dialog from "@radix-ui/react-dialog";
import * as Tabs from "@radix-ui/react-tabs";
import * as stylex from "@stylexjs/stylex";
import { ArrowLeft, ChevronRight, X } from "lucide-preact";
import type { ComponentType } from "preact";
import { chatHref, navigate } from "../lib/router.ts";
import {
  colors,
  layer,
  media,
  motion,
  radius,
  shadows,
  size,
  space,
  stroke,
  type,
  weight,
} from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { IconButton } from "./controls.tsx";
import {
  About,
  Advanced,
  Behavior,
  General,
  MemorySection,
  ModelSection,
  Usage,
} from "./sections.tsx";

const SECTIONS: { id: string; title: string; Body: ComponentType }[] = [
  { id: "general", title: "General", Body: General },
  { id: "model", title: "Model", Body: ModelSection },
  { id: "behavior", title: "Behavior", Body: Behavior },
  { id: "memory", title: "Memory", Body: MemorySection },
  { id: "usage", title: "Usage", Body: Usage },
  { id: "advanced", title: "Advanced", Body: Advanced },
  { id: "about", title: "About", Body: About },
];

export function Settings({
  section,
  sessionId,
  phone,
}: {
  section: string | null;
  sessionId: string | null;
  phone: boolean;
}) {
  const open = section !== null;
  const close = () => navigate(chatHref(sessionId));
  const known = SECTIONS.find((entry) => entry.id === section);
  // The phone shows the list first; larger screens open on General.
  const current = known ?? (phone ? null : SECTIONS[0]);

  return (
    <Dialog.Root open={open} onOpenChange={(next) => (next ? undefined : close())}>
      <Dialog.Portal>
        {phone ? null : <Dialog.Overlay {...stylex.props(styles.overlay)} />}
        <Dialog.Content
          aria-describedby={undefined}
          // The panel itself takes focus: a focused close button would show its ring and tooltip.
          onOpenAutoFocus={(event) => {
            event.preventDefault();
            if (event.target instanceof HTMLElement) event.target.focus();
          }}
          {...stylex.props(phone ? styles.sheet : styles.dialog)}
        >
          {phone ? (
            <>
              <header {...stylex.props(styles.head)}>
                {current ? (
                  <IconButton
                    label="Back to Settings"
                    onClick={() => navigate(chatHref(sessionId, ""), true)}
                  >
                    <ArrowLeft aria-hidden="true" {...stylex.props(ui.icon)} />
                  </IconButton>
                ) : null}
                <Dialog.Title {...stylex.props(ui.title, styles.title)}>
                  {current ? current.title : "Settings"}
                </Dialog.Title>
                <Dialog.Close asChild>
                  <IconButton label="Close Settings">
                    <X aria-hidden="true" {...stylex.props(ui.icon)} />
                  </IconButton>
                </Dialog.Close>
              </header>
              <div {...stylex.props(styles.body)}>
                {current ? (
                  <current.Body />
                ) : (
                  <ul {...stylex.props(styles.list)}>
                    {SECTIONS.map((entry) => (
                      <li key={entry.id}>
                        <a
                          href={chatHref(sessionId, entry.id)}
                          {...stylex.props(ui.focusRing, styles.listRow)}
                        >
                          <span>{entry.title}</span>
                          <ChevronRight
                            aria-hidden="true"
                            {...stylex.props(ui.icon, ui.tertiary)}
                          />
                        </a>
                      </li>
                    ))}
                  </ul>
                )}
              </div>
            </>
          ) : (
            <Tabs.Root
              orientation="vertical"
              value={current?.id ?? "general"}
              onValueChange={(next) => navigate(chatHref(sessionId, next), true)}
              {...stylex.props(styles.tabs)}
            >
              <div {...stylex.props(styles.rail)}>
                <Dialog.Title {...stylex.props(ui.title, styles.railTitle)}>Settings</Dialog.Title>
                <Tabs.List aria-label="Sections" {...stylex.props(styles.tabList)}>
                  {SECTIONS.map((entry) => (
                    <Tabs.Trigger
                      key={entry.id}
                      value={entry.id}
                      {...stylex.props(
                        ui.reset,
                        ui.focusRing,
                        styles.tab,
                        current?.id === entry.id && styles.tabOn,
                      )}
                    >
                      {entry.title}
                    </Tabs.Trigger>
                  ))}
                </Tabs.List>
              </div>
              <div {...stylex.props(styles.pane)}>
                <header {...stylex.props(styles.paneHead)}>
                  <h2 {...stylex.props(ui.title)}>{current?.title}</h2>
                  <Dialog.Close asChild>
                    <IconButton label="Close Settings">
                      <X aria-hidden="true" {...stylex.props(ui.icon)} />
                    </IconButton>
                  </Dialog.Close>
                </header>
                {SECTIONS.map((entry) => (
                  <Tabs.Content key={entry.id} value={entry.id} {...stylex.props(styles.body)}>
                    <entry.Body />
                  </Tabs.Content>
                ))}
              </div>
            </Tabs.Root>
          )}
        </Dialog.Content>
      </Dialog.Portal>
    </Dialog.Root>
  );
}

const fadeIn = stylex.keyframes({ from: { opacity: 0 }, to: { opacity: 1 } });
const rise = stylex.keyframes({
  from: { opacity: 0, transform: "translate(-50%, -48%) scale(0.98)" },
  to: { opacity: 1, transform: "translate(-50%, -50%) scale(1)" },
});
const slideIn = stylex.keyframes({
  from: { transform: `translateX(${space.x6})`, opacity: 0 },
  to: { transform: "none", opacity: 1 },
});

const styles = stylex.create({
  overlay: {
    position: "fixed",
    inset: 0,
    zIndex: layer.overlay,
    backgroundColor: colors.scrim,
    animationName: { default: null, [media.motion]: fadeIn },
    animationDuration: motion.fast,
  },
  dialog: {
    position: "fixed",
    top: "50%",
    left: "50%",
    zIndex: layer.overlay,
    display: "flex",
    width: size.dialog,
    height: size.dialogHeight,
    borderRadius: radius.bubble,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: colors.raised,
    boxShadow: shadows.raised,
    color: colors.primary,
    transform: "translate(-50%, -50%)",
    overflow: "hidden",
    outline: "none",
    animationName: { default: null, [media.motion]: rise },
    animationDuration: motion.rise,
    animationTimingFunction: motion.emphasized,
  },
  sheet: {
    position: "fixed",
    inset: 0,
    zIndex: layer.overlay,
    display: "flex",
    flexDirection: "column",
    paddingTop: "env(safe-area-inset-top, 0px)",
    paddingBottom: "env(safe-area-inset-bottom, 0px)",
    backgroundColor: colors.bg,
    color: colors.primary,
    outline: "none",
    animationName: { default: null, [media.motion]: slideIn },
    animationDuration: motion.fade,
    animationTimingFunction: motion.emphasized,
  },
  head: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x1,
    flexShrink: 0,
    height: size.topbar,
    paddingInline: space.x1,
  },
  title: { flexGrow: 1, minWidth: 0, margin: 0, paddingInlineStart: space.x3 },
  body: {
    flexGrow: 1,
    minHeight: 0,
    overflowY: "auto",
    overscrollBehavior: "contain",
    paddingInline: { default: space.x6, [media.phone]: space.x4 },
    paddingBottom: space.x8,
    outline: "none",
  },
  list: { listStyle: "none", margin: 0, padding: 0 },
  listRow: {
    display: "flex",
    alignItems: "center",
    justifyContent: "space-between",
    minHeight: size.listRow,
    borderBottomWidth: stroke.hairline,
    borderBottomStyle: "solid",
    borderBottomColor: colors.hairline,
    color: colors.primary,
    textDecoration: "none",
    fontSize: type.text,
  },
  tabs: { display: "flex", width: "100%", minHeight: 0 },
  rail: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x2,
    flexShrink: 0,
    width: size.rail,
    padding: space.x3,
    backgroundColor: colors.sidebar,
    borderInlineEndWidth: stroke.hairline,
    borderInlineEndStyle: "solid",
    borderInlineEndColor: colors.hairline,
  },
  railTitle: { margin: 0, paddingInline: space.x3, paddingBlock: space.x2 },
  tabList: { display: "flex", flexDirection: "column", rowGap: space.x05 },
  tab: {
    display: "flex",
    alignItems: "center",
    height: size.row,
    paddingInline: space.x3,
    borderRadius: radius.control,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  tabOn: { backgroundColor: colors.hover, color: colors.primary, fontWeight: weight.medium },
  pane: { display: "flex", flexDirection: "column", flexGrow: 1, minWidth: 0, minHeight: 0 },
  paneHead: {
    display: "flex",
    alignItems: "center",
    justifyContent: "space-between",
    flexShrink: 0,
    height: size.topbar,
    paddingInlineStart: space.x6,
    paddingInlineEnd: space.x2,
  },
});
