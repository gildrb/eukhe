// The shell, in chatgpt.com's structure: the chats in a sidebar (a drawer
// below 1024px), then the top bar, the conversation and the composer in
// one 100dvh column; Settings over it as a route.

import * as Dialog from "@radix-ui/react-dialog";
import * as Tooltip from "@radix-ui/react-tooltip";
import * as stylex from "@stylexjs/stylex";
import { useEffect, useRef, useState } from "react";
import { newChat } from "../lib/actions.ts";
import { mediaQuery, useMedia } from "../lib/media.ts";
import { chatHref, navigate, useRoute } from "../lib/router.ts";
import { store, useStore } from "../lib/store.ts";
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
} from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { Composer, composerField } from "./Composer.tsx";
import { Conversation, stopTurn } from "./Conversation.tsx";
import { Settings } from "./Settings.tsx";
import { Sidebar } from "./Sidebar.tsx";
import { Topbar } from "./Topbar.tsx";

export function App() {
  const route = useRoute();
  const compact = useMedia(media.compact);
  const phone = useMedia(media.phone);
  const session = useStore((state) => state.session);
  const [drawer, setDrawer] = useState(false);
  const pushed = useRef(false);
  const panel = useRef<HTMLDivElement>(null);
  const activeId = route.sessionId ?? session?.id ?? null;

  // The drawer owns one history entry on phones and tablets, so Back closes it.
  const openDrawer = () => {
    history.pushState({ eukheDrawer: true }, "");
    pushed.current = true;
    setDrawer(true);
  };
  const closeDrawer = () => {
    setDrawer(false);
    if (pushed.current) {
      pushed.current = false;
      history.back();
    }
  };
  // Choosing a chat replaces the drawer's entry: Back then returns to the chat before.
  const choose = (href: string) => {
    if (drawer && pushed.current) {
      pushed.current = false;
      setDrawer(false);
      location.replace(href);
    } else {
      setDrawer(false);
      navigate(href);
    }
  };
  useEffect(() => {
    const onPop = () => {
      if (!pushed.current) return;
      pushed.current = false;
      setDrawer(false);
    };
    window.addEventListener("popstate", onPop);
    return () => window.removeEventListener("popstate", onPop);
  }, []);
  useEffect(() => {
    if (!compact && drawer) closeDrawer();
  }, [compact]);
  // gildrb's spring on the drawer itself (transform only).
  useEffect(() => {
    if (drawer && panel.current && matchMedia(mediaQuery(media.motion)).matches) {
      panel.current.animate(
        { transform: ["translateX(-100%)", "translateX(0)"] },
        { duration: motion.springMs, easing: motion.springEase },
      );
    }
  }, [drawer]);

  // Keys: ⌘/Ctrl+Shift+O new chat, ⌘/Ctrl+K search, Esc stops a running turn when the composer is empty or not focused.
  useEffect(() => {
    const onKey = (event: KeyboardEvent) => {
      const mod = event.metaKey || event.ctrlKey;
      const key = event.key.toLowerCase();
      if (mod && event.shiftKey && key === "o") {
        event.preventDefault();
        void newChat();
        return;
      }
      if (mod && !event.shiftKey && key === "k") {
        event.preventDefault();
        if (compact && !drawer) openDrawer();
        requestAnimationFrame(() => document.getElementById("chat-search")?.focus());
        return;
      }
      if (event.key === "Escape" && !event.defaultPrevented) {
        if (document.querySelector("[role=dialog], [role=menu], [role=alertdialog]")) return;
        const field = composerField.current;
        const typing = document.activeElement === field && Boolean(field?.value.trim());
        if (store.get().session?.turn.running && !typing) {
          event.preventDefault();
          stopTurn();
        }
      }
    };
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  });

  const sidebar = (inDrawer: boolean) => (
    <Sidebar
      drawer={inDrawer}
      activeId={activeId}
      onClose={closeDrawer}
      onChoose={choose}
      onSettings={() => {
        const href = chatHref(activeId, "");
        if (inDrawer) choose(href);
        else navigate(href);
      }}
    />
  );

  return (
    <Tooltip.Provider
      delayDuration={motion.tooltipDelay}
      skipDelayDuration={motion.tooltipSkipDelay}
    >
      <a href="#composer-input" {...stylex.props(styles.skip)}>
        Skip to the message field
      </a>
      <div {...stylex.props(styles.shell)}>
        {compact ? null : <div {...stylex.props(styles.column)}>{sidebar(false)}</div>}
        <main {...stylex.props(styles.main)}>
          <Topbar compact={compact} onOpenDrawer={openDrawer} />
          <Conversation routeId={route.sessionId} />
          <Composer />
        </main>
      </div>
      {compact ? (
        <Dialog.Root open={drawer} onOpenChange={(next) => (next ? openDrawer() : closeDrawer())}>
          <Dialog.Portal>
            <Dialog.Overlay {...stylex.props(styles.scrim)} />
            <Dialog.Content
              ref={panel}
              aria-describedby={undefined}
              // Esc in a search with text clears the search (Sidebar) and keeps the drawer open.
              onEscapeKeyDown={(event) => {
                const search = document.getElementById("chat-search");
                if (
                  search instanceof HTMLInputElement &&
                  document.activeElement === search &&
                  search.value
                ) {
                  event.preventDefault();
                }
              }}
              onOpenAutoFocus={(event) => {
                event.preventDefault();
                if (event.target instanceof HTMLElement) event.target.focus();
              }}
              {...stylex.props(styles.drawer)}
            >
              <Dialog.Title {...stylex.props(ui.srOnly)}>Chats</Dialog.Title>
              {sidebar(true)}
            </Dialog.Content>
          </Dialog.Portal>
        </Dialog.Root>
      ) : null}
      <Settings section={route.settings} sessionId={activeId} phone={phone} />
    </Tooltip.Provider>
  );
}

const fadeIn = stylex.keyframes({ from: { opacity: 0 }, to: { opacity: 1 } });

const styles = stylex.create({
  shell: { display: "flex", height: "100dvh", overflow: "hidden", backgroundColor: colors.bg },
  column: {
    flexShrink: 0,
    width: size.sidebar,
    height: "100%",
    borderInlineEndWidth: stroke.hairline,
    borderInlineEndStyle: "solid",
    borderInlineEndColor: colors.hairline,
  },
  main: {
    display: "flex",
    flexDirection: "column",
    flexGrow: 1,
    minWidth: 0,
    height: "100%",
    paddingTop: "env(safe-area-inset-top, 0px)",
    paddingLeft: "env(safe-area-inset-left, 0px)",
    paddingRight: "env(safe-area-inset-right, 0px)",
  },
  scrim: {
    position: "fixed",
    inset: 0,
    zIndex: layer.overlay,
    backgroundColor: colors.scrim,
    animationName: { default: null, [media.motion]: fadeIn },
    animationDuration: motion.fade,
  },
  drawer: {
    position: "fixed",
    top: 0,
    bottom: 0,
    left: 0,
    zIndex: layer.overlay,
    width: size.drawer,
    outline: "none",
    boxShadow: shadows.drawer,
    transitionTimingFunction: motion.spring,
  },
  skip: {
    position: "fixed",
    top: space.x2,
    left: space.x2,
    zIndex: layer.skip,
    paddingBlock: space.x2,
    paddingInline: space.x3,
    borderRadius: radius.control,
    backgroundColor: colors.primary,
    color: colors.bg,
    transform: { default: "translateY(-200%)", ":focus": "none" },
  },
});
