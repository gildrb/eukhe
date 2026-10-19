// The composer: one box with the same footprint in every state (its only
// size change is its own text growing, in exact 24px lines from 1 to 8),
// attach / paste / drop images, the model button, Steer | Queue while a
// turn runs and the box has text, and the one action button (Send, muted
// Send, Stop). Sends are optimistic; drafts persist per chat.

import * as stylex from "@stylexjs/stylex";
import { ArrowUp, Plus, Square, X } from "lucide-preact";
import { useEffect, useLayoutEffect, useRef, useState } from "react";
import { admissionId, send, setPref, unqueue } from "../lib/actions.ts";
import { store, useStore } from "../lib/store.ts";
import type { Pending } from "../lib/turn.ts";
import { colors, media, radius, size, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { stopTurn } from "./Conversation.tsx";
import { IconButton, Segmented } from "./controls.tsx";
import { ModelMenu, ReasoningMenu } from "./ModelMenu.tsx";

const LINE = 24;
const MAX_LINES = 8;
const DRAFT_DEBOUNCE_MS = 300;
const nativeSizing = CSS.supports("field-sizing", "content");

type Image = Pending["images"][number];

let fill: ((text: string, images?: Image[]) => void) | null = null;

/** Put `text` (and images) in the composer and focus it: Edit on a queued or unsent message. */
export function fillComposer(text: string, images: Image[] = []): void {
  fill?.(text, images);
}

/** The composer's field, for Esc and the skip link. */
export const composerField: { current: HTMLTextAreaElement | null } = { current: null };

function readImage(file: File): Promise<Image> {
  const { promise, resolve, reject } = Promise.withResolvers<Image>();
  const reader = new FileReader();
  reader.addEventListener("load", () => {
    const url = typeof reader.result === "string" ? reader.result : "";
    resolve({
      data: url.slice(url.indexOf(",") + 1),
      mimeType: file.type,
      preview: URL.createObjectURL(file),
      name: file.name,
    });
  });
  reader.addEventListener("error", () =>
    reject(reader.error ?? new Error("The image could not be read.")),
  );
  reader.readAsDataURL(file);
  return promise;
}

export function Composer() {
  const session = useStore((state) => state.session);
  const lane = useStore((state) => state.prefs.lane);
  const enterSendsOnTouch = useStore((state) => state.prefs.enterSendsOnTouch);
  const [text, setText] = useState("");
  const [images, setImages] = useState<Image[]>([]);
  const [dragging, setDragging] = useState(false);
  const field = useRef<HTMLTextAreaElement>(null);
  const mirror = useRef<HTMLDivElement>(null);
  const files = useRef<HTMLInputElement>(null);
  const [lines, setLines] = useState(1);
  const sessionId = session?.id ?? null;
  const running = Boolean(session?.turn.running);
  const hasText = Boolean(text.trim()) || images.length > 0;
  const mode = running && !hasText ? "stop" : hasText ? "send" : "empty";
  const coarse = matchMedia("(pointer: coarse)").matches;

  // Drafts persist per chat.
  useEffect(() => {
    if (!sessionId) return;
    let draft = "";
    try {
      draft = localStorage.getItem(`eukhe.draft.${sessionId}`) ?? "";
    } catch {
      draft = "";
    }
    setText(draft);
  }, [sessionId]);
  useEffect(() => {
    if (!sessionId) return undefined;
    const timer = setTimeout(() => {
      try {
        if (text) localStorage.setItem(`eukhe.draft.${sessionId}`, text);
        else localStorage.removeItem(`eukhe.draft.${sessionId}`);
      } catch {
        // Storage full or blocked: the draft lives in the field.
      }
    }, DRAFT_DEBOUNCE_MS);
    return () => clearTimeout(timer);
  }, [text, sessionId]);

  // Without `field-sizing`, a hidden twin of the field (same width, same font) counts the lines.
  useLayoutEffect(() => {
    if (nativeSizing || !mirror.current || !field.current) return;
    mirror.current.style.width = `${field.current.clientWidth}px`;
    mirror.current.textContent = `${text}\u200b`;
    setLines(Math.min(MAX_LINES, Math.max(1, Math.round(mirror.current.offsetHeight / LINE))));
  }, [text]);

  useEffect(() => {
    composerField.current = field.current;
    fill = (next, nextImages = []) => {
      setText(next);
      setImages(nextImages);
      requestAnimationFrame(() => {
        const input = field.current;
        if (!input) return;
        input.focus();
        input.setSelectionRange(next.length, next.length);
      });
    };
    return () => {
      fill = null;
    };
  }, []);

  const addFiles = async (list: FileList | File[]) => {
    const picked = [...list].filter((file) => file.type.startsWith("image/"));
    if (!picked.length) return;
    try {
      const read = await Promise.all(picked.map(readImage));
      setImages((current) => [...current, ...read]);
    } catch {
      store.set({ notice: "That image could not be read." });
    }
  };

  const submit = () => {
    if (!session || (!text.trim() && !images.length)) return;
    void send({
      admissionId: admissionId(),
      text,
      images,
      mode: running ? lane : "followUp",
      queued: running,
    });
    setText("");
    setImages([]);
  };

  return (
    <div {...stylex.props(styles.wrap)}>
      <form
        aria-label="Message"
        // The whole box is the field's hit area: a tap on its padding or its empty row focuses it.
        onPointerDown={(event) => {
          const target = event.target;
          if (target instanceof Element && !target.closest("button, a, input, textarea")) {
            event.preventDefault();
            field.current?.focus();
          }
        }}
        onSubmit={(event) => {
          event.preventDefault();
          submit();
        }}
        onDragOver={(event) => {
          if (
            event.dataTransfer &&
            [...event.dataTransfer.items].some((item) => item.type.startsWith("image/"))
          ) {
            event.preventDefault();
            setDragging(true);
          }
        }}
        onDragLeave={() => setDragging(false)}
        onDrop={(event) => {
          setDragging(false);
          if (!event.dataTransfer?.files.length) return;
          event.preventDefault();
          void addFiles(event.dataTransfer.files);
        }}
        {...stylex.props(styles.box, dragging && styles.dragging)}
      >
        {images.length ? (
          <div {...stylex.props(styles.images)}>
            {images.map((image, index) => (
              <div key={image.preview} {...stylex.props(styles.image)}>
                <img
                  src={image.preview}
                  alt={image.name || "Attached image"}
                  {...stylex.props(styles.thumb)}
                />
                <IconButton
                  label="Remove image"
                  onClick={() => {
                    URL.revokeObjectURL(image.preview);
                    setImages((current) => current.filter((_, at) => at !== index));
                  }}
                >
                  <X aria-hidden="true" {...stylex.props(ui.iconSmall)} />
                </IconButton>
              </div>
            ))}
          </div>
        ) : null}
        <div {...stylex.props(styles.fieldWrap)}>
          <textarea
            ref={field}
            id="composer-input"
            name="message"
            rows={1}
            autoComplete="off"
            autoCapitalize="sentences"
            spellcheck
            placeholder="Message eukhe"
            aria-label="Message eukhe"
            enterkeyhint={coarse && !enterSendsOnTouch ? "enter" : "send"}
            value={text}
            onInput={(event) => setText(event.currentTarget.value)}
            onKeyDown={(event) => {
              if (event.isComposing || event.keyCode === 229) return;
              if (event.key === "Enter") {
                const mod = event.metaKey || event.ctrlKey;
                if (event.shiftKey && !mod) return;
                if (mod || !coarse || enterSendsOnTouch) {
                  event.preventDefault();
                  submit();
                }
                return;
              }
              if (
                event.key === "ArrowUp" &&
                !text &&
                !event.altKey &&
                !event.metaKey &&
                !event.ctrlKey
              ) {
                // ↑ in an empty composer edits the last queued message.
                const queue = store.get().session?.queue;
                const lastFollowUp = queue?.followUps.at(-1);
                const lastSteer = queue?.steering.at(-1);
                const taken = lastFollowUp
                  ? unqueue("followUp", (queue?.followUps.length ?? 1) - 1, lastFollowUp.text)
                  : lastSteer
                    ? unqueue("steering", (queue?.steering.length ?? 1) - 1, lastSteer.text)
                    : null;
                if (taken) {
                  event.preventDefault();
                  taken.then(
                    (queued) => setText(queued),
                    (error: Error) => store.set({ notice: `Not editable. ${error.message}` }),
                  );
                }
              }
            }}
            onPaste={(event) => {
              const pasted = event.clipboardData ? [...event.clipboardData.files] : [];
              if (pasted.some((file) => file.type.startsWith("image/"))) {
                event.preventDefault();
                void addFiles(pasted);
              }
            }}
            {...stylex.props(styles.field, nativeSizing ? styles.native : null)}
            style={nativeSizing ? undefined : { height: `${lines * LINE}px` }}
          />
          {nativeSizing ? null : (
            <div ref={mirror} aria-hidden="true" {...stylex.props(styles.mirror)} />
          )}
        </div>
        <div {...stylex.props(styles.row)}>
          <IconButton label="Attach images" side="top" onClick={() => files.current?.click()}>
            <Plus aria-hidden="true" {...stylex.props(ui.icon)} />
          </IconButton>
          <ModelMenu />
          <ReasoningMenu />
          <div {...stylex.props(styles.end)}>
            {running && hasText ? (
              <Segmented
                compact
                label="When to send"
                options={[
                  { value: "steer", label: "Steer" },
                  { value: "followUp", label: "Queue" },
                ]}
                value={lane}
                onChange={(value) => void setPref("lane", value === "steer" ? "steer" : "followUp")}
              />
            ) : null}
            <IconButton
              label={mode === "stop" ? "Stop" : "Send"}
              keys={mode === "stop" ? "Esc" : coarse ? undefined : "Enter"}
              side="top"
              aria-disabled={mode === "empty"}
              onClick={() => {
                if (mode === "stop") stopTurn();
                else if (mode === "send") submit();
                else field.current?.focus();
              }}
              xstyle={[styles.action, mode === "empty" && styles.actionMuted]}
            >
              {mode === "stop" ? (
                <Square aria-hidden="true" fill="currentColor" {...stylex.props(ui.iconSmall)} />
              ) : (
                <ArrowUp aria-hidden="true" strokeWidth={2.25} {...stylex.props(ui.icon)} />
              )}
            </IconButton>
          </div>
        </div>
        <input
          ref={files}
          type="file"
          accept="image/*"
          multiple
          tabIndex={-1}
          aria-hidden="true"
          onChange={(event) => {
            const input = event.currentTarget;
            if (input.files) void addFiles(input.files);
            input.value = "";
          }}
          {...stylex.props(ui.srOnly)}
        />
      </form>
    </div>
  );
}

const styles = stylex.create({
  wrap: {
    flexShrink: 0,
    width: "100%",
    maxWidth: size.column,
    marginInline: "auto",
    paddingInline: { default: space.x6, [media.phone]: space.x3 },
    paddingBottom: {
      default: space.x4,
      [media.phone]: `calc(${space.x3} + env(safe-area-inset-bottom, 0px))`,
    },
  },
  box: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x2,
    paddingTop: space.x3,
    paddingInline: space.x4,
    paddingBottom: space.x2,
    borderRadius: radius.composer,
    backgroundColor: colors.surface,
    boxShadow: `inset 0 0 0 1px ${colors.hairline}`,
  },
  dragging: { boxShadow: `inset 0 0 0 1px ${colors.tertiary}` },
  images: { display: "flex", flexWrap: "wrap", gap: space.x2 },
  image: { position: "relative", display: "flex", alignItems: "flex-start", columnGap: space.x1 },
  thumb: {
    display: "block",
    width: "56px",
    height: "56px",
    objectFit: "cover",
    borderRadius: radius.control,
  },
  fieldWrap: { position: "relative" },
  field: {
    display: "block",
    width: "100%",
    minHeight: `${LINE}px`,
    maxHeight: `${LINE * MAX_LINES}px`,
    margin: 0,
    padding: 0,
    borderWidth: 0,
    backgroundColor: "transparent",
    color: colors.primary,
    fontSize: type.text,
    lineHeight: `${LINE}px`,
    resize: "none",
    outline: "none",
    overflowY: "auto",
    "::placeholder": { color: colors.tertiary },
  },
  native: { fieldSizing: "content" },
  mirror: {
    position: "absolute",
    top: 0,
    left: 0,
    visibility: "hidden",
    pointerEvents: "none",
    whiteSpace: "pre-wrap",
    overflowWrap: "break-word",
    fontSize: type.text,
    lineHeight: `${LINE}px`,
  },
  row: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x1,
    height: { default: size.row, [media.touch]: size.touch },
    marginInline: `calc(-1 * ${space.x2})`,
  },
  end: { display: "flex", alignItems: "center", columnGap: space.x2, marginInlineStart: "auto" },
  action: {
    borderRadius: radius.menu,
    backgroundColor: { default: colors.primary, ":hover": { [media.hover]: colors.secondary } },
    color: { default: colors.bg, ":hover": { [media.hover]: colors.bg } },
  },
  actionMuted: {
    backgroundColor: { default: colors.hover, ":hover": { [media.hover]: colors.hover } },
    color: { default: colors.tertiary, ":hover": { [media.hover]: colors.tertiary } },
    cursor: "default",
  },
});
