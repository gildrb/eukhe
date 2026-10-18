// The bar over the conversation: the drawer button and New chat on
// phones and tablets, the chat's title opening the chat menu, and the
// link state while it is not connected (a fixed slot: the bar never
// changes height).

import * as AlertDialog from "@radix-ui/react-alert-dialog";
import * as Dialog from "@radix-ui/react-dialog";
import * as Menu from "@radix-ui/react-dropdown-menu";
import * as stylex from "@stylexjs/stylex";
import {
  ChevronDown,
  Download,
  FileText,
  GitFork,
  Menu as MenuIcon,
  Pencil,
  Shrink,
  SquarePen,
  Trash,
} from "lucide-preact";
import { useState } from "react";
import {
  compactChat,
  deleteChat,
  exportChat,
  forkChat,
  newChat,
  renameChat,
} from "../lib/actions.ts";
import { reconnect } from "../lib/link.ts";
import { useStore } from "../lib/store.ts";
import { colors, media, radius, size, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { Button, IconButton, Status, TextButton, TextField } from "./controls.tsx";
import { dialog } from "./dialog.ts";
import { NEW_CHAT_KEYS } from "./Sidebar.tsx";

export function Topbar({ compact, onOpenDrawer }: { compact: boolean; onOpenDrawer: () => void }) {
  const link = useStore((state) => state.link.status);
  const everOpen = useStore((state) => state.link.everOpen);
  return (
    <header {...stylex.props(styles.bar)}>
      {compact ? (
        <IconButton label="Open chats" onClick={onOpenDrawer}>
          <MenuIcon aria-hidden="true" {...stylex.props(ui.icon)} />
        </IconButton>
      ) : null}
      <ChatMenu />
      <div {...stylex.props(styles.end)}>
        {link === "open" ? null : (
          <span role="status" {...stylex.props(styles.offline)}>
            {link === "unavailable" ? (
              <span {...stylex.props(ui.small, ui.tertiary)}>eukhe is not running</span>
            ) : (
              <span {...stylex.props(ui.small, ui.shimmer)}>
                {everOpen ? "Reconnecting" : "Connecting"}
              </span>
            )}
            <TextButton strong onClick={reconnect}>
              Retry
            </TextButton>
          </span>
        )}
        {compact ? (
          <IconButton label="New chat" keys={NEW_CHAT_KEYS} onClick={() => void newChat()}>
            <SquarePen aria-hidden="true" {...stylex.props(ui.icon)} />
          </IconButton>
        ) : null}
      </div>
    </header>
  );
}

type Busy = { text: string; error: boolean } | null;

/** The chat's title as a button, opening Rename, Fork, Export, Compact and Delete. */
function ChatMenu() {
  const session = useStore((state) => state.session);
  const [open, setOpen] = useState(false);
  const [status, setStatus] = useState<Busy>(null);
  const [renaming, setRenaming] = useState(false);
  const [deleting, setDeleting] = useState(false);
  const title = session?.title ?? "eukhe";

  // An item runs its action with the menu still open and reports the result in it.
  const act =
    (action: () => Promise<string>, doing: string, closeAfter = false) =>
    (event: Event) => {
      event.preventDefault();
      setStatus({ text: doing, error: false });
      action().then(
        (text) => {
          setStatus({ text, error: false });
          if (closeAfter) setOpen(false);
        },
        (error: Error) => setStatus({ text: error.message, error: true }),
      );
    };

  return (
    <>
      <Menu.Root
        open={open}
        onOpenChange={(next) => {
          setOpen(next);
          if (next) setStatus(null);
        }}
      >
        <Menu.Trigger asChild disabled={!session}>
          <button
            type="button"
            {...stylex.props(ui.reset, ui.focusRing, styles.title, open && styles.titleOpen)}
          >
            <span {...stylex.props(ui.ellipsis)}>{title}</span>
            <ChevronDown aria-hidden="true" {...stylex.props(ui.iconSmall, ui.tertiary)} />
          </button>
        </Menu.Trigger>
        <Menu.Portal>
          <Menu.Content
            align="start"
            sideOffset={4}
            collisionPadding={8}
            loop
            {...stylex.props(ui.menu, styles.menu)}
          >
            <Menu.Item onSelect={() => setRenaming(true)} {...stylex.props(ui.menuItem)}>
              <Pencil aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Rename
            </Menu.Item>
            <Menu.Item onSelect={act(forkChat, "Forking", true)} {...stylex.props(ui.menuItem)}>
              <GitFork aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Fork
            </Menu.Item>
            <Menu.Item
              onSelect={act(() => exportChat("html"), "Exporting")}
              {...stylex.props(ui.menuItem)}
            >
              <Download aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Export as HTML
            </Menu.Item>
            <Menu.Item
              onSelect={act(() => exportChat("jsonl"), "Exporting")}
              {...stylex.props(ui.menuItem)}
            >
              <FileText aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Export as JSONL
            </Menu.Item>
            <Menu.Item
              onSelect={act(() => compactChat(), "Compacting")}
              {...stylex.props(ui.menuItem)}
            >
              <Shrink aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Compact context
            </Menu.Item>
            <Menu.Separator {...stylex.props(ui.menuSeparator)} />
            <Menu.Item
              onSelect={() => setDeleting(true)}
              {...stylex.props(ui.menuItem, ui.menuDanger)}
            >
              <Trash aria-hidden="true" {...stylex.props(ui.iconSmall)} />
              Delete
            </Menu.Item>
            {status ? (
              <p role="status" {...stylex.props(ui.menuStatus, status.error && ui.menuDanger)}>
                {status.text}
              </p>
            ) : null}
          </Menu.Content>
        </Menu.Portal>
      </Menu.Root>
      {session ? (
        <RenameDialog
          open={renaming}
          onOpenChange={setRenaming}
          id={session.id}
          title={session.title}
        />
      ) : null}
      {session ? (
        <DeleteDialog
          open={deleting}
          onOpenChange={setDeleting}
          id={session.id}
          title={session.title}
        />
      ) : null}
    </>
  );
}

function RenameDialog({
  open,
  onOpenChange,
  id,
  title,
}: {
  open: boolean;
  onOpenChange: (open: boolean) => void;
  id: string;
  title: string;
}) {
  const [name, setName] = useState(title);
  const [status, setStatus] = useState<Busy>(null);
  return (
    <Dialog.Root
      open={open}
      onOpenChange={(next) => {
        onOpenChange(next);
        if (next) {
          setName(title);
          setStatus(null);
        }
      }}
    >
      <Dialog.Portal>
        <Dialog.Overlay {...stylex.props(dialog.overlay)} />
        <Dialog.Content {...stylex.props(dialog.small)}>
          <Dialog.Title {...stylex.props(dialog.title)}>Rename this chat</Dialog.Title>
          <Dialog.Description {...stylex.props(ui.srOnly)}>
            A new name for the chat.
          </Dialog.Description>
          <form
            {...stylex.props(dialog.form)}
            onSubmit={(event) => {
              event.preventDefault();
              setStatus({ text: "Renaming", error: false });
              renameChat(id, name).then(
                () => onOpenChange(false),
                (error: Error) => setStatus({ text: error.message, error: true }),
              );
            }}
          >
            <TextField
              aria-label="Name"
              value={name}
              autoFocus
              onInput={(event) => setName(event.currentTarget.value)}
              onFocus={(event) => event.currentTarget.select()}
            />
            {status ? <Status text={status.text} error={status.error} /> : null}
            <div {...stylex.props(dialog.buttons)}>
              <Dialog.Close asChild>
                <Button>Cancel</Button>
              </Dialog.Close>
              <Button kind="primary" type="submit">
                Rename
              </Button>
            </div>
          </form>
        </Dialog.Content>
      </Dialog.Portal>
    </Dialog.Root>
  );
}

function DeleteDialog({
  open,
  onOpenChange,
  id,
  title,
}: {
  open: boolean;
  onOpenChange: (open: boolean) => void;
  id: string;
  title: string;
}) {
  const [status, setStatus] = useState<Busy>(null);
  return (
    <AlertDialog.Root
      open={open}
      onOpenChange={(next) => {
        onOpenChange(next);
        if (next) setStatus(null);
      }}
    >
      <AlertDialog.Portal>
        <AlertDialog.Overlay {...stylex.props(dialog.overlay)} />
        <AlertDialog.Content {...stylex.props(dialog.small)}>
          <AlertDialog.Title {...stylex.props(dialog.title)}>Delete this chat?</AlertDialog.Title>
          <AlertDialog.Description {...stylex.props(dialog.body)}>
            “{title || "New chat"}” and its transcript are removed from this computer.
          </AlertDialog.Description>
          {status ? <Status text={status.text} error={status.error} /> : null}
          <div {...stylex.props(dialog.buttons)}>
            <AlertDialog.Cancel asChild>
              <Button>Cancel</Button>
            </AlertDialog.Cancel>
            <Button
              kind="danger"
              disabled={status !== null && !status.error}
              onClick={() => {
                setStatus({ text: "Deleting", error: false });
                deleteChat(id).then(
                  () => onOpenChange(false),
                  (error: Error) =>
                    setStatus({ text: `Not deleted. ${error.message}`, error: true }),
                );
              }}
            >
              Delete
            </Button>
          </div>
        </AlertDialog.Content>
      </AlertDialog.Portal>
    </AlertDialog.Root>
  );
}

const styles = stylex.create({
  bar: {
    position: "relative",
    zIndex: 10,
    display: "flex",
    alignItems: "center",
    columnGap: space.x1,
    flexShrink: 0,
    height: size.topbar,
    paddingInline: { default: space.x3, [media.compact]: space.x1 },
    backgroundColor: colors.bg,
  },
  title: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x1,
    minWidth: 0,
    maxWidth: "min(560px, 100%)",
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    fontSize: { default: type.title, [media.phone]: type.text },
    fontWeight: 500,
    color: colors.primary,
    backgroundColor: {
      default: "transparent",
      ":hover": { [media.hover]: colors.hover },
      ":disabled": "transparent",
    },
    cursor: { default: "pointer", ":disabled": "default" },
  },
  titleOpen: { backgroundColor: colors.hover },
  menu: { minWidth: "240px" },
  end: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x3,
    marginInlineStart: "auto",
    flexShrink: 0,
  },
  offline: { display: "flex", alignItems: "center", columnGap: space.x3 },
});
