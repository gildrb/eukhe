// The "pairing needed" screen: shown instead of the app while the tab has
// no pairing token, or the server refused it (a rotation replaced it).
// The user opens the link `eukhe dashboard` prints, or pastes it here (an
// app on a phone's home screen has its own storage, so it pairs here).

import * as stylex from "@stylexjs/stylex";
import { useState } from "react";
import { pair } from "../lib/link.ts";
import { useStore } from "../lib/store.ts";
import { colors, size, space } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { Button, Status, TextField } from "./controls.tsx";

export function Pairing() {
  const refused = useStore((state) => state.link.error);
  const [text, setText] = useState("");
  const [wrong, setWrong] = useState(false);
  const submit = () => {
    const paired = pair(text);
    setWrong(!paired);
    if (paired) setText("");
  };
  return (
    <main {...stylex.props(styles.page)}>
      <form
        {...stylex.props(styles.card)}
        onSubmit={(event) => {
          event.preventDefault();
          submit();
        }}
      >
        <h1 {...stylex.props(ui.title)}>Pairing needed</h1>
        <p {...stylex.props(ui.secondary)}>
          Open the link that <code {...stylex.props(ui.mono)}>eukhe dashboard</code> prints on the
          computer that runs it. Behind a forwarder (poros, tailscale serve), add its{" "}
          <code {...stylex.props(ui.mono)}>#token=…</code> part to the forwarder's link. Or paste
          the link here.
        </p>
        {refused ? <Status text={refused} error /> : null}
        <label for="pairing-link" {...stylex.props(ui.srOnly)}>
          Pairing link
        </label>
        <TextField
          id="pairing-link"
          type="password"
          autoComplete="off"
          spellcheck={false}
          placeholder="Pairing link"
          value={text}
          onInput={(event) => {
            setText(event.currentTarget.value);
            setWrong(false);
          }}
          mono
        />
        {wrong ? <Status text="This text holds no pairing token." error /> : null}
        <Button kind="primary" type="submit" disabled={!text.trim()}>
          Pair
        </Button>
      </form>
    </main>
  );
}

const styles = stylex.create({
  page: {
    display: "flex",
    alignItems: "center",
    justifyContent: "center",
    minHeight: "100dvh",
    paddingInline: space.x6,
    backgroundColor: colors.bg,
  },
  card: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x3,
    width: size.alert,
  },
});
