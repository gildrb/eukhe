import * as stylex from "@stylexjs/stylex";
import { colors, media, radius, shadows, space, type } from "../tokens.stylex.ts";

const fadeIn = stylex.keyframes({ from: { opacity: 0 }, to: { opacity: 1 } });
const rise = stylex.keyframes({
  from: { opacity: 0, transform: "translate(-50%, -48%) scale(0.98)" },
  to: { opacity: 1, transform: "translate(-50%, -50%) scale(1)" },
});

/** The look of every dialog: a scrim, and a raised card centred over it. */
export const dialog = stylex.create({
  overlay: {
    position: "fixed",
    inset: 0,
    zIndex: 40,
    backgroundColor: colors.scrim,
    animationName: { default: null, [media.motion]: fadeIn },
    animationDuration: "150ms",
    animationTimingFunction: "ease-out",
  },
  small: {
    position: "fixed",
    top: "50%",
    left: "50%",
    zIndex: 40,
    display: "flex",
    flexDirection: "column",
    rowGap: space.x4,
    width: "min(420px, calc(100vw - 32px))",
    padding: space.x6,
    borderRadius: radius.bubble,
    borderWidth: "1px",
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: colors.raised,
    boxShadow: shadows.raised,
    color: colors.primary,
    transform: "translate(-50%, -50%)",
    outline: "none",
    animationName: { default: null, [media.motion]: rise },
    animationDuration: "180ms",
    animationTimingFunction: "cubic-bezier(0.2, 0, 0, 1)",
  },
  title: { fontSize: type.title, lineHeight: type.textLine, fontWeight: 500, margin: 0 },
  body: { color: colors.secondary, margin: 0 },
  form: { display: "flex", flexDirection: "column", rowGap: space.x4 },
  buttons: {
    display: "flex",
    justifyContent: "flex-end",
    columnGap: space.x2,
    flexWrap: "wrap",
    rowGap: space.x2,
  },
});
