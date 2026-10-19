import * as stylex from "@stylexjs/stylex";
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
    zIndex: layer.overlay,
    backgroundColor: colors.scrim,
    animationName: { default: null, [media.motion]: fadeIn },
    animationDuration: motion.fast,
    animationTimingFunction: "ease-out",
  },
  small: {
    position: "fixed",
    top: "50%",
    left: "50%",
    zIndex: layer.overlay,
    display: "flex",
    flexDirection: "column",
    rowGap: space.x4,
    width: size.alert,
    padding: space.x6,
    borderRadius: radius.bubble,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: colors.raised,
    boxShadow: shadows.raised,
    color: colors.primary,
    transform: "translate(-50%, -50%)",
    outline: "none",
    animationName: { default: null, [media.motion]: rise },
    animationDuration: motion.rise,
    animationTimingFunction: motion.emphasized,
  },
  title: { fontSize: type.title, lineHeight: type.textLine, fontWeight: weight.medium, margin: 0 },
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
