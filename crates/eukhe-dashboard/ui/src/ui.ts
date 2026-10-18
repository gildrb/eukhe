import * as stylex from "@stylexjs/stylex";
import { colors, fonts, media, radius, shadows, size, space, type } from "./tokens.stylex.ts";

const appear = stylex.keyframes({ from: { opacity: 0 }, to: { opacity: 1 } });

/** Light passing over the words of a live status, right to left. */
const sweep = stylex.keyframes({
  from: { backgroundPosition: "100% 0" },
  to: { backgroundPosition: "-100% 0" },
});

/** Shared styles: text roles, controls, and the one look of every menu and popover. */
export const ui = stylex.create({
  /** The one live-status look: the words, with a sweep of light over them (no spinner, no dots). */
  shimmer: {
    color: "transparent",
    backgroundImage: `linear-gradient(90deg, ${colors.tertiary} 0%, ${colors.tertiary} 40%, ${colors.primary} 50%, ${colors.tertiary} 60%, ${colors.tertiary} 100%)`,
    backgroundSize: "200% 100%",
    backgroundClip: "text",
    WebkitBackgroundClip: "text",
    animationName: { default: null, [media.motion]: sweep },
    animationDuration: "2s",
    animationTimingFunction: "linear",
    animationIterationCount: "infinite",
  },
  focusRing: {
    outline: { default: "none", ":focus-visible": `1px solid ${colors.primary}` },
    outlineOffset: "2px",
  },
  reset: {
    appearance: "none",
    margin: 0,
    padding: 0,
    borderWidth: 0,
    backgroundColor: "transparent",
    color: "inherit",
    fontFamily: "inherit",
    fontSize: "inherit",
    fontWeight: "inherit",
    lineHeight: "inherit",
    fontFeatureSettings: "inherit",
    textAlign: "start",
    cursor: "pointer",
    touchAction: "manipulation",
    userSelect: "none",
    WebkitUserSelect: "none",
  },
  small: { fontSize: type.small, lineHeight: type.smallLine },
  text: { fontSize: type.text, lineHeight: type.textLine },
  title: {
    fontSize: type.title,
    lineHeight: type.textLine,
    fontWeight: 500,
    letterSpacing: "-0.01em",
  },
  mono: { fontFamily: fonts.mono, fontFeatureSettings: "normal" },
  figures: { fontVariantNumeric: "tabular-nums" },
  secondary: { color: colors.secondary },
  tertiary: { color: colors.tertiary },
  strong: { fontWeight: 500 },
  ellipsis: { overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap", minWidth: 0 },
  srOnly: {
    position: "absolute",
    width: "1px",
    height: "1px",
    padding: 0,
    margin: "-1px",
    overflow: "hidden",
    clip: "rect(0, 0, 0, 0)",
    whiteSpace: "nowrap",
    borderWidth: 0,
  },
  icon: { display: "block", flexShrink: 0, width: "18px", height: "18px" },
  iconSmall: { display: "block", flexShrink: 0, width: "16px", height: "16px" },

  /**
   * A menu or popover: the page's raised ground, a hairline edge, a soft
   * shadow, 6px of padding inside a 14px corner so 8px rows sit concentric
   * (as introspectum.si's logo menu); it fades in.
   */
  menu: {
    zIndex: 50,
    boxSizing: "border-box",
    minWidth: "220px",
    maxWidth: "calc(100vw - 16px)",
    maxHeight:
      "var(--radix-dropdown-menu-content-available-height, var(--radix-popover-content-available-height, 80dvh))",
    overflowY: "auto",
    padding: "6px",
    borderWidth: "1px",
    borderStyle: "solid",
    borderColor: colors.hairline,
    borderRadius: radius.menu,
    backgroundColor: colors.raised,
    boxShadow: shadows.raised,
    color: colors.primary,
    outline: "none",
    animationName: { default: null, [media.motion]: appear },
    animationDuration: "120ms",
    animationTimingFunction: "ease-out",
  },
  /** One choice: the whole row answers the pointer and the arrow keys, on a shade of its own. */
  menuItem: {
    position: "relative",
    display: "flex",
    alignItems: "center",
    columnGap: space.x3,
    minHeight: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    outline: "none",
    backgroundColor: {
      default: "transparent",
      ":hover": { [media.hover]: colors.hover },
      ":focus": colors.hover,
    },
    color: colors.primary,
    fontSize: type.text,
    lineHeight: type.textLine,
    textDecoration: "none",
    cursor: "pointer",
    userSelect: "none",
    WebkitUserSelect: "none",
  },
  menuDanger: { color: colors.danger },
  menuSeparator: {
    height: "1px",
    marginBlock: "6px",
    marginInline: "-6px",
    backgroundColor: colors.hairline,
  },
  menuLabel: {
    paddingInline: space.x3,
    paddingTop: space.x2,
    paddingBottom: space.x1,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: colors.tertiary,
  },
  menuTrail: {
    marginInlineStart: "auto",
    color: colors.tertiary,
    fontSize: type.small,
    lineHeight: type.smallLine,
  },
  menuStatus: {
    paddingInline: space.x3,
    paddingBlock: space.x2,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: colors.secondary,
  },
});
