import * as stylex from "@stylexjs/stylex";

/**
 * Breakpoints: phone < 768, tablet 768–1023 (the phone layout, a wider
 * column), desktop ≥ 1024 (the sidebar stays). `touch` sizes every hit
 * area to 44px.
 */
export const media = stylex.defineConsts({
  phone: "@media (max-width: 767px)",
  compact: "@media (max-width: 1023px)",
  desktop: "@media (min-width: 1024px)",
  hover: "@media (hover: hover)",
  touch: "@media (pointer: coarse)",
  motion: "@media (prefers-reduced-motion: no-preference)",
});

/**
 * Monochrome neutrals. Each value is `light-dark(light, dark)`: the root's
 * `color-scheme` (System, Light or Dark in Settings; theme.js sets it
 * before the first paint) picks one, so no class swaps a palette.
 */
const pair = (light: string, dark: string) => `light-dark(${light}, ${dark})`;

export const colors = stylex.defineVars({
  /** The conversation's ground. */
  bg: pair("#ffffff", "#212121"),
  /** The sidebar's ground, a step away from the conversation. */
  sidebar: pair("#f9f9f9", "#181818"),
  /** Menus, popovers and dialogs: on the page's ground, lifted by an edge and a shadow. */
  raised: pair("#ffffff", "#2a2a2a"),
  /** Fills: the composer, the user's bubbles, code, the selected row, a pressed control. */
  surface: pair("#f4f4f4", "#303030"),
  /** A row under the pointer or the keyboard, on any ground. */
  hover: pair("#ececec", "#3a3a3a"),
  primary: pair("#0d0d0d", "#ececec"),
  secondary: pair("#5d5d5d", "#b4b4b4"),
  tertiary: pair("#737373", "#9b9b9b"),
  hairline: pair("rgb(0 0 0 / 0.1)", "rgb(255 255 255 / 0.1)"),
  /** The scrim behind the drawer and dialogs. */
  scrim: pair("rgb(0 0 0 / 0.2)", "rgb(0 0 0 / 0.5)"),
  danger: pair("#c4271b", "#ff8a80"),
});

export const shadows = stylex.defineVars({
  /** Menus and popovers: a close shadow and a wide one, so they lift off what they cover. */
  raised: pair(
    "0 1px 2px rgb(0 0 0 / 0.06), 0 8px 24px rgb(0 0 0 / 0.1)",
    "0 1px 2px rgb(0 0 0 / 0.3), 0 8px 24px rgb(0 0 0 / 0.4)",
  ),
});

/** The 4px grid. */
export const space = stylex.defineConsts({
  x1: "4px",
  x2: "8px",
  x3: "12px",
  x4: "16px",
  x5: "20px",
  x6: "24px",
  x8: "32px",
  x12: "48px",
});

/** The only radii: 4 inline code, 8 controls and rows, 14 menus and the send button, 18 bubbles and dialogs, 22 the composer. */
export const radius = stylex.defineConsts({
  code: "4px",
  control: "8px",
  menu: "14px",
  bubble: "18px",
  composer: "22px",
});

export const fonts = stylex.defineConsts({
  sans: 'Inter, "Inter Fallback", -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif',
  mono: '"Ioskeley Mono", "SFMono-Regular", "SF Mono", Menlo, Consolas, monospace',
  /** Interface text: case forms put hyphens and @ among capitals and figures. */
  interface: '"liga" 1, "calt" 1, "case" 1',
});

export const type = stylex.defineConsts({
  small: "14px",
  smallLine: "20px",
  text: "16px",
  textLine: "24px",
  proseLine: "26px",
  title: "19px",
});

/** Heights: 36px rows and controls with a pointer, 44px for a finger. */
export const size = stylex.defineConsts({
  row: "36px",
  touch: "44px",
  topbar: "56px",
  sidebar: "260px",
  column: "768px",
});

export const layer = stylex.defineConsts({
  topbar: 10,
  latest: 20,
  overlay: 40,
  popover: 50,
  tooltip: 60,
});

export const motion = stylex.defineConsts({
  /** gildrb's 330ms spring, as a linear() curve. */
  spring:
    "linear(0, 0.078, 0.235, 0.401, 0.549, 0.669, 0.762, 0.831, 0.882, 0.918, 0.944, 0.962, 0.974, 0.982, 0.988, 0.992, 0.995, 0.996, 0.998, 0.998, 1)",
});
