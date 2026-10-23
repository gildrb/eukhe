import * as stylex from "@stylexjs/stylex";

// The token source: every presentation value of the dashboard is written
// here, and only here. The lint rule eukhe/token-literals (lint/tokens.ts)
// fails `vp check` on a color, length, duration, easing, layer, weight or
// opacity written in another file under src/; src/tokens.test.ts does the
// same for global.css. bend/tokens.bend holds the same table, and
// laws/tokens.bend states its rules (T2): src/tokens.test.ts
// checks that the two tables are equal.

/**
 * Breakpoints: phone < 768, tablet 768–1023 (the phone layout, a wider
 * column), desktop ≥ 1024 (the sidebar stays). `touch` sizes every hit
 * area to 44px. Scripts read a rule through `mediaQuery` (lib/format.ts).
 */
export const media = stylex.defineConsts({
  phone: "@media (max-width: 767px)",
  compact: "@media (max-width: 1023px)",
  desktop: "@media (min-width: 1024px)",
  hover: "@media (hover: hover)",
  touch: "@media (pointer: coarse)",
  motion: "@media (prefers-reduced-motion: no-preference)",
  dark: "@media (prefers-color-scheme: dark)",
});

/**
 * The palette: every color, once in each mode. A key has its light value
 * in `lightPalette` and its dark value in `darkPalette`. `colors`,
 * `shadows` and `page` pair the two with `light-dark()`: the root's
 * `color-scheme` (System, Light or Dark in Settings; theme.js sets it
 * before the first paint) selects one, so no class swaps a palette.
 * index.html, public/manifest.webmanifest and public/theme.js cannot read
 * CSS, so they write `bg` again; src/tokens.test.ts checks that they agree.
 */
export const lightPalette = stylex.defineConsts({
  bg: "#ffffff",
  sidebar: "#f9f9f9",
  raised: "#ffffff",
  surface: "#f4f4f4",
  hover: "#ececec",
  primary: "#0d0d0d",
  secondary: "#5d5d5d",
  tertiary: "#737373",
  hairline: "rgb(0 0 0 / 0.1)",
  scrim: "rgb(0 0 0 / 0.2)",
  danger: "#c4271b",
  selection: "rgb(0 0 0 / 0.14)",
  scrollbar: "rgb(0 0 0 / 0.2)",
  shadowNear: "rgb(0 0 0 / 0.06)",
  shadowFar: "rgb(0 0 0 / 0.1)",
  shadowDrawer: "rgb(0 0 0 / 0.2)",
  shadowLatest: "rgb(0 0 0 / 0.12)",
});

export const darkPalette = stylex.defineConsts({
  bg: "#212121",
  sidebar: "#181818",
  raised: "#2a2a2a",
  surface: "#303030",
  hover: "#3a3a3a",
  primary: "#ececec",
  secondary: "#b4b4b4",
  tertiary: "#9b9b9b",
  hairline: "rgb(255 255 255 / 0.1)",
  scrim: "rgb(0 0 0 / 0.5)",
  danger: "#ff8a80",
  selection: "rgb(255 255 255 / 0.22)",
  scrollbar: "rgb(255 255 255 / 0.2)",
  shadowNear: "rgb(0 0 0 / 0.3)",
  shadowFar: "rgb(0 0 0 / 0.4)",
  shadowDrawer: "rgb(0 0 0 / 0.2)",
  shadowLatest: "rgb(0 0 0 / 0.12)",
});

const pair = (light: string, dark: string) => `light-dark(${light}, ${dark})`;

/** Monochrome neutrals. */
export const colors = stylex.defineVars({
  /** The conversation's ground. */
  bg: pair(lightPalette.bg, darkPalette.bg),
  /** The sidebar's ground, a step away from the conversation. */
  sidebar: pair(lightPalette.sidebar, darkPalette.sidebar),
  /** Menus, popovers and dialogs: on the page's ground, lifted by an edge and a shadow. */
  raised: pair(lightPalette.raised, darkPalette.raised),
  /** Fills: the composer, the user's bubbles, code, the selected row, a pressed control. */
  surface: pair(lightPalette.surface, darkPalette.surface),
  /** A row under the pointer or the keyboard, on any ground. */
  hover: pair(lightPalette.hover, darkPalette.hover),
  primary: pair(lightPalette.primary, darkPalette.primary),
  secondary: pair(lightPalette.secondary, darkPalette.secondary),
  tertiary: pair(lightPalette.tertiary, darkPalette.tertiary),
  hairline: pair(lightPalette.hairline, darkPalette.hairline),
  /** The scrim behind the drawer and dialogs. */
  scrim: pair(lightPalette.scrim, darkPalette.scrim),
  danger: pair(lightPalette.danger, darkPalette.danger),
});

export const shadows = stylex.defineVars({
  /** Menus and popovers: a close shadow and a wide one, so they lift off what they cover. */
  raised: pair(
    `0 1px 2px ${lightPalette.shadowNear}, 0 8px 24px ${lightPalette.shadowFar}`,
    `0 1px 2px ${darkPalette.shadowNear}, 0 8px 24px ${darkPalette.shadowFar}`,
  ),
  /** The drawer, over the conversation it covers. */
  drawer: pair(`0 0 24px ${lightPalette.shadowDrawer}`, `0 0 24px ${darkPalette.shadowDrawer}`),
  /** The "latest" button, over the conversation. */
  latest: pair(`0 2px 8px ${lightPalette.shadowLatest}`, `0 2px 8px ${darkPalette.shadowLatest}`),
});

/** The 4px grid, with the half steps a few tight spots use. */
export const space = stylex.defineConsts({
  x025: "1px",
  x05: "2px",
  x1: "4px",
  x15: "6px",
  x2: "8px",
  x25: "10px",
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

/** Line widths: hairline edges and rules, the quote bar and the meter, the focus ring's gap, icon strokes (lucide numbers). */
export const stroke = stylex.defineConsts({
  hairline: "1px",
  bar: "2px",
  offset: "2px",
  checkMark: 2.5,
  sendArrow: 2.25,
});

export const fonts = stylex.defineConsts({
  sans: 'Inter, "Inter Fallback", -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif',
  mono: '"Ioskeley Mono", "SFMono-Regular", "SF Mono", Menlo, Consolas, monospace',
  /** Interface text: case forms put hyphens and @ among capitals and figures. */
  interface: '"liga" 1, "calt" 1, "case" 1',
  /** Prose: ligatures, no case forms. */
  prose: '"liga" 1, "calt" 1',
});

/** Sizes, ascending (tiny, small, text, title), then line heights, ascending. */
export const type = stylex.defineConsts({
  tiny: "13px",
  small: "14px",
  text: "16px",
  title: "19px",
  smallLine: "20px",
  /** Small text in blocks: thinking, tool output, code. */
  blockLine: "22px",
  textLine: "24px",
  proseLine: "26px",
  titleTracking: "-0.01em",
  /** Inline code, relative to its text. */
  inlineCode: "0.875em",
  underlineOffset: "0.2em",
});

export const weight = stylex.defineConsts({
  regular: 400,
  medium: 500,
  semibold: 600,
});

export const opacity = stylex.defineConsts({
  /** An approval's effect line, under its command. */
  quiet: 0.75,
  /** A message not sent yet, a tooltip's keys, a disabled approval button. */
  dim: 0.6,
  /** A disabled button. */
  disabled: 0.5,
});

/** Heights: 36px rows and controls with a pointer, 44px for a finger. Then widths and other extents. */
export const size = stylex.defineConsts({
  row: "36px",
  touch: "44px",
  topbar: "56px",
  sidebar: "260px",
  column: "768px",
  iconSmall: "16px",
  icon: "18px",
  checkbox: "20px",
  /** Small controls with a pointer: text buttons, segments, checkboxes, disclosures. */
  control: "28px",
  /** Value and event rows in Settings, the "latest" button. */
  item: "32px",
  /** A row of the Settings section list on a phone. */
  listRow: "52px",
  thumb: "56px",
  reasoningTrigger: "120px",
  modelTriggerPhone: "132px",
  select: "180px",
  modelTrigger: "200px",
  rail: "200px",
  menu: "220px",
  titleMenu: "240px",
  image: "240px",
  /** Tall scroll panes (tool output, values, JSON) and the wide model menu. */
  pane: "320px",
  menuHeight: "80dvh",
  titleMax: "min(560px, 100%)",
  drawer: "min(85vw, 320px)",
  dialog: "min(800px, 92vw)",
  dialogHeight: "min(600px, 86dvh)",
  alert: "min(420px, calc(100vw - 32px))",
});

/** The stacking order, bottom to top. */
export const layer = stylex.defineConsts({
  topbar: 10,
  latest: 20,
  overlay: 40,
  popover: 50,
  tooltip: 60,
  skip: 70,
});

export const motion = stylex.defineConsts({
  /** gildrb's 330ms spring, as a linear() curve. */
  spring:
    "linear(0, 0.078, 0.235, 0.401, 0.549, 0.669, 0.762, 0.831, 0.882, 0.918, 0.944, 0.962, 0.974, 0.982, 0.988, 0.992, 0.995, 0.996, 0.998, 0.998, 1)",
  /** The drawer's slide (Web Animations take milliseconds). */
  springMs: 330,
  springEase: "cubic-bezier(0.2, 0.9, 0.3, 1)",
  /** Dialogs and sheets as they come in. */
  emphasized: "cubic-bezier(0.2, 0, 0, 1)",
  appear: "120ms",
  fast: "150ms",
  rise: "180ms",
  fade: "200ms",
  /** One pass of the live-status shimmer. */
  sweep: "2s",
  /** Radix tooltips, in milliseconds. */
  tooltipDelay: 500,
  tooltipSkipDelay: 300,
});

/**
 * The document itself, named so global.css can read it: StyleX styles
 * only the elements it renders, not the root, the selection or the
 * scrollbars.
 */
export const page = stylex.defineVars({
  "--page-bg": pair(lightPalette.bg, darkPalette.bg),
  "--page-text": pair(lightPalette.primary, darkPalette.primary),
  "--page-selection": pair(lightPalette.selection, darkPalette.selection),
  "--page-scrollbar": pair(lightPalette.scrollbar, darkPalette.scrollbar),
  "--page-font": fonts.sans,
  "--page-features": fonts.interface,
  "--page-size": type.text,
  "--page-line": type.textLine,
});
