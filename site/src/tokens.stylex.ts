import * as stylex from "@stylexjs/stylex";

const light = "@media (prefers-color-scheme: light)";

/**
 * Every color on the page, in OKLCH, per theme. The one source: `colors` below sets them as CSS
 * variables.
 *
 * gildrb.com's forge palette, same names and values (`gildrb.com/src/tokens.stylex.ts`): an
 * umber page, ivory text, bronze below it; each ladder's hue climbs from ember (55) to gilt (85)
 * with its lightness. `primary`: headings, the cursor, the selection. `article`: the text.
 * `tertiary`: Markdown marks, comments, underlines at rest. WCAG on `bg`, dark: primary 16.9:1,
 * article 13.6:1, tertiary 6.5:1. Light: 16.1:1, 12.4:1, 5.5:1.
 */
export const palette = {
  bg: { dark: "oklch(15.5% 0.013 55)", light: "oklch(96.5% 0.012 85)" },
  primary: { dark: "oklch(95% 0.02 85)", light: "oklch(21% 0.018 50)" },
  article: { dark: "oklch(88% 0.024 80)", light: "oklch(30% 0.022 52)" },
  tertiary: { dark: "oklch(67% 0.042 64)", light: "oklch(50% 0.036 58)" },
};

export const colors = stylex.defineVars({
  bg: { default: palette.bg.dark, [light]: palette.bg.light },
  primary: { default: palette.primary.dark, [light]: palette.primary.light },
  article: { default: palette.article.dark, [light]: palette.article.light },
  tertiary: { default: palette.tertiary.dark, [light]: palette.tertiary.light },
});

/** Page metrics: 12px type on a 20px line, a 40px inset, a 68-character measure. */
export const type = stylex.defineConsts({
  family: '"Paper Mono", ui-monospace, "SF Mono", Menlo, Consolas, monospace',
  size: "12px",
  leading: "20px",
  bold: "700",
  inset: "40px",
  insetPhone: "20px",
  measure: "68ch",
});
