import content from "./content/index.md?raw";
import { palette, type Token } from "./tokens.stylex.ts";

/** The swatch printed before each color value; the page paints it in that value. */
export const swatch = "█";

/**
 * The install command: the one block with a `[copy]` button. Other commands (`cd /path/to/project`)
 * hold paths of no use on the reader's machine. The page source must contain it as is.
 */
export const install = "curl -fsSL https://eukhe.com/install | sh";
if (!content.includes(`\n${install}\n`)) throw new Error("index.md lacks the install command");

const tokens = Object.keys(palette).filter((key): key is Token => key in palette);

/** The COLORS section: every token of `palette` with its value in each theme. */
function colorsSection(): string {
  const rows = [
    ["TOKEN", "DARK", "LIGHT"],
    ...tokens.map((token) => [
      token,
      `${swatch} ${palette[token].dark}`,
      `${swatch} ${palette[token].light}`,
    ]),
  ];
  const widths = [0, 1, 2].map((column) =>
    Math.max(...rows.map((row) => row[column]?.length ?? 0)),
  );
  const line = (cells: readonly string[]) =>
    `| ${cells.map((cell, column) => cell.padEnd(widths[column] ?? 0)).join(" | ")} |`;
  const [header, ...body] = rows;
  if (header === undefined) throw new Error("COLORS has no header row");
  return [
    "## COLORS",
    "",
    line(header),
    line(widths.map((width) => "-".repeat(width))),
    ...body.map(line),
  ].join("\n");
}

/** The whole page as Markdown: what the page shows, and what `Accept: text/markdown` gets. */
export const source = `${content.trimEnd()}\n\n${colorsSection()}\n`;

export const notFound = `404
NO PAGE HERE
2026

~*~ εὐχή: a wish, a prayer ~*~

# NOT FOUND

Back to [eukhe.com](/).
`;
