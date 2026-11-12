import { epigraphs, titleEpigraph } from "./epigraphs.ts";
// The repository's own README (the site lives in site/ of Eukhe's repository).
import readme from "../../README.md?raw";

/**
 * The install command: the one block with a `[copy]` button. Other commands (`cd /path/to/project`)
 * hold paths of no use on the reader's machine. The README must hold it as a line of its own (a
 * trailing `# comment` aside).
 */
export const install = "curl -fsSL https://eukhe.com/install | sh";
if (!readme.split("\n").some((line) => line.split(/\s+#\s/)[0]?.trimEnd() === install))
  throw new Error("README.md lacks the install command");

/**
 * The line of the README's first level-1 heading (`# `, outside code blocks), its name whatever its
 * text; -1 if it has none.
 */
function titleLine(lines: readonly string[]): number {
  let fenced = false;
  return lines.findIndex((line) => {
    if (line.startsWith("```")) fenced = !fenced;
    return !fenced && line.startsWith("# ");
  });
}

/**
 * The README, each epigraph's quote under its heading; the README's own lines stay as they are. The
 * title epigraph goes under the README's first level-1 heading, whatever its text; any other
 * epigraph whose heading the README does not hold exactly once is left out, and the build names it.
 */
function withEpigraphs(markdown: string): string {
  const lines = markdown.split("\n");
  const title = titleLine(lines);
  if (title === -1) console.warn("README.md has no `# ` heading: the title epigraph is left out");
  const placed = new Map(
    [...epigraphs].filter(([heading]) => {
      const once = lines.filter((line) => line === heading).length === 1;
      if (!once)
        console.warn(`README.md has no single "${heading}" line: its epigraph is left out`);
      return once;
    }),
  );
  return lines
    .flatMap((line, index) => {
      const quote = index === title ? titleEpigraph : placed.get(line);
      return quote === undefined ? [line] : [line, "", ...quote.map((text) => `> ${text}`)];
    })
    .join("\n");
}

/** Where eukhe's source lives: the page's last line, after the README. */
const repository = "https://github.com/gildrb/eukhe";

/**
 * The whole page as Markdown: what the page shows, and what `Accept: text/markdown` gets. Eukhe's
 * README (the repository's `README.md`, read at build time) from its own first line, with the
 * site's epigraphs, then the source.
 */
export const source = `${withEpigraphs(readme).trimEnd()}\n\nSource: [${repository}](${repository})\n`;

export const notFound = `EUKHE
404: NO PAGE HERE
2026

# NOT FOUND

Back to [eukhe.com](/).
`;
