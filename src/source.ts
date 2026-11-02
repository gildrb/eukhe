import { epigraphs } from "./epigraphs.ts";
import head from "./content/head.md?raw";
import readme from "./content/eukhe/README.md?raw";

/**
 * The install command: the one block with a `[copy]` button. Other commands (`cd /path/to/project`)
 * hold paths of no use on the reader's machine. The README must hold it as a line of its own (a
 * trailing `# comment` aside).
 */
export const install = "curl -fsSL https://eukhe.com/install | sh";
if (!readme.split("\n").some((line) => line.split(/\s+#\s/)[0]?.trimEnd() === install))
  throw new Error("README.md lacks the install command");

/** The README, each epigraph's quote under its heading; the README's own lines stay as they are. */
function withEpigraphs(markdown: string): string {
  const lines = markdown.split("\n");
  for (const heading of epigraphs.keys())
    if (lines.filter((line) => line === heading).length !== 1)
      throw new Error(`README.md has no single "${heading}" line for its epigraph`);
  return lines
    .flatMap((line) => {
      const quote = epigraphs.get(line);
      return quote === undefined ? [line] : [line, "", ...quote.map((text) => `> ${text}`)];
    })
    .join("\n");
}

/** Where eukhe's source lives: the page's last line, after the README. */
const repository = "https://github.com/gildrb/eukhe";

/**
 * The whole page as Markdown: what the page shows, and what `Accept: text/markdown` gets. The
 * site's header, then eukhe's README (`scripts/eukhe.ts` keeps the copy equal to it) with the
 * site's epigraphs, then the source.
 */
export const source = `${head.trimEnd()}\n\n${withEpigraphs(readme).trimEnd()}\n\nSource: [${repository}](${repository})\n`;

export const notFound = `EUKHE
404: NO PAGE HERE
2026

~*~ εὐχή: a wish, a prayer ~*~

# NOT FOUND

Back to [eukhe.com](/).
`;
