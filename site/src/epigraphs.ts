/**
 * The site's epigraphs: Attic Greek the README does not carry, one under a heading at most. Each is
 * the Greek as Perseus prints it (Burnet's Plato, Bywater's Ethics, Ross's Metaphysics and
 * Politics), then a plain English translation and the citation. The README is the repository's,
 * read at build time, so a README edit never breaks the site.
 */

/** Under the README's first level-1 heading, whatever its text (`source.ts`). */
export const titleEpigraph: readonly string[] = [
  "μὴ παντάπασιν ἡμᾶς εὐχὰς εἰρηκέναι, ἀλλὰ χαλεπὰ μέν, δυνατὰ δέ πῃ.",
  "That we have not spoken mere wishes, but things hard, yet somehow possible. (Plato, Republic 7.540d)",
];

/**
 * The others, keyed by their section's heading line in the README: `source.ts` leaves out (and
 * names) one whose heading the README does not hold once.
 */
export const epigraphs: ReadonlyMap<string, readonly string[]> = new Map([
  [
    "## Laws",
    [
      "τὸν ἄρα νόμον ἄρχειν αἱρετώτερον μᾶλλον ἢ τῶν πολιτῶν ἕνα τινά.",
      "It is better, then, that the law rule than any one of the citizens. (Aristotle, Politics 3.1287a19-20)",
    ],
  ],
  [
    "## Limitations",
    [
      "ἃ μὴ οἶδα οὐδὲ οἴομαι εἰδέναι.",
      "What I do not know, I do not think I know either. (Plato, Apology 21d)",
    ],
  ],
]);
