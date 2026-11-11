/**
 * The site's epigraphs: Attic Greek the README does not carry, one under a section's heading at
 * most, keyed by that heading's line in the README. Each is the Greek as Perseus prints it (Burnet's
 * Plato, Bywater's Ethics, Ross's Metaphysics and Politics), then a plain English translation and
 * the citation. The README is the repository's, read at build time: `source.ts` leaves out (and
 * names) an epigraph whose heading the README does not hold once, so a README edit never breaks
 * the site.
 */
export const epigraphs: ReadonlyMap<string, readonly string[]> = new Map([
  [
    "# Eukhe",
    [
      "μὴ παντάπασιν ἡμᾶς εὐχὰς εἰρηκέναι, ἀλλὰ χαλεπὰ μέν, δυνατὰ δέ πῃ.",
      "That we have not spoken mere wishes, but things hard, yet somehow possible. (Plato, Republic 7.540d)",
    ],
  ],
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
