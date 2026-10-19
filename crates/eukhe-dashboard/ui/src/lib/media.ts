// The media rules of tokens.stylex.ts, for scripts: `matchMedia` takes the
// query without its `@media `.

import { useEffect, useState } from "react";

/** The query of a `media` rule, for `matchMedia`. */
export function mediaQuery(rule: string): string {
  return rule.replace(/^@media /, "");
}

/** True while the `media` rule matches. */
export function useMedia(rule: string): boolean {
  const query = mediaQuery(rule);
  const [matches, setMatches] = useState(() => matchMedia(query).matches);
  useEffect(() => {
    const list = matchMedia(query);
    const sync = () => setMatches(list.matches);
    sync();
    list.addEventListener("change", sync);
    return () => list.removeEventListener("change", sync);
  }, [query]);
  return matches;
}
