// The pairing token (docs/dashboard.md, "Pairing"). `eukhe dashboard` puts
// it in the URL's fragment (`#token=<64 hex digits>`), which a browser never
// sends to a server. The page takes it out of the address bar at once,
// keeps it in this browser's storage (so a bookmark of the page keeps
// working), and the link presents it in the first frame of each socket.
// The token never goes into the page, the frame log or a message.

const TOKEN_KEY = "eukhe.pairing";
const TOKEN = /^[0-9a-fA-F]{64}$/;
const IN_FRAGMENT = /(?:^#|[#&])token=([0-9a-fA-F]{64})(?:&|$)/;

/** The token when storage is not available (a private window). */
let kept: string | null = null;

function store(token: string | null) {
  kept = token;
  try {
    if (token) localStorage.setItem(TOKEN_KEY, token);
    else localStorage.removeItem(TOKEN_KEY);
  } catch {
    // Storage is off: the token lives as long as the page.
  }
}

/** The token that `text` holds: a pairing link, its fragment, or the token itself. */
function tokenIn(text: string): string | null {
  const trimmed = text.trim();
  if (TOKEN.test(trimmed)) return trimmed.toLowerCase();
  const hash = trimmed.includes("#") ? trimmed.slice(trimmed.indexOf("#")) : "";
  const found = IN_FRAGMENT.exec(hash)?.[1];
  return found ? found.toLowerCase() : null;
}

/** The kept token, or null when this browser is not paired. */
export function pairingToken(): string | null {
  try {
    return localStorage.getItem(TOKEN_KEY) ?? kept;
  } catch {
    return kept;
  }
}

/** Keep the token that `text` (a pasted link or token) holds. False when it holds none. */
export function adoptToken(text: string): boolean {
  const token = tokenIn(text);
  if (!token) return false;
  store(token);
  return true;
}

/** The server refused the kept token (a rotation replaced it): forget it. */
export function forgetToken(): void {
  store(null);
}

/** Move a token in the address bar's fragment into storage; true when there was one. */
export function takeFromAddress(): boolean {
  if (!IN_FRAGMENT.test(location.hash)) return false;
  adoptToken(location.hash);
  history.replaceState(history.state, "", `${location.pathname}${location.search}#/`);
  return true;
}

// The link's token moves into storage before anything reads the route.
takeFromAddress();
