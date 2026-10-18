// Locale-aware figures (Intl with navigator.languages). Every unit is
// joined to its number with a no-break space, so `10 MB` never wraps.

const locales = navigator.languages.length ? [...navigator.languages] : undefined;
const NBSP = "\u00a0";
const NONE = "–";

const integer = new Intl.NumberFormat(locales, { maximumFractionDigits: 0 });
const oneDecimal = new Intl.NumberFormat(locales, { maximumFractionDigits: 1 });
const compact = new Intl.NumberFormat(locales, { notation: "compact", maximumFractionDigits: 1 });
const percentFormat = new Intl.NumberFormat(locales, {
  style: "percent",
  maximumFractionDigits: 0,
});
const dateFormat = new Intl.DateTimeFormat(locales, {
  year: "numeric",
  month: "short",
  day: "numeric",
});
const monthFormat = new Intl.DateTimeFormat(locales, { year: "numeric", month: "long" });
const timeFormat = new Intl.DateTimeFormat(locales, { hour: "numeric", minute: "2-digit" });

function asDate(value: unknown): Date {
  if (value instanceof Date) return value;
  if (typeof value === "number" || typeof value === "string") return new Date(value);
  return new Date(Number.NaN);
}

function hms(total: number): string {
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = String(total % 60).padStart(2, "0");
  return hours > 0
    ? `${hours}:${String(minutes).padStart(2, "0")}:${seconds}`
    : `${minutes}:${seconds}`;
}

export const fmt = {
  /** An integer (`1,204`). */
  num(value: number): string {
    return Number.isFinite(value) ? integer.format(value) : NONE;
  },
  /** Bytes in decimal units (`84 KB`, `1.2 MB`). */
  bytes(value: number): string {
    if (!Number.isFinite(value)) return NONE;
    const units = ["B", "KB", "MB", "GB", "TB"];
    let size = value;
    let unit = 0;
    while (size >= 1000 && unit < units.length - 1) {
      size /= 1000;
      unit += 1;
    }
    return `${unit === 0 ? integer.format(size) : oneDecimal.format(size)}${NBSP}${units[unit]}`;
  },
  /** A span of milliseconds: `0.8 s`, `12 s`, `2:17`, `1:02:05`. */
  duration(ms: number): string {
    if (!Number.isFinite(ms) || ms < 0) return NONE;
    if (ms < 10_000) return `${oneDecimal.format(Math.floor(ms / 100) / 10)}${NBSP}s`;
    const total = Math.floor(ms / 1000);
    return total < 60 ? `${integer.format(total)}${NBSP}s` : hms(total);
  },
  /** Elapsed time as a clock (`0:07`, `2:17`, `1:02:05`). */
  clock(ms: number): string {
    return !Number.isFinite(ms) || ms < 0 ? "0:00" : hms(Math.floor(ms / 1000));
  },
  /** Whole seconds, rounded up (`8 s`). */
  seconds(ms: number): string {
    return `${integer.format(Math.max(0, Math.ceil(ms / 1000)))}${NBSP}s`;
  },
  /** A token count: exact below 10,000, compact above (`612`, `76K`). */
  tokens(value: number, unit = true): string {
    if (!Number.isFinite(value)) return NONE;
    const figure = value < 10_000 ? integer.format(value) : compact.format(value);
    return unit ? `${figure}${NBSP}tok` : figure;
  },
  /** Tokens per second (`41 tok/s`, `3.5 tok/s`). */
  rate(perSecond: number): string {
    if (!Number.isFinite(perSecond) || perSecond <= 0) return NONE;
    const figure = perSecond < 10 ? oneDecimal.format(perSecond) : integer.format(perSecond);
    return `${figure}${NBSP}tok/s`;
  },
  /** A cost in US dollars, always two decimals (four below one cent). */
  cost(dollars: number): string {
    if (!Number.isFinite(dollars)) return NONE;
    const digits = dollars > 0 && dollars < 0.01 ? 4 : 2;
    return new Intl.NumberFormat(locales, {
      style: "currency",
      currency: "USD",
      minimumFractionDigits: digits,
      maximumFractionDigits: digits,
    }).format(dollars);
  },
  /** A calendar date (`Oct 18, 2026`). */
  date(value: unknown): string {
    const day = asDate(value);
    return Number.isNaN(day.getTime()) ? NONE : dateFormat.format(day);
  },
  /** A month (`September 2026`). */
  month(value: unknown): string {
    const day = asDate(value);
    return Number.isNaN(day.getTime()) ? NONE : monthFormat.format(day);
  },
  /** A clock time (`2:05 PM`). */
  time(value: unknown): string {
    const moment = asDate(value);
    return Number.isNaN(moment.getTime()) ? NONE : timeFormat.format(moment);
  },
  /** A fraction (0..1) as a percentage. */
  percent(value: number): string {
    return Number.isFinite(value) ? percentFormat.format(value) : NONE;
  },
};

/** A date range (`Oct 2, 2026 – Oct 5, 2026`), one date when both fall on the same day. */
export function dateSpan(first: unknown, last: unknown): string {
  const start = asDate(first);
  const end = asDate(last);
  if (Number.isNaN(start.getTime())) return "";
  if (Number.isNaN(end.getTime()) || start.toDateString() === end.toDateString())
    return fmt.date(start);
  return `${fmt.date(start)} – ${fmt.date(end)}`;
}
