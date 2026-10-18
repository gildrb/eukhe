// Locale-aware figures (Intl with navigator.languages). Every unit is
// joined to its number with a no-break space, so `10 MB` never wraps.

const locales = navigator.languages && navigator.languages.length ? [...navigator.languages] : undefined;
const NBSP = '\u00a0';

const integer = new Intl.NumberFormat(locales, { maximumFractionDigits: 0 });
const oneDecimal = new Intl.NumberFormat(locales, { maximumFractionDigits: 1 });
const compact = new Intl.NumberFormat(locales, { notation: 'compact', maximumFractionDigits: 1 });
const percentFormat = new Intl.NumberFormat(locales, { style: 'percent', maximumFractionDigits: 0 });
const dateFormat = new Intl.DateTimeFormat(locales, { year: 'numeric', month: 'short', day: 'numeric' });
const timeFormat = new Intl.DateTimeFormat(locales, { hour: 'numeric', minute: '2-digit' });
const relativeFormat = new Intl.RelativeTimeFormat(locales, { numeric: 'auto', style: 'short' });

/** An integer or a one-decimal number (`1,204`, `3.5`). */
export function num(value, { decimals = 0 } = {}) {
  if (!Number.isFinite(value)) return '—';
  if (decimals === 0) return integer.format(value);
  return new Intl.NumberFormat(locales, { maximumFractionDigits: decimals, minimumFractionDigits: decimals }).format(value);
}

/** Bytes in decimal units (`84 KB`, `1.2 MB`). */
export function bytes(value) {
  if (!Number.isFinite(value)) return '—';
  const units = ['B', 'KB', 'MB', 'GB', 'TB'];
  let size = value;
  let unit = 0;
  while (size >= 1000 && unit < units.length - 1) {
    size /= 1000;
    unit += 1;
  }
  return `${unit === 0 ? integer.format(size) : oneDecimal.format(size)}${NBSP}${units[unit]}`;
}

/** A span of milliseconds: `0.8 s`, `12 s`, `2:17`, `1:02:05`. */
export function duration(ms) {
  if (!Number.isFinite(ms) || ms < 0) return '—';
  if (ms < 10_000) return `${oneDecimal.format(Math.floor(ms / 100) / 10)}${NBSP}s`;
  const total = Math.floor(ms / 1000);
  if (total < 60) return `${integer.format(total)}${NBSP}s`;
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = String(total % 60).padStart(2, '0');
  if (hours > 0) return `${hours}:${String(minutes).padStart(2, '0')}:${seconds}`;
  return `${minutes}:${seconds}`;
}

/** Elapsed time as a clock (`0:07`, `2:17`, `1:02:05`). */
export function clock(ms) {
  if (!Number.isFinite(ms) || ms < 0) return '0:00';
  const total = Math.floor(ms / 1000);
  const hours = Math.floor(total / 3600);
  const minutes = Math.floor((total % 3600) / 60);
  const seconds = String(total % 60).padStart(2, '0');
  return hours > 0 ? `${hours}:${String(minutes).padStart(2, '0')}:${seconds}` : `${minutes}:${seconds}`;
}

/** Whole seconds, rounded up (`8 s`). */
export function seconds(ms) {
  return `${integer.format(Math.max(0, Math.ceil(ms / 1000)))}${NBSP}s`;
}

/** A token count: exact below 10,000, compact above (`612`, `76k`). */
export function tokens(value, { unit = true } = {}) {
  if (!Number.isFinite(value)) return '—';
  const figure = value < 10_000 ? integer.format(value) : compact.format(value);
  return unit ? `${figure}${NBSP}tok` : figure;
}

/** Tokens per second (`41 tok/s`, `3.5 tok/s`). */
export function rate(perSecond) {
  if (!Number.isFinite(perSecond) || perSecond <= 0) return '—';
  const figure = perSecond < 10 ? oneDecimal.format(perSecond) : integer.format(perSecond);
  return `${figure}${NBSP}tok/s`;
}

/** A cost in US dollars, always two decimals (four below one cent). */
export function cost(dollars) {
  if (!Number.isFinite(dollars)) return '—';
  const digits = dollars > 0 && dollars < 0.01 ? 4 : 2;
  return new Intl.NumberFormat(locales, {
    style: 'currency',
    currency: 'USD',
    minimumFractionDigits: digits,
    maximumFractionDigits: digits,
  }).format(dollars);
}

function asDate(value) {
  if (value instanceof Date) return value;
  if (typeof value === 'number') return new Date(value);
  if (typeof value === 'string') return new Date(value);
  return new Date(Number.NaN);
}

/** A calendar date (`Oct 18, 2026`). */
export function date(value) {
  const day = asDate(value);
  return Number.isNaN(day.getTime()) ? '—' : dateFormat.format(day);
}

/** A clock time (`14:05`). */
export function time(value) {
  const moment = asDate(value);
  return Number.isNaN(moment.getTime()) ? '—' : timeFormat.format(moment);
}

/** Time from now (`3 hr. ago`, `now`). */
export function relative(value, now = Date.now()) {
  const moment = asDate(value);
  if (Number.isNaN(moment.getTime())) return '—';
  const seconds = Math.round((moment.getTime() - now) / 1000);
  const units = [
    ['year', 31_557_600],
    ['month', 2_629_800],
    ['week', 604_800],
    ['day', 86_400],
    ['hour', 3600],
    ['minute', 60],
  ];
  const magnitude = Math.abs(seconds);
  for (const [unit, size] of units) {
    if (magnitude >= size) return relativeFormat.format(Math.round(seconds / size), unit);
  }
  return relativeFormat.format(0, 'second');
}

/** A fraction (0..1) or a percentage (0..100 with `{ of100: true }`). */
export function percent(value, { of100 = false } = {}) {
  if (!Number.isFinite(value)) return '—';
  return percentFormat.format(of100 ? value / 100 : value);
}

export const fmt = { num, bytes, duration, clock, seconds, tokens, rate, cost, date, time, relative, percent };
