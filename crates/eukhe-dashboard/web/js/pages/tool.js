// Tool (`#/s/<id>/tool/<callId>`): one tool call whole — arguments, live
// output on the terminal surface, the result, structured details (diffs
// as +/− lines), and Copy for each.

import { definePage } from '../pages.js';
import { toolTarget } from '../turn.js';
import { backToChat, boundSession, frame, knownTools, outputText, paneHref, tick, stopTick, toolStatus, waiting } from './kit.js';

const SHOWN_LINES = 2000;
const FOLLOW_SLACK_PX = 24;

const views = new WeakMap();

function toolOf(ctx) {
  const session = boundSession(ctx);
  if (!session) return { session: null, tool: null };
  return { session, tool: knownTools(session).get(ctx.route.rest[0]) || null };
}

/** `failed · 0.2 s · import os`: status word, figure, then what the call acts on. */
function statusLine(tool, now) {
  const target = toolTarget(tool.args);
  return target ? `${toolStatus(tool, now)} · ${target}` : toolStatus(tool, now);
}

function prettyJson(value) {
  if (value === null || value === undefined) return '';
  if (typeof value === 'string') return value;
  try {
    return JSON.stringify(value, null, 2);
  } catch {
    return String(value);
  }
}

/** A numbered diff (`+N|new`, `-N|old`, ` N|context`) as glyph-led mono lines. */
function diffBlock(ui, text) {
  const node = ui.el('pre', { class: 'pg-diff mono', translate: 'no' });
  for (const line of text.split('\n')) {
    const mark = line[0];
    const kind = mark === '+' ? 'add' : mark === '-' ? 'del' : 'ctx';
    const shown = kind === 'del' ? `−${line.slice(1)}` : line;
    node.append(ui.el('span', { class: 'pg-diff-line', 'data-kind': kind, text: shown }), '\n');
  }
  return node;
}

/** Arguments: long or multi-line strings (code, commands, file text) raw under their key, the rest as JSON. */
function argsView(ui, args) {
  if (!args || typeof args !== 'object' || Array.isArray(args)) {
    return [ui.el('pre', { class: 'pg-json mono', translate: 'no', text: prettyJson(args) || '{}' })];
  }
  const entries = Object.entries(args);
  const isLong = (value) => typeof value === 'string' && (value.includes('\n') || value.length > 80);
  const rest = Object.fromEntries(entries.filter(([, value]) => !isLong(value)));
  const parts = entries.filter(([, value]) => isLong(value)).map(([key, value]) => ui.el('div', { class: 'pg-field' },
    ui.el('span', { class: 'pg-field-label mono', translate: 'no', text: key }),
    ui.el('pre', { class: 'pg-json mono', translate: 'no', text: value })));
  if (Object.keys(rest).length || !parts.length) parts.unshift(ui.el('pre', { class: 'pg-json mono', translate: 'no', text: prettyJson(rest) }));
  return parts;
}

function detailsView(ui, details) {
  if (details === null || details === undefined) return null;
  const parts = [];
  const entries = Array.isArray(details) ? details : [details];
  for (const entry of entries) {
    if (entry && typeof entry === 'object' && typeof entry.diff === 'string' && entry.diff) {
      const { diff, ...rest } = entry;
      if (typeof rest.path === 'string') parts.push(ui.el('p', { class: 'pg-line mono', translate: 'no', text: rest.path }));
      parts.push(diffBlock(ui, diff));
      const remaining = Object.keys(rest).filter((key) => key !== 'path');
      if (remaining.length) parts.push(ui.el('pre', { class: 'pg-json mono', translate: 'no', text: prettyJson(rest) }));
    } else {
      parts.push(ui.el('pre', { class: 'pg-json mono', translate: 'no', text: prettyJson(entry) }));
    }
  }
  return parts;
}

function imagesOf(output) {
  if (!output || !Array.isArray(output.content)) return [];
  return output.content.filter((block) => block.type === 'image' && block.data);
}

function render(root, ctx) {
  const { ui } = ctx;
  const parts = frame(root, ctx, { title: 'Tool', back: { ...backToChat(ctx), label: 'Back' } });
  const status = ui.el('p', { class: 'pg-status fig', role: 'status' });
  const argsBox = ui.el('div', { class: 'pg-stack' });
  const terminal = ui.el('pre', { class: 'terminal pg-terminal mono', translate: 'no', tabindex: '0', 'aria-label': 'Tool output' });
  const outputNote = ui.el('p', { class: 'pg-line small' });
  const follow = ui.button({ label: '↓ Follow', onClick: () => {
    view.following = true;
    terminal.scrollTop = terminal.scrollHeight;
    follow.hidden = true;
  } });
  follow.hidden = true;
  const showAll = ui.el('a', { class: 'link target', text: '' });
  const images = ui.el('div', { class: 'pg-images' });
  const details = ui.el('div', { class: 'pg-details' });
  const view = {
    parts,
    status,
    argsBox,
    terminal,
    outputNote,
    follow,
    showAll,
    images,
    details,
    following: true,
    cache: new Map(),
    sig: null,
    tool: null,
  };
  views.set(root, view);
  terminal.addEventListener('scroll', () => {
    const atBottom = terminal.scrollHeight - terminal.scrollTop - terminal.clientHeight <= FOLLOW_SLACK_PX;
    view.following = atBottom;
    follow.hidden = atBottom || !view.tool || view.tool.status !== 'running';
  }, { passive: true });
  view.argsSection = ui.section('Arguments', argsBox, ui.el('div', { class: 'pg-actions' }, ui.copyButton(() => prettyJson(view.tool ? view.tool.args : null), 'Copy arguments')));
  view.outputSection = ui.section('Output', terminal, ui.el('div', { class: 'pg-actions' }, follow, showAll, ui.copyButton(() => view.fullOutput || '', 'Copy output')), outputNote, images);
  view.detailsSection = ui.section('Details', details);
  view.content = ui.el('div', { class: 'pg-stack' });
  parts.body.append(status, view.content);
  tick(root, () => {
    if (view.tool && view.tool.status === 'running') status.textContent = statusLine(view.tool, Date.now());
  });
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  const { ui } = ctx;
  const { session, tool } = toolOf(ctx);
  const showAllLines = ctx.route.params.get('all') === '1';
  const sig = session ? [tool, showAllLines] : null;
  if (view.sig && sig && view.sig[0] === sig[0] && view.sig[1] === sig[1]) return;
  view.sig = sig;
  view.tool = tool;
  if (!session) {
    view.parts.setTitle('Tool');
    view.status.textContent = '';
    view.content.replaceChildren(waiting(ctx, view.cache, 6));
    return;
  }
  if (!tool) {
    view.parts.setTitle('Tool');
    view.status.textContent = '';
    view.content.replaceChildren(ui.empty({
      title: 'This tool call is not in this session.',
      body: 'It may belong to an older branch, or the link is wrong.',
      action: { label: 'See the turn', href: paneHref(ctx, { page: 'turn' }) },
    }));
    return;
  }
  view.parts.setTitle(tool.name || 'Tool');
  view.status.textContent = statusLine(tool, Date.now());
  view.argsBox.replaceChildren(...argsView(ui, tool.args));

  const output = tool.result || tool.partial;
  const text = outputText(output);
  view.fullOutput = text;
  const lines = text ? text.split('\n') : [];
  const cut = !showAllLines && lines.length > SHOWN_LINES;
  view.terminal.textContent = cut ? lines.slice(-SHOWN_LINES).join('\n') : text;
  view.terminal.dataset.empty = text ? 'false' : 'true';
  if (!text) view.terminal.textContent = tool.status === 'running' ? 'No output yet.' : 'No output.';
  if (cut) {
    view.showAll.hidden = false;
    view.showAll.textContent = `Show all ${ctx.fmt.num(lines.length)} lines`;
    const params = new URLSearchParams(ctx.route.params);
    params.set('all', '1');
    view.showAll.href = paneHref(ctx, { page: 'tool', rest: ctx.route.rest, params });
  } else {
    view.showAll.hidden = true;
  }
  const notes = [];
  if (tool.status === 'running') notes.push('Live. The output follows while you stay at the bottom.');
  if (tool.status === 'failed') notes.push('The tool reported a failure.');
  if (tool.status === 'stopped') notes.push('Stopped before it finished.');
  if (cut) notes.push(`Showing the last ${ctx.fmt.num(SHOWN_LINES)} lines.`);
  view.outputNote.textContent = notes.join(' ');
  view.follow.hidden = view.following || tool.status !== 'running';
  if (view.following) view.terminal.scrollTop = view.terminal.scrollHeight;

  view.images.replaceChildren(...imagesOf(output).map((block) => ui.el('img', {
    class: 'pg-image',
    src: `data:${block.mimeType || 'image/png'};base64,${block.data}`,
    alt: 'Image from the tool output',
    loading: 'lazy',
  })));

  const detailParts = detailsView(ui, output ? output.details : null);
  view.details.replaceChildren(...(detailParts || []));
  const sections = [view.argsSection, view.outputSection];
  if (detailParts && detailParts.length) sections.push(view.detailsSection);
  sections.push(ui.el('p', { class: 'pg-line small' },
    ui.el('a', { class: 'link target', href: ctx.href('events', { params: { text: tool.id } }), text: 'Find in Events →' })));
  if (view.content.children.length !== sections.length || [...view.content.children].some((child, index) => child !== sections[index])) {
    view.content.replaceChildren(...sections);
  }
}

export default definePage({
  id: 'tool',
  title(ctx) {
    const { tool } = toolOf(ctx);
    return tool ? `${tool.name} · Tool` : 'Tool';
  },
  render,
  update,
  dispose(root) {
    stopTick(root);
    views.delete(root);
  },
});
