// Streaming markdown → DOM (textContent only, never HTML). The text is cut
// into top-level blocks; on each update only blocks whose source changed
// (in practice the last one while streaming) are rebuilt.

import { el, copyButton } from './ui.js';

const FENCE = /^ {0,3}(`{3,}|~{3,})\s*([^`\s]*)/;
const HEADING = /^ {0,3}(#{1,6})\s+(.*?)\s*#*\s*$/;
const RULE = /^ {0,3}([-*_])(\s*\1){2,}\s*$/;
const QUOTE = /^ {0,3}>\s?/;
const ITEM = /^(\s*)([-*+]|\d{1,9}[.)])\s+(.*)$/;
const TABLE_RULE = /^\s*\|?\s*:?-{1,}:?\s*(\|\s*:?-{1,}:?\s*)*\|?\s*$/;

function isTableStart(lines, index) {
  return lines[index].includes('|') && index + 1 < lines.length && TABLE_RULE.test(lines[index + 1]) && lines[index + 1].includes('-');
}

function startsBlock(lines, index) {
  const line = lines[index];
  return FENCE.test(line) || HEADING.test(line) || RULE.test(line) || QUOTE.test(line) || ITEM.test(line) || isTableStart(lines, index);
}

/** Split `text` into `{ kind, source, lines }` blocks. */
export function splitBlocks(text) {
  const lines = text.replace(/\r\n?/g, '\n').split('\n');
  const blocks = [];
  let index = 0;
  while (index < lines.length) {
    const line = lines[index];
    if (!line.trim()) {
      index += 1;
      continue;
    }
    const start = index;
    let kind;
    const fence = FENCE.exec(line);
    if (fence) {
      kind = 'fence';
      index += 1;
      const close = new RegExp(`^ {0,3}${fence[1][0]}{${fence[1].length},}\\s*$`);
      while (index < lines.length && !close.test(lines[index])) index += 1;
      if (index < lines.length) index += 1;
    } else if (HEADING.test(line)) {
      kind = 'heading';
      index += 1;
    } else if (RULE.test(line)) {
      kind = 'rule';
      index += 1;
    } else if (QUOTE.test(line)) {
      kind = 'quote';
      while (index < lines.length && lines[index].trim() && (QUOTE.test(lines[index]) || !startsBlock(lines, index))) index += 1;
    } else if (ITEM.test(line)) {
      kind = 'list';
      index += 1;
      while (index < lines.length) {
        const next = lines[index];
        if (next.trim()) {
          if (ITEM.test(next) || /^\s+\S/.test(next) || !startsBlock(lines, index)) {
            index += 1;
            continue;
          }
          break;
        }
        const after = lines[index + 1];
        if (after !== undefined && (ITEM.test(after) || /^\s{2,}\S/.test(after))) {
          index += 1;
          continue;
        }
        break;
      }
    } else if (isTableStart(lines, index)) {
      kind = 'table';
      index += 2;
      while (index < lines.length && lines[index].includes('|') && lines[index].trim()) index += 1;
    } else {
      kind = 'paragraph';
      index += 1;
      while (index < lines.length && lines[index].trim() && !startsBlock(lines, index)) index += 1;
    }
    const blockLines = lines.slice(start, index);
    blocks.push({ kind, lines: blockLines, source: blockLines.join('\n') });
  }
  return blocks;
}

const INLINE = /(`+)([\s\S]*?[^`])\1(?!`)|\*\*([^*]+?)\*\*|__([^_]+?)__|~~([^~]+?)~~|\*([^*\s][^*]*?)\*|(?<![\w])_([^_\s][^_]*?)_(?![\w])|\[([^\]]+)\]\(([^)\s]+)(?:\s+"[^"]*")?\)|<(https?:\/\/[^>\s]+)>|(https?:\/\/[^\s<>()]+[^\s<>().,;:!?'"])/g;

function safeHref(url) {
  return /^(https?:|mailto:)/i.test(url) ? url : null;
}

function link(text, url) {
  const href = safeHref(url);
  if (!href) return document.createTextNode(text);
  return el('a', { href, target: '_blank', rel: 'noopener noreferrer', text });
}

/** Inline markdown into `parent`. */
export function inline(text, parent) {
  let last = 0;
  for (const match of text.matchAll(INLINE)) {
    if (match.index > last) parent.append(text.slice(last, match.index));
    if (match[1]) parent.append(el('code', { translate: 'no', text: match[2].replace(/^ (.*) $/, '$1') }));
    else if (match[3] || match[4]) inline(match[3] || match[4], parent.appendChild(el('strong')));
    else if (match[5]) inline(match[5], parent.appendChild(el('del')));
    else if (match[6] || match[7]) inline(match[6] || match[7], parent.appendChild(el('em')));
    else if (match[8]) {
      const node = link('', match[9]);
      if (node.nodeType === Node.TEXT_NODE) parent.append(match[8]);
      else {
        inline(match[8], node);
        parent.append(node);
      }
    } else parent.append(link(match[10] || match[11], match[10] || match[11]));
    last = match.index + match[0].length;
  }
  if (last < text.length) parent.append(text.slice(last));
}

function inlineLines(lines, parent) {
  lines.forEach((line, index) => {
    if (index > 0) parent.append(el('br'));
    inline(line, parent);
  });
  return parent;
}

function renderFence(block) {
  const open = FENCE.exec(block.lines[0]);
  const marker = open[1];
  const language = open[2] || '';
  let body = block.lines.slice(1);
  const closed = body.length && new RegExp(`^ {0,3}${marker[0]}{${marker.length},}\\s*$`).test(body[body.length - 1]);
  if (closed) body = body.slice(0, -1);
  const code = el('code', { translate: 'no', text: body.join('\n') });
  const pre = el('pre', { tabindex: '0' }, code);
  const header = el('div', { class: 'code-head' }, el('span', { class: 'code-lang', text: language || 'text' }), copyButton(() => code.textContent));
  return el('div', { class: 'code', 'data-open': closed ? null : 'true' }, header, el('div', { class: 'code-scroll' }, pre));
}

function renderHeading(block) {
  const match = HEADING.exec(block.lines[0]);
  const level = Math.min(match[1].length + 2, 6);
  return inlineLines([match[2]], el(`h${level}`, { class: 'md-heading' }));
}

function parseItems(lines) {
  const root = { indent: -1, children: [], ordered: false };
  const stack = [root];
  let lastItem = null;
  for (const line of lines) {
    const match = ITEM.exec(line);
    if (match) {
      const indent = match[1].replace(/\t/g, '    ').length;
      while (stack.length > 1 && indent <= stack[stack.length - 1].indent) stack.pop();
      let parent = stack[stack.length - 1];
      const ordered = /\d/.test(match[2]);
      if (lastItem && indent > lastItem.indent) {
        parent = { indent, children: [], ordered };
        lastItem.sub = parent;
        stack.push(parent);
      } else if (parent === root && root.children.length === 0) {
        root.ordered = ordered;
        root.start = ordered ? parseInt(match[2], 10) : null;
      }
      let text = match[3];
      let task = null;
      const taskMatch = /^\[( |x|X)\]\s+(.*)$/.exec(text);
      if (taskMatch) {
        task = taskMatch[1] !== ' ';
        text = taskMatch[2];
      }
      lastItem = { indent, lines: [text], task, sub: null };
      parent.children.push(lastItem);
    } else if (lastItem && line.trim()) {
      lastItem.lines.push(line.trim());
    }
  }
  return root;
}

function renderList(list) {
  const node = el(list.ordered ? 'ol' : 'ul', { class: 'md-list', start: list.ordered && list.start && list.start !== 1 ? String(list.start) : null });
  for (const item of list.children) {
    const li = el('li', { class: item.task === null ? null : 'task' });
    if (item.task !== null) {
      li.append(el('span', { class: 'task-box', role: 'img', 'aria-label': item.task ? 'Done' : 'Not done', text: item.task ? '☑' : '☐' }), ' ');
    }
    inlineLines(item.lines, li);
    if (item.sub) li.append(renderList(item.sub));
    node.append(li);
  }
  return node;
}

function cells(line) {
  let row = line.trim();
  if (row.startsWith('|')) row = row.slice(1);
  if (row.endsWith('|') && !row.endsWith('\\|')) row = row.slice(0, -1);
  return row.split(/(?<!\\)\|/).map((cell) => cell.trim().replace(/\\\|/g, '|'));
}

function renderTable(block) {
  const head = cells(block.lines[0]);
  const aligns = cells(block.lines[1]).map((spec) => (spec.endsWith(':') ? (spec.startsWith(':') ? 'center' : 'right') : spec.startsWith(':') ? 'left' : null));
  const table = el('table', { class: 'md-table' });
  const headRow = el('tr');
  head.forEach((text, index) => headRow.append(inlineLines([text], el('th', { scope: 'col', 'data-align': aligns[index] })) ));
  table.append(el('thead', null, headRow));
  const body = el('tbody');
  for (const line of block.lines.slice(2)) {
    const row = el('tr');
    cells(line).forEach((text, index) => row.append(inlineLines([text], el('td', { 'data-align': aligns[index] || null }))));
    body.append(row);
  }
  table.append(body);
  return el('div', { class: 'table-scroll', tabindex: '0' }, table);
}

function renderBlock(block) {
  switch (block.kind) {
    case 'fence':
      return renderFence(block);
    case 'heading':
      return renderHeading(block);
    case 'rule':
      return el('hr');
    case 'quote': {
      const quote = el('blockquote');
      for (const inner of splitBlocks(block.lines.map((line) => line.replace(QUOTE, '')).join('\n'))) quote.append(renderBlock(inner));
      return quote;
    }
    case 'list':
      return renderList(parseItems(block.lines));
    case 'table':
      return renderTable(block);
    case 'paragraph':
      return inlineLines(block.lines, el('p'));
    default:
      return inlineLines(block.lines, el('p'));
  }
}

/**
 * A renderer bound to `container`. `update(text)` re-renders only the
 * blocks that changed since the last call.
 */
export function createRenderer(container) {
  let rendered = [];
  return {
    update(text) {
      const blocks = splitBlocks(text);
      let same = 0;
      while (same < blocks.length && same < rendered.length && blocks[same].source === rendered[same].source) same += 1;
      for (const stale of rendered.slice(same)) stale.node.remove();
      rendered = rendered.slice(0, same);
      for (const block of blocks.slice(same)) {
        const node = renderBlock(block);
        container.append(node);
        rendered.push({ source: block.source, node });
      }
    },
  };
}

/** A one-shot render of settled text. */
export function markdown(text) {
  const node = el('div', { class: 'md' });
  createRenderer(node).update(text);
  return node;
}
