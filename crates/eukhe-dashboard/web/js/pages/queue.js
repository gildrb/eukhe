// Queue (`#/s/<id>/queue`): the steer and follow-up lanes with edit,
// move, delete (Undo), send now and clear, plus the pending shell
// approvals. Edits carry `expectedText`, so a stale view never misapplies.
// `?edit=<lane>:<index>` opens an item's sheet (Back closes it).

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { effectWords } from '../turn.js';
import { answerApproval } from '../approvals.js';
import { actionButton, backToChat, boundSession, failed, frame, keyed, paneHref, place, waiting } from './kit.js';

const UNDO_MS = 5000;

/** Wire lane names (`mutate_queued_message`) and their words. */
const LANES = [
  { id: 'steering', key: 'steering', title: 'Steer', other: 'followUp', hint: 'Delivered at the next turn boundary.' },
  { id: 'followUp', key: 'followUps', title: 'Next', other: 'steering', hint: 'Sent when the current work ends.' },
];

const views = new WeakMap();

function laneOf(id) {
  return LANES.find((lane) => lane.id === id);
}

function originWords(origin) {
  if (!origin || !origin.kind) return '';
  switch (origin.kind) {
    case 'user':
      return '';
    case 'goal':
      return 'from the goal';
    case 'autonomous':
      return 'autonomous';
    case 'director':
      return 'from the director';
    case 'quotaResume':
      return 'quota resume';
    case 'report':
      return origin.report && origin.report.report ? `report · ${origin.report.report}` : 'report';
    default:
      return origin.kind;
  }
}

function isUserItem(item) {
  return !item.origin || item.origin.kind === 'user';
}

function editHref(ctx, lane, index) {
  const params = new URLSearchParams(ctx.route.params);
  if (lane === null) params.delete('edit');
  else params.set('edit', `${lane}:${index}`);
  return paneHref(ctx, { page: 'queue', params });
}

/** Run one queue mutation; a `rejected` status means the queue moved on. */
async function mutate(ctx, lane, index, expectedText, mutation) {
  const reply = await ctx.run({ type: 'mutate_queued_message', lane, index, expectedText, mutation });
  if (reply && reply.status === 'rejected') {
    ctx.ui.toast({ text: 'The queue changed. Showing the latest.' });
    return false;
  }
  return true;
}

/** Delete an item after a 5 s Undo; the index is found again by text at that point. */
function deleteWithUndo(ctx, view, lane, text) {
  const key = `${lane}\u0000${text}`;
  view.hidden.add(key);
  view.rerender();
  const note = ctx.ui.toast({ text: 'Removed from the queue.', undo: UNDO_MS });
  note.undone.then(async (undone) => {
    view.hidden.delete(key);
    if (undone) {
      view.rerender();
      return;
    }
    const session = store.get().session;
    const items = session ? session.queue[laneOf(lane).key] : [];
    const index = items.findIndex((item) => item.text === text);
    try {
      if (index >= 0) await mutate(ctx, lane, index, text, { type: 'delete' });
    } catch (error) {
      failed(error, 'Not removed');
    } finally {
      view.rerender();
    }
  });
}

function editSheet(ctx, view, laneId, index, item) {
  const { ui } = ctx;
  const lane = laneOf(laneId);
  const other = laneOf(lane.other);
  const text = ui.el('textarea', {
    class: 'pg-textarea',
    rows: '4',
    name: 'queued-text',
    'aria-label': 'Queued message',
    autocapitalize: 'sentences',
    spellcheck: 'true',
  });
  text.value = item.text;
  let handle = null;
  const done = async (work) => {
    try {
      await work();
      handle.close();
    } catch (error) {
      failed(error);
    }
  };
  const actions = [
    actionButton({ label: 'Save', busyLabel: 'Saving', kind: 'primary', work: () => done(() => mutate(ctx, laneId, index, item.text, { type: 'replace', text: text.value })) }),
    actionButton({ label: `Move to ${other.title}`, busyLabel: 'Moving', work: () => done(() => mutate(ctx, laneId, index, item.text, { type: 'replace', text: text.value, lane: other.id })) }),
    actionButton({ label: 'Move up', busyLabel: 'Moving', work: () => done(() => mutate(ctx, laneId, index, item.text, { type: 'move', direction: -1 })) }),
    actionButton({ label: 'Move down', busyLabel: 'Moving', work: () => done(() => mutate(ctx, laneId, index, item.text, { type: 'move', direction: 1 })) }),
    ui.button({ label: 'Delete', kind: 'danger', onClick: () => {
      handle.close();
      deleteWithUndo(ctx, view, laneId, item.text);
    } }),
  ];
  handle = ui.sheet({
    title: `${lane.title} · item ${index + 1}`,
    content: ui.el('div', { class: 'pg-stack' },
      text,
      ui.el('p', { class: 'pg-line small', text: lane.hint }),
      ui.el('div', { class: 'pg-actions' }, ...actions)),
    onClose: () => {
      view.sheet = null;
      if (view.ctx.route.params.get('edit') !== null) {
        view.ctx.navigate(editHref(view.ctx, null, 0), { replace: true });
      }
    },
  });
  return handle;
}

function itemRow(ctx, laneId, index, item) {
  const { ui } = ctx;
  const origin = originWords(item.origin);
  const editable = isUserItem(item);
  const body = ui.el('span', { class: 'pg-queue-text', text: item.text });
  const node = editable
    ? ui.el('a', { class: 'pg-queue-item', href: editHref(ctx, laneId, index) }, body, ui.el('span', { class: 'pg-queue-act', text: 'Edit' }))
    : ui.el('div', { class: 'pg-queue-item', 'data-internal': 'true' }, body, ui.el('span', { class: 'pg-queue-act', text: origin }));
  return ui.el('li', {}, node);
}

function laneSection(ctx, view, session, lane) {
  const { ui } = ctx;
  const items = session.queue[lane.key] || [];
  const list = ui.el('ol', { class: 'pg-queue' });
  items.forEach((item, index) => {
    if (view.hidden.has(`${lane.id}\u0000${item.text}`)) return;
    list.append(itemRow(ctx, lane.id, index, item));
  });
  const body = list.children.length ? list : ui.el('p', { class: 'pg-line small', text: 'Empty.' });
  return ui.section(`${lane.title} · ${items.length}`, ui.el('p', { class: 'pg-line small', text: lane.hint }), body);
}

function approvalsSection(ctx, approvals) {
  const { ui } = ctx;
  if (!approvals.length) return null;
  const cards = approvals.map((approval, index) => ui.el('div', { class: 'pg-approval', role: 'group', 'aria-label': 'Needs approval' },
    ui.el('p', { class: 'pg-approval-head', text: `Needs approval${approvals.length > 1 ? ` · ${index + 1} of ${approvals.length}` : ''}${approval.step ? ` · step ${approval.step}` : ''}` }),
    ui.el('pre', { class: 'pg-approval-command mono', translate: 'no', text: approval.command }),
    ui.el('p', { class: 'pg-approval-effect', text: effectWords(approval.effect) }),
    ui.el('div', { class: 'pg-approval-actions' },
      approval.status === 'elsewhere'
        ? ui.el('p', { class: 'pg-line', text: 'Answered elsewhere.' })
        : [
          ui.button({ label: 'Deny', busy: approval.status === 'answering', onClick: () => answerApproval(approval.requestId, 'deny') }),
          ui.button({ label: 'Approve', kind: 'primary', busy: approval.status === 'answering', onClick: () => answerApproval(approval.requestId, 'approve') }),
        ])));
  return ui.section('Needs you', ...cards);
}

function laneActions(ctx, session) {
  const { ui } = ctx;
  const { steering, followUps } = session.queue;
  const nodes = [];
  if (session.turn.running && steering.length) {
    nodes.push(actionButton({ label: 'Stop & steer now', busyLabel: 'Stopping', work: () => ctx.run({ type: 'abort_and_send_queued' }) }));
  }
  if (steering.length || followUps.length) {
    nodes.push(ui.button({ label: 'Clear queue', kind: 'danger', onClick: async () => {
      const yes = await ui.confirm({
        title: 'Clear the queue?',
        body: `${steering.length + followUps.length} queued messages will be dropped. They cannot be restored.`,
        action: 'Clear queue',
      });
      if (!yes) return;
      try {
        const dropped = await ctx.run({ type: 'clear_queue' });
        const count = dropped ? dropped.steering.length + dropped.followUp.length : 0;
        ui.toast({ text: `Cleared ${count} queued ${count === 1 ? 'message' : 'messages'}.` });
      } catch (error) {
        failed(error, 'Not cleared');
      }
    } }));
  }
  if (session.turn.running && (steering.length || followUps.length)) {
    nodes.push(ui.button({ label: 'Stop & clear', kind: 'danger', onClick: async () => {
      const yes = await ui.confirm({
        title: 'Stop and clear the queue?',
        body: 'The running turn stops and every queued message is dropped.',
        action: 'Stop & clear',
      });
      if (!yes) return;
      try {
        await ctx.run({ type: 'abort_and_clear_queue' });
      } catch (error) {
        failed(error, 'Not stopped');
      }
    } }));
  }
  return nodes;
}

function syncSheet(ctx, view, session) {
  const edit = ctx.route.params.get('edit');
  if (!edit) {
    if (view.sheet) {
      const { handle } = view.sheet;
      view.sheet = null;
      handle.close();
    }
    return;
  }
  const [laneId, rawIndex] = edit.split(':');
  const lane = laneOf(laneId);
  const index = Number(rawIndex);
  const item = lane && Number.isInteger(index) ? (session.queue[lane.key] || [])[index] : null;
  if (view.sheet && view.sheet.edit === edit) {
    if (!item || item.text !== view.sheet.text) {
      const { handle } = view.sheet;
      view.sheet = null;
      handle.close();
      ctx.ui.toast({ text: 'That item already left the queue.' });
    }
    return;
  }
  if (view.sheet) view.sheet.handle.close();
  view.sheet = null;
  if (!item || !isUserItem(item)) {
    ctx.navigate(editHref(ctx, null, 0), { replace: true });
    if (!item) ctx.ui.toast({ text: 'That item already left the queue.' });
    return;
  }
  view.sheet = { edit, text: item.text, handle: editSheet(ctx, view, laneId, index, item) };
}

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Queue', back: backToChat(ctx) });
  const view = { parts, cache: new Map(), hidden: new Set(), sheet: null, ctx, version: 0 };
  view.rerender = () => {
    view.version += 1;
    update(root, { ...view.ctx, state: store.get() });
  };
  views.set(root, view);
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui, state } = ctx;
  const session = boundSession(ctx);
  if (!session) {
    place(view.parts.body, [waiting(ctx, view.cache, 6)]);
    return;
  }
  const { queue } = session;
  const count = queue.steering.length + queue.followUps.length;
  view.parts.setTitle(count ? `Queue · ${count}` : 'Queue');
  const approvalsNode = keyed(view.cache, 'approvals', [state.approvals], () => approvalsSection(ctx, state.approvals));
  const actions = keyed(view.cache, 'actions', [queue, session.turn.running], () => laneActions(ctx, session));
  if (view.actions !== actions) {
    view.actions = actions;
    view.parts.setActions(...actions);
  }
  const lanesNode = keyed(view.cache, 'lanes', [queue, view.version, ctx.route.params.toString()], () => {
    if (!count) {
      return ui.empty({
        title: 'Nothing queued.',
        body: session.turn.running ? 'While a turn runs, Steer and Queue in the chat add messages here.' : 'Messages wait here while a turn runs.',
        action: { label: 'Go to the chat', href: ctx.href('chat', { sessionId: session.id }) },
      });
    }
    return ui.el('div', { class: 'pg-stack' }, ...LANES.map((lane) => laneSection(ctx, view, session, lane)));
  });
  place(view.parts.body, [approvalsNode, lanesNode]);
  syncSheet(ctx, view, session);
}

export default definePage({
  id: 'queue',
  title(ctx) {
    const session = boundSession(ctx);
    const count = session ? session.queue.steering.length + session.queue.followUps.length : 0;
    return count ? `Queue · ${count}` : 'Queue';
  },
  render,
  update,
  dispose(root) {
    const view = views.get(root);
    if (view && view.sheet) view.sheet.handle.close();
    views.delete(root);
  },
});
