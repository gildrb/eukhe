// The top bar (56px): on phones and tablets the Open chats and New chat
// buttons; the chat title as a button opening the Chat menu; the
// connection state only when not connected ("Reconnecting", or "Offline"
// with Retry) in a fixed slot that never changes the bar's height.

import { el, icon, iconButton, textButton, openMenu, menuItem, statusLine, input, button } from './ui.js';
import { renameChat, forkChat, exportChat, compactChat, confirmDelete } from './actions.js';
import { reconnect } from './link.js';

/** The Chat menu: Rename…, Fork, Export, Compact context, Delete…. */
function openChatMenu(anchor, app) {
  openMenu({
    anchor,
    label: 'Chat',
    className: 'chat-menu',
    build: (panel, close) => {
      const status = statusLine();
      const items = el('div', { class: 'menu-items', role: 'menu', 'aria-label': 'Chat' });
      let busy = false;
      const act = (label, work, doneWord) => menuItem(label, async (event) => {
        if (busy) return;
        busy = true;
        const node = event.currentTarget;
        node.setAttribute('aria-busy', 'true');
        status.say(doneWord);
        try {
          const text = await work();
          status.say(text);
        } catch (error) {
          status.say(error.message, { error: true });
        } finally {
          busy = false;
          node.removeAttribute('aria-busy');
        }
      });
      const rename = menuItem('Rename…', () => showRename());
      const del = menuItem('Delete…', async () => {
        await close();
        await confirmDelete({ id: app.sessionId(), title: app.title() });
      }, { kind: 'danger' });
      items.append(
        rename,
        menuItem('Fork', async () => {
          await close();
          try {
            await forkChat();
          } catch (error) {
            app.notice(`Not forked. ${error.message}`);
          }
        }),
        act('Export as HTML', () => exportChat('html'), 'Exporting'),
        act('Export as JSONL', () => exportChat('jsonl'), 'Exporting'),
        act('Compact context', () => compactChat(), 'Compacting'),
        el('div', { class: 'menu-rule', role: 'separator' }),
        del,
      );
      panel.append(items, status);

      function showRename() {
        const field = input({ value: app.title(), name: 'chat-name', label: 'Chat name' });
        field.setAttribute('data-autofocus', '');
        const note = statusLine();
        const save = async () => {
          try {
            await renameChat(app.sessionId(), field.value);
            close();
          } catch (error) {
            note.say(error.message, { error: true });
          }
        };
        field.addEventListener('keydown', (event) => {
          if (event.key === 'Enter' && !event.isComposing) {
            event.preventDefault();
            save();
          }
        });
        const form = el('div', { class: 'menu-rename' },
          el('label', { class: 'control-label', for: field.id || '', text: 'Name' }),
          field,
          note,
          el('div', { class: 'menu-actions' }, button('Cancel', () => {
            form.replaceWith(items, status);
            rename.focus();
            panel.place();
          }), button('Save', save, { kind: 'primary' })));
        field.id = 'chat-name-field';
        form.querySelector('label').setAttribute('for', field.id);
        items.remove();
        status.remove();
        panel.append(form);
        panel.place();
        requestAnimationFrame(() => {
          field.focus();
          field.select();
        });
      }
    },
  });
}

/** `createTopbar(app)` → `{ node, update(state) }`. */
export function createTopbar(app) {
  const menu = iconButton('Open chats', 'menu', () => app.openDrawer(), { className: 'topbar-menu' });
  const fresh = iconButton('New chat', 'newChat', () => app.newChat(), { className: 'topbar-new' });
  const titleText = el('span', { class: 'title-text', text: '' });
  const title = el('button', { type: 'button', class: 'title-button', 'aria-haspopup': 'dialog', 'aria-expanded': 'false' }, titleText, icon('chevron'));
  title.addEventListener('click', () => openChatMenu(title, app));
  const connWord = el('span', { class: 'conn-word' });
  const retry = textButton('Retry', () => reconnect(), { className: 'conn-retry' });
  const conn = el('div', { class: 'conn', role: 'status', 'aria-live': 'polite' }, connWord, retry);
  const node = el('header', { class: 'topbar' }, menu, el('div', { class: 'topbar-title' }, title), conn, fresh);

  let lastTitle = null;
  let lastConn = null;
  return {
    node,
    update(state) {
      const text = state.session ? state.session.title : state.link.status === 'open' ? '' : 'eukhe';
      if (text !== lastTitle) {
        lastTitle = text;
        titleText.textContent = text;
      }
      title.disabled = !state.session;
      const { status, everOpen } = state.link;
      let word = '';
      if (status === 'offline' || status === 'unavailable') word = 'Offline';
      else if (status === 'connecting' && everOpen) word = 'Reconnecting';
      else if (status === 'connecting' || state.link.catchingUp) word = everOpen ? 'Reconnecting' : 'Connecting';
      if (word !== lastConn) {
        lastConn = word;
        connWord.textContent = word;
        connWord.classList.toggle('shimmer', word === 'Reconnecting' || word === 'Connecting');
        retry.hidden = word !== 'Offline';
        conn.hidden = !word;
      }
    },
  };
}
