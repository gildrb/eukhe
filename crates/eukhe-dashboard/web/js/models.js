// The Model menu (a popover above the model button; a bottom sheet on
// phones) and the model controls Settings shares: available models with
// the current one checked, Thinking level, Service tier, "All models"
// (the catalog, loaded on demand). Changes apply at once and roll back
// with the error shown inline.

import { store } from './store.js';
import { el, icon, segmented, select, statusLine, labelled, openMenu, textButton } from './ui.js';
import { listModels, modelKey, setModel, setAndReload, SERVICE_TIERS, levelWord } from './actions.js';

/** A list of model rows (name primary, provider tertiary, the current one checked). */
function modelList(status, { all = false } = {}) {
  const host = el('div', { class: 'model-list', role: 'listbox', 'aria-label': 'Models' });
  const more = textButton('All models →', () => load(true), { className: 'model-all' });
  const paint = (models) => {
    const session = store.get().session;
    const currentKey = session ? modelKey(session.state.model) : '';
    const rows = models.map((model) => {
      const key = modelKey(model);
      const isCurrent = key === currentKey;
      const row = el('button', { type: 'button', class: 'model-row', role: 'option', 'aria-selected': isCurrent ? 'true' : 'false' },
        el('span', { class: 'model-row-name', text: model.name || model.id }),
        el('span', { class: 'model-row-provider', translate: 'no', text: model.provider }),
        el('span', { class: 'model-row-check' }, isCurrent ? icon('check') : null));
      row.addEventListener('click', async () => {
        if (isCurrent) return;
        status.say('Switching');
        try {
          await setModel(model);
          status.say(`Now using ${model.name || model.id}.`);
          paint(models);
        } catch (error) {
          status.say(`Not switched. ${error.message}`, { error: true });
        }
      });
      return row;
    });
    host.replaceChildren(...rows);
    if (!models.length) host.append(el('p', { class: 'model-empty', text: 'No models are available.' }));
  };
  const load = async (catalog) => {
    more.hidden = true;
    try {
      paint(await listModels(catalog));
      more.hidden = catalog;
    } catch (error) {
      status.say(`Models did not load. ${error.message}`, { error: true });
      more.hidden = catalog;
    }
  };
  load(all);
  return { host, more };
}

/** The Thinking level control (segmented up to 5 levels, else a select). */
export function thinkingControl(status) {
  const state = store.get().session.state;
  const levels = state.availableThinkingLevels && state.availableThinkingLevels.length ? state.availableThinkingLevels : ['off'];
  const options = levels.map((level) => ({ value: level, label: levelWord(level) }));
  const onPick = (level) => setAndReload({ type: 'set_thinking_level', level });
  const onError = (error) => status.say(`Not changed. ${error.message}`, { error: true });
  const control = levels.length <= 5
    ? segmented({ label: 'Thinking', options, value: state.thinkingLevel, onPick, onError })
    : select({ label: 'Thinking', options, value: state.thinkingLevel, onPick, onError });
  return labelled('Thinking', control);
}

/** The Service tier select. */
export function tierControl(status) {
  const session = store.get().session;
  const value = session.state.serviceTier || session.serviceTier || 'default';
  const control = select({
    label: 'Service tier',
    options: SERVICE_TIERS,
    value,
    onPick: async (serviceTier) => {
      await setAndReload({ type: 'set_service_tier', serviceTier });
      // The daemon answers success but keeps its tier when the model has no such tier.
      const kept = store.get().session && store.get().session.state.serviceTier;
      if (kept && kept !== serviceTier) {
        const word = (SERVICE_TIERS.find((tier) => tier.value === kept) || { label: kept }).label;
        throw new Error(`eukhe kept ${word}: this model has no ${serviceTier} tier.`);
      }
    },
    onError: (error) => status.say(`Not changed. ${error.message}`, { error: true }),
  });
  return labelled('Service tier', control);
}

/** The model controls as a block (Settings → Model and the Model menu). */
export function modelControls() {
  const status = statusLine();
  const list = modelList(status);
  const node = el('div', { class: 'model-controls' },
    list.host,
    list.more,
    thinkingControl(status),
    tierControl(status),
    status);
  return node;
}

/** Open the Model menu above the composer box, aligned with `anchor`. */
export function openModelMenu(anchor) {
  if (!store.get().session) return;
  openMenu({
    anchor,
    above: anchor.closest('.composer'),
    label: 'Model',
    placement: 'above',
    className: 'model-menu',
    build: (panel) => {
      panel.append(modelControls());
    },
  });
}
