// Model (`#/s/<id>/model?q=&provider=&all=1`): the current model with its
// thinking level and service tier, the scoped models (the cycle list), and
// the catalog (GetAvailableModels + GetModelCatalog) to switch or scope.

import { definePage } from '../pages.js';
import { store } from '../store.js';
import { backToChat, boundSession, failed, frame, keyed, modelName, paneHref, place, reloadState, replaceSoon, segmented, stats, waiting } from './kit.js';

const SERVICE_TIERS = [
  { value: 'auto', label: 'Auto' },
  { value: 'default', label: 'Default' },
  { value: 'flex', label: 'Flex' },
  { value: 'scale', label: 'Scale' },
  { value: 'priority', label: 'Priority' },
];

const views = new WeakMap();

function modelKey(model) {
  return model ? `${model.provider}/${model.id || model.modelId}` : '';
}

/**
 * The usable models (`get_available_models`); the full catalog
 * (`get_model_catalog`, often hundreds of KB) only when `?all=1` asks for it.
 */
function load(ctx, view, { withCatalog }) {
  const byName = (a, b) => `${a.provider}/${a.id}`.localeCompare(`${b.provider}/${b.id}`);
  view.models = Promise.all([
    ctx.run({ type: 'get_available_models' }),
    withCatalog ? ctx.run({ type: 'get_model_catalog' }) : null,
  ]).then(([available, catalog]) => ({
    available: new Set((available.models || []).map(modelKey)),
    models: [...((catalog || available).models || [])].sort(byName),
    withCatalog,
  }));
  view.models.catch(() => {});
  return view.models;
}

function scopedKeys(state) {
  return new Set((state.scopedModels || []).map((entry) => modelKey(entry && entry.model)));
}

async function setScoped(ctx, entries) {
  await ctx.run({ type: 'set_scoped_models', scopedModels: entries });
  await reloadState(ctx);
}

async function switchModel(ctx, model) {
  await ctx.run({ type: 'set_model', provider: model.provider, modelId: model.id });
  await reloadState(ctx);
  ctx.ui.toast({ text: `Now using ${model.name || model.id}.` });
}

function figures(fmt, model) {
  const parts = [];
  if (model.contextWindow) parts.push(`${fmt.tokens(model.contextWindow, { unit: false })} ctx`);
  if (model.cost && (model.cost.input || model.cost.output)) parts.push(`${fmt.cost(model.cost.input)} / ${fmt.cost(model.cost.output)} per M`);
  if (model.reasoning) parts.push('reasons');
  if (Array.isArray(model.input) && model.input.includes('image')) parts.push('images');
  return parts.join(' · ');
}

function currentSection(ctx, session) {
  const { ui, fmt } = ctx;
  const { state } = session;
  const model = state.model && typeof state.model === 'object' ? state.model : null;
  const levels = state.availableThinkingLevels && state.availableThinkingLevels.length ? state.availableThinkingLevels : ['off'];
  return ui.section('Current',
    ui.el('p', { class: 'pg-lead' }, ui.el('span', { text: modelName(state.model) }),
      model ? ui.el('span', { class: 'pg-lead-detail mono', translate: 'no', text: ` ${modelKey(model)}` }) : null),
    model ? stats([
      ['Context', model.contextWindow ? fmt.tokens(model.contextWindow) : null],
      ['Max output', model.maxTokens ? fmt.tokens(model.maxTokens) : null],
      ['Input', model.cost ? `${fmt.cost(model.cost.input)} per M` : null],
      ['Output', model.cost ? `${fmt.cost(model.cost.output)} per M` : null],
      ['Cache read', model.cost ? `${fmt.cost(model.cost.cacheRead)} per M` : null],
    ]) : null,
    segmented({
      label: 'Thinking',
      options: levels,
      value: state.thinkingLevel,
      onPick: async (level) => {
        await ctx.run({ type: 'set_thinking_level', level });
        await reloadState(ctx);
      },
    }),
    segmented({
      label: 'Service tier',
      options: SERVICE_TIERS,
      value: session.serviceTier || state.serviceTier,
      onPick: (serviceTier) => ctx.run({ type: 'set_service_tier', serviceTier }),
    }),
    ui.el('div', { class: 'pg-actions' },
      ui.button({ label: 'Previous model', onClick: () => ctx.run({ type: 'cycle_model', direction: 'backward' }).then(() => reloadState(ctx)).catch((error) => failed(error)) }),
      ui.button({ label: 'Next model', onClick: () => ctx.run({ type: 'cycle_model', direction: 'forward' }).then(() => reloadState(ctx)).catch((error) => failed(error)) })),
    ui.el('p', { class: 'pg-line small', text: 'Previous and Next step through the scoped models below, or all models when none are scoped.' }));
}

function scopedSection(ctx, session) {
  const { ui } = ctx;
  const entries = session.state.scopedModels || [];
  if (!entries.length) {
    return ui.section('Scoped models', ui.el('p', { class: 'pg-line small', text: 'None. Scope models in the list below to cycle through just those.' }));
  }
  const list = ui.el('ol', { class: 'pg-list' });
  entries.forEach((entry, index) => {
    const model = entry && entry.model ? entry.model : {};
    list.append(ui.el('li', {}, ui.row({
      title: model.name || model.id || 'model',
      detail: [modelKey(model), entry.thinkingLevel].filter(Boolean).join(' · '),
      trail: ui.button({ label: 'Remove', onClick: () => setScoped(ctx, entries.filter((_, other) => other !== index)).catch((error) => failed(error, 'Not removed')) }),
    })));
  });
  return ui.section(`Scoped models · ${entries.length}`, list,
    ui.el('div', { class: 'pg-actions' }, ui.button({ label: 'Clear scope', onClick: () => setScoped(ctx, []).catch((error) => failed(error)) })));
}

function catalogRow(ctx, session, model, data, scoped) {
  const { ui, fmt } = ctx;
  const key = modelKey(model);
  const usable = data.available.has(key);
  const isCurrent = key === modelKey(session.state.model);
  const inScope = scoped.has(key);
  const pick = ui.el('button', {
    type: 'button',
    class: 'pg-model-pick',
    'aria-current': isCurrent ? 'true' : null,
    disabled: !usable || isCurrent,
  },
  ui.el('span', { class: 'pg-model-name', text: model.name || model.id }),
  ui.el('span', { class: 'pg-model-id mono', translate: 'no', text: model.id }),
  ui.el('span', { class: 'pg-model-figures fig', text: figures(fmt, model) }),
  ui.el('span', { class: 'pg-model-state', text: isCurrent ? 'Current' : usable ? '' : 'Sign in needed' }));
  pick.addEventListener('click', async () => {
    const label = pick.querySelector('.pg-model-state');
    pick.disabled = true;
    label.textContent = 'Switching…';
    try {
      await switchModel(ctx, model);
    } catch (error) {
      label.textContent = '';
      pick.disabled = false;
      failed(error, 'Model not switched');
    }
  });
  const scope = ui.button({
    label: inScope ? 'Unscope' : 'Scope',
    current: inScope,
    onClick: () => {
      const entries = session.state.scopedModels || [];
      const next = inScope
        ? entries.filter((entry) => modelKey(entry && entry.model) !== key)
        : [...entries, { model: { provider: model.provider, id: model.id } }];
      setScoped(ctx, next).catch((error) => failed(error, 'Scope not changed'));
    },
  });
  return ui.el('li', { class: 'pg-model', 'data-usable': usable ? 'true' : 'false' }, pick, usable ? scope : null);
}

function catalogSection(ctx, view, session, data) {
  const { ui, fmt } = ctx;
  const query = (ctx.route.params.get('q') || '').trim().toLowerCase();
  const provider = ctx.route.params.get('provider') || '';
  const all = ctx.route.params.get('all') === '1';
  const scoped = scopedKeys(session.state);
  const shown = data.models.filter((model) => {
    if (!all && !data.available.has(modelKey(model))) return false;
    if (provider && model.provider !== provider) return false;
    if (query && !`${model.name} ${model.id} ${model.provider}`.toLowerCase().includes(query)) return false;
    return true;
  });
  const groups = new Map();
  for (const model of shown) {
    if (!groups.has(model.provider)) groups.set(model.provider, []);
    groups.get(model.provider).push(model);
  }
  const blocks = [...groups].map(([name, models]) => ui.el('section', { class: 'pg-model-group' },
    ui.el('h3', { class: 'pg-subtitle', text: `${name} · ${fmt.num(models.length)}` }),
    ui.el('ol', { class: 'pg-models' }, ...models.map((model) => catalogRow(ctx, session, model, data, scoped)))));
  const allParams = new URLSearchParams(ctx.route.params);
  if (all) allParams.delete('all');
  else allParams.set('all', '1');
  const allLink = ui.el('a', {
    class: 'link target',
    href: paneHref(ctx, { page: 'model', params: allParams }),
    text: all ? 'Only models you can use' : 'Also show models that need a sign-in',
  });
  const empty = shown.length ? null : ui.empty({
    title: query ? `No models match “${query}”.` : 'No models to show.',
    action: { label: 'Clear filters', href: paneHref(ctx, { page: 'model' }) },
  });
  return ui.el('div', { class: 'pg-stack' }, ...blocks, empty, allLink);
}

function filters(ctx, view, providers) {
  const { ui } = ctx;
  const setParam = (key, value, { debounce }) => {
    const live = view.ctx;
    const params = new URLSearchParams(live.route.params);
    if (value) params.set(key, value);
    else params.delete(key);
    const target = paneHref(live, { page: 'model', params });
    if (debounce) replaceSoon(live, target);
    else live.navigate(target, { replace: true });
  };
  return ui.el('div', { class: 'pg-filters' },
    ui.field({
      label: 'Search models',
      value: ctx.route.params.get('q') || '',
      type: 'search',
      placeholder: 'Name or id…',
      name: 'model-search',
      onInput: (value) => setParam('q', value.trim(), { debounce: true }),
    }),
    ui.select({
      label: 'Provider',
      options: [{ value: '', label: 'All providers' }, ...providers.map((name) => ({ value: name, label: name }))],
      value: ctx.route.params.get('provider') || '',
      onChange: (value) => setParam('provider', value, { debounce: false }),
    }));
}

function render(root, ctx) {
  const parts = frame(root, ctx, { title: 'Model', back: backToChat(ctx) });
  const view = { parts, cache: new Map(), ctx, models: null, data: null, error: null, boundTo: null, version: 0 };
  views.set(root, view);
  update(root, ctx);
}

function update(root, ctx) {
  const view = views.get(root);
  if (!view) return;
  view.ctx = ctx;
  const { ui } = ctx;
  const session = boundSession(ctx);
  if (!session) {
    place(view.parts.body, [waiting(ctx, view.cache, 10)]);
    return;
  }
  const wantCatalog = ctx.route.params.get('all') === '1';
  if (view.boundTo !== session.id || (wantCatalog && view.data && !view.data.withCatalog)) {
    view.boundTo = session.id;
    view.data = null;
    view.error = null;
    load(ctx, view, { withCatalog: wantCatalog }).then((data) => {
      view.data = data;
      view.version += 1;
      update(root, { ...view.ctx, state: store.get() });
    }, (error) => {
      view.error = error;
      view.version += 1;
      update(root, { ...view.ctx, state: store.get() });
    });
  }
  view.parts.setTitle(`Model · ${modelName(session.state.model)}`);
  const currentNode = keyed(view.cache, 'current', [session.state, session.serviceTier], () => currentSection(ctx, session));
  const scopedNode = keyed(view.cache, 'scoped', [session.state.scopedModels], () => scopedSection(ctx, session));
  let catalogNode;
  if (view.error) {
    catalogNode = keyed(view.cache, 'catalog-error', [view.version], () => ui.section('All models', ui.empty({
      title: 'The model list did not load.',
      body: view.error.message,
      action: { label: 'Try again', onClick: () => {
        view.boundTo = null;
        update(root, { ...view.ctx, state: store.get() });
      } },
    })));
  } else if (!view.data) {
    catalogNode = keyed(view.cache, 'catalog-loading', [], () => ui.section('All models', ui.delayed(view.models, () => null, { lines: 10 })));
  } else {
    const providers = [...new Set(view.data.models.map((model) => model.provider))].sort();
    const filterNode = keyed(view.cache, 'filters', [view.version], () => filters(ctx, view, providers));
    const listNode = keyed(view.cache, 'catalog', [view.version, session.state, ctx.route.params.toString()], () => catalogSection(ctx, view, session, view.data));
    catalogNode = keyed(view.cache, 'catalog-section', [filterNode, listNode], () => ui.section('All models', filterNode, listNode));
  }
  place(view.parts.body, [currentNode, scopedNode, catalogNode]);
}

export default definePage({
  id: 'model',
  title: (ctx) => {
    const session = boundSession(ctx);
    return session ? `Model · ${modelName(session.state.model)}` : 'Model';
  },
  render,
  update,
  dispose(root) {
    views.delete(root);
  },
});
