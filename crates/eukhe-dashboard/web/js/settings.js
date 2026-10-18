// Settings, driven by the route (`#/c/<id>/settings[/<section>]`). On
// desktop and tablet a modal (760×560, max 90vw/85vh) with a section list
// on the left; on phones a full-screen view: the section list ("← Settings"
// closes it), each section its own view ("← Settings" and Back return to
// the list).

import { el, iconButton, pushLayer, trapFocus, isPhone } from './ui.js';
import { chatHref, navigate } from './router.js';
import { SECTIONS } from './settings-sections.js';

/** `createSettings(app)` → `{ sync(route, state), update(state), open(section) }`. */
export function createSettings(app) {
  let shell = null;
  let fromApp = false;

  function leave() {
    const id = app.routeSessionId() || app.sessionId();
    if (fromApp) {
      fromApp = false;
      history.back();
    } else navigate(chatHref(id), { replace: true });
  }

  function sectionHref(section) {
    return chatHref(app.routeSessionId() || app.sessionId(), section);
  }

  function build() {
    const nav = el('nav', { class: 'settings-nav', 'aria-label': 'Settings sections' });
    const links = new Map();
    for (const section of SECTIONS) {
      const link = el('a', { class: 'settings-link', href: sectionHref(section.id) },
        el('span', { text: section.title }),
        el('span', { class: 'settings-arrow', 'aria-hidden': 'true', text: '→' }));
      link.addEventListener('click', (event) => {
        if (event.metaKey || event.ctrlKey || event.button !== 0) return;
        event.preventDefault();
        navigate(sectionHref(section.id), { replace: true });
      });
      links.set(section.id, link);
      nav.append(link);
    }
    const heading = el('h2', { class: 'settings-heading', id: 'settings-heading', tabindex: '-1', text: 'Settings' });
    const content = el('div', { class: 'settings-content' });
    const contentScroll = el('div', { class: 'settings-scroll' }, heading, content);
    const back = el('button', { type: 'button', class: 'settings-back' }, el('span', { class: 'settings-back-arrow', 'aria-hidden': 'true', text: '←' }), el('span', { text: 'Settings' }));
    back.addEventListener('click', () => {
      if (current.sectionLayer) current.sectionLayer.close();
      else current.layer.close();
    });
    const close = iconButton('Close settings', 'close', () => current.layer.close(), { className: 'settings-close' });
    const top = el('div', { class: 'settings-top' }, back, close);
    const panel = el('div', { class: 'settings', role: 'dialog', 'aria-modal': 'true', 'aria-labelledby': 'settings-heading', tabindex: '-1' }, top, el('div', { class: 'settings-main' }, nav, contentScroll));
    const scrim = el('div', { class: 'layer-catcher scrim-layer' });
    scrim.addEventListener('pointerdown', (event) => {
      event.preventDefault();
      current.layer.close();
    });
    const host = el('div', { class: 'layer layer-center settings-layer' }, scrim, panel);
    const current = { host, panel, nav, links, heading, content, contentScroll, layer: null, section: null, sections: new Map(), leaving: false, sectionLayer: null };
    current.layer = pushLayer({
      dismiss: () => {
        host.remove();
        if (shell === current) shell = null;
        if (current.sectionLayer) {
          const inner = current.sectionLayer;
          current.leaving = true;
          inner.close();
        }
        if (!current.leaving) leave();
      },
    });
    document.body.append(host);
    trapFocus(panel);
    requestAnimationFrame(() => host.classList.add('open'));
    return current;
  }

  function show(section, state) {
    if (!shell) shell = build();
    const phone = isPhone();
    const named = SECTIONS.find((entry) => entry.id === section);
    const known = named || (phone ? null : SECTIONS[0]);
    const wanted = known ? known.id : '';
    shell.host.classList.toggle('full', phone);
    shell.host.dataset.view = wanted ? 'section' : 'list';
    if (shell.section === wanted) return;
    shell.section = wanted;
    if (phone && wanted && !shell.sectionLayer) {
      const owner = shell;
      owner.sectionLayer = pushLayer({
        history: true,
        dismiss: () => {
          owner.sectionLayer = null;
          if (!owner.leaving && shell === owner) navigate(sectionHref(''), { replace: true });
        },
      });
    }
    for (const [id, link] of shell.links) link.setAttribute('aria-current', id === wanted ? 'page' : 'false');
    if (!wanted) {
      shell.heading.textContent = 'Settings';
      shell.content.replaceChildren();
      const owner = shell;
      requestAnimationFrame(() => owner.panel.focus({ preventScroll: true }));
      return;
    }
    let created = shell.sections.get(wanted);
    if (!created) {
      created = known.create(app);
      shell.sections.set(wanted, created);
    }
    shell.heading.textContent = known.title;
    shell.content.replaceChildren(created.node);
    shell.contentScroll.scrollTop = 0;
    created.update(state);
    const owner = shell;
    requestAnimationFrame(() => {
      if (isPhone()) owner.heading.focus({ preventScroll: true });
      else if (!owner.panel.contains(document.activeElement)) owner.panel.focus({ preventScroll: true });
    });
  }

  return {
    sync(route, state) {
      if (route.settings === null) {
        if (shell) {
          shell.leaving = true;
          shell.layer.close();
        }
        return;
      }
      show(route.settings, state);
    },
    update(state) {
      if (!shell || !shell.section) return;
      const created = shell.sections.get(shell.section);
      if (created) created.update(state);
    },
    /** Open Settings from inside the app (closing it then goes Back). */
    open(section = '') {
      fromApp = true;
      navigate(sectionHref(section));
    },
  };
}
