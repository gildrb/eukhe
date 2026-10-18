// The model button in the composer and its menu: the available models
// (the current one checked), "All models" (the catalog, on demand), and
// submenus for the thinking level and the service tier. Changes apply at
// once; an error shows in the menu.

import * as Menu from "@radix-ui/react-dropdown-menu";
import * as stylex from "@stylexjs/stylex";
import { Check, ChevronDown } from "lucide-preact";
import { useState } from "react";
import { levelWord, listModels, modelKey, SERVICE_TIERS, setAndReload } from "../lib/actions.ts";
import { store, useStore } from "../lib/store.ts";
import { modelName } from "../lib/turn.ts";
import type { Model } from "../lib/types.ts";
import { colors, media, radius, size, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";

type Status = { text: string; error: boolean } | null;

/** Switch the thinking level. */
export function setThinking(level: string): Promise<void> {
  return setAndReload({ type: "set_thinking_level", level });
}

/** Switch the service tier; the daemon keeps its tier when the model has no such tier. */
export async function setTier(serviceTier: string): Promise<void> {
  await setAndReload({ type: "set_service_tier", serviceTier });
  const kept = store.get().session?.state.serviceTier;
  if (kept && kept !== serviceTier) {
    const word = SERVICE_TIERS.find((tier) => tier.value === kept)?.label ?? kept;
    throw new Error(`eukhe kept ${word}: this model has no ${serviceTier} tier.`);
  }
}

/** Switch the model. */
export function setModel(model: Model): Promise<void> {
  return setAndReload({ type: "set_model", provider: model.provider, modelId: model.id });
}

export function ModelMenu() {
  const session = useStore((state) => state.session);
  const [models, setModels] = useState<Model[] | null>(null);
  const [catalog, setCatalog] = useState(false);
  const [status, setStatus] = useState<Status>(null);
  const state = session?.state;
  const current = modelKey(state?.model);
  const levels = state?.availableThinkingLevels?.length ? state.availableThinkingLevels : ["off"];
  const tier = state?.serviceTier ?? session?.serviceTier ?? "default";

  const load = (all: boolean) => {
    setCatalog(all);
    listModels(all).then(setModels, (error: Error) =>
      setStatus({ text: `Models did not load. ${error.message}`, error: true }),
    );
  };
  const apply = (action: Promise<void>, done: string) => {
    setStatus({ text: "Switching", error: false });
    action.then(
      () => setStatus({ text: done, error: false }),
      (error: Error) => setStatus({ text: `Not changed. ${error.message}`, error: true }),
    );
  };

  return (
    <Menu.Root
      onOpenChange={(open) => {
        if (!open) return;
        setStatus(null);
        load(false);
      }}
    >
      <Menu.Trigger asChild disabled={!session}>
        <button type="button" {...stylex.props(ui.reset, ui.focusRing, styles.trigger)}>
          <span {...stylex.props(ui.ellipsis)}>
            {session ? modelName(state?.model) || "Model" : "Model"}
          </span>
          <ChevronDown aria-hidden="true" {...stylex.props(ui.iconSmall)} />
        </button>
      </Menu.Trigger>
      <Menu.Portal>
        <Menu.Content
          side="top"
          align="start"
          sideOffset={8}
          collisionPadding={8}
          loop
          {...stylex.props(ui.menu, styles.menu)}
        >
          <Menu.Label {...stylex.props(ui.menuLabel)}>
            {catalog ? "All models" : "Models"}
          </Menu.Label>
          <Menu.RadioGroup
            value={current}
            onValueChange={(key) => {
              const model = models?.find((entry) => modelKey(entry) === key);
              if (model) apply(setModel(model), `Now using ${model.name || model.id}.`);
            }}
          >
            {(models ?? []).map((model) => (
              <Menu.RadioItem
                key={modelKey(model)}
                value={modelKey(model)}
                onSelect={(event) => event.preventDefault()}
                {...stylex.props(ui.menuItem)}
              >
                <span {...stylex.props(ui.ellipsis, styles.name)}>{model.name || model.id}</span>
                <span translate={false} {...stylex.props(ui.menuTrail)}>
                  {model.provider}
                </span>
                <span {...stylex.props(styles.checkSlot)}>
                  <Menu.ItemIndicator>
                    <Check aria-hidden="true" {...stylex.props(ui.iconSmall)} />
                  </Menu.ItemIndicator>
                </span>
              </Menu.RadioItem>
            ))}
          </Menu.RadioGroup>
          {models && !models.length ? (
            <p {...stylex.props(ui.menuStatus)}>No models are available.</p>
          ) : null}
          {catalog ? null : (
            <Menu.Item
              onSelect={(event) => {
                event.preventDefault();
                load(true);
              }}
              {...stylex.props(ui.menuItem, styles.quiet)}
            >
              All models
            </Menu.Item>
          )}
          <Menu.Separator {...stylex.props(ui.menuSeparator)} />
          {/* Inline groups, not submenus: one tap on a phone, and the result shows right here. */}
          <Menu.Label {...stylex.props(ui.menuLabel)}>Thinking</Menu.Label>
          <Menu.RadioGroup
            value={state?.thinkingLevel ?? "off"}
            onValueChange={(level) =>
              apply(setThinking(level), `Thinking ${levelWord(level).toLowerCase()}.`)
            }
          >
            {levels.map((level) => (
              <Menu.RadioItem
                key={level}
                value={level}
                onSelect={(event) => event.preventDefault()}
                {...stylex.props(ui.menuItem)}
              >
                <span {...stylex.props(styles.name)}>{levelWord(level)}</span>
                <span {...stylex.props(styles.checkSlot)}>
                  <Menu.ItemIndicator>
                    <Check aria-hidden="true" {...stylex.props(ui.iconSmall)} />
                  </Menu.ItemIndicator>
                </span>
              </Menu.RadioItem>
            ))}
          </Menu.RadioGroup>
          <Menu.Separator {...stylex.props(ui.menuSeparator)} />
          <Menu.Label {...stylex.props(ui.menuLabel)}>Service tier</Menu.Label>
          <Menu.RadioGroup
            value={tier}
            onValueChange={(value) => apply(setTier(value), "Service tier changed.")}
          >
            {SERVICE_TIERS.map((entry) => (
              <Menu.RadioItem
                key={entry.value}
                value={entry.value}
                onSelect={(event) => event.preventDefault()}
                {...stylex.props(ui.menuItem)}
              >
                <span {...stylex.props(styles.name)}>{entry.label}</span>
                <span {...stylex.props(styles.checkSlot)}>
                  <Menu.ItemIndicator>
                    <Check aria-hidden="true" {...stylex.props(ui.iconSmall)} />
                  </Menu.ItemIndicator>
                </span>
              </Menu.RadioItem>
            ))}
          </Menu.RadioGroup>
          {status ? (
            <p role="status" {...stylex.props(ui.menuStatus, status.error && ui.menuDanger)}>
              {status.text}
            </p>
          ) : null}
        </Menu.Content>
      </Menu.Portal>
    </Menu.Root>
  );
}

const styles = stylex.create({
  trigger: {
    display: "inline-flex",
    alignItems: "center",
    columnGap: space.x1,
    minWidth: 0,
    maxWidth: "200px",
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x2,
    borderRadius: radius.control,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
    cursor: { default: "pointer", ":disabled": "default" },
  },
  menu: { width: "320px" },
  name: { flexGrow: 1, minWidth: 0 },
  checkSlot: { display: "flex", width: "16px", flexShrink: 0, justifyContent: "center" },
  quiet: { color: colors.secondary },
});
