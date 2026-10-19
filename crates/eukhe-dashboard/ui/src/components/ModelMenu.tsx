// The composer's model button and reasoning button, each with its menu.
// The model menu lists the available models (the current one checked),
// "All models" (the catalog, on demand) and, only when the model honors
// more than one, the service tiers. The reasoning menu lists the thinking
// levels. Level and tier names are the daemon's strings, shown verbatim as
// the CLI shows them (`availableThinkingLevels`, `availableServiceTiers`).
// Changes apply at once; the result shows in the menu.

import * as Menu from "@radix-ui/react-dropdown-menu";
import * as stylex from "@stylexjs/stylex";
import { Brain, Check, ChevronDown } from "lucide-preact";
import type { ComponentChildren } from "preact";
import { useState } from "react";
import { listModels, modelKey, setModel, setThinking, setTier } from "../lib/actions.ts";
import { useStore } from "../lib/store.ts";
import { modelName } from "../lib/turn.ts";
import type { AgentState, Model } from "../lib/types.ts";
import { colors, media, radius, size, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";

type Status = { text: string; error: boolean } | null;

/** The thinking levels the daemon offers for the current model. */
export function thinkingLevels(state: AgentState | undefined): string[] {
  return state?.availableThinkingLevels ?? [];
}

/** The service tiers the daemon offers; a choice exists only with more than one. */
export function serviceTiers(state: AgentState | undefined): string[] {
  return state?.availableServiceTiers ?? [];
}

/** Run a change and report it in the menu: "Switching", then `done` or the error. */
function useApply(): [
  Status,
  (action: Promise<void>, done: string) => void,
  (status: Status) => void,
] {
  const [status, setStatus] = useState<Status>(null);
  const apply = (action: Promise<void>, done: string) => {
    setStatus({ text: "Switching", error: false });
    action.then(
      () => setStatus({ text: done, error: false }),
      (error: Error) => setStatus({ text: `Not changed. ${error.message}`, error: true }),
    );
  };
  return [status, apply, setStatus];
}

function StatusLine({ status }: { status: Status }) {
  return status ? (
    <p role="status" {...stylex.props(ui.menuStatus, status.error && ui.menuDanger)}>
      {status.text}
    </p>
  ) : null;
}

/** One radio row: the name, an optional trailing note, the check of the current one. */
function Choice({ value, children }: { value: string; children: ComponentChildren }) {
  return (
    <Menu.RadioItem
      value={value}
      // The menu stays open, so the result shows under the choices.
      onSelect={(event) => event.preventDefault()}
      {...stylex.props(ui.menuItem)}
    >
      {children}
      <span {...stylex.props(styles.checkSlot)}>
        <Menu.ItemIndicator>
          <Check aria-hidden="true" {...stylex.props(ui.iconSmall)} />
        </Menu.ItemIndicator>
      </span>
    </Menu.RadioItem>
  );
}

/** The reasoning button: the current level, opening the levels. `defaultOpen` is a test seam. */
export function ReasoningMenu({ defaultOpen = false }: { defaultOpen?: boolean }) {
  const state = useStore((current) => current.session?.state);
  const [status, apply, setStatus] = useApply();
  const levels = thinkingLevels(state);
  const level = state?.thinkingLevel ?? levels[0] ?? "";
  // A model without a choice of levels gets no button.
  if (levels.length < 2) return null;
  return (
    <Menu.Root defaultOpen={defaultOpen} onOpenChange={(open) => open && setStatus(null)}>
      <Menu.Trigger asChild>
        <button
          type="button"
          aria-label={`Reasoning: ${level}`}
          {...stylex.props(ui.reset, ui.focusRing, styles.trigger, styles.reasoning)}
        >
          <Brain aria-hidden="true" {...stylex.props(ui.iconSmall)} />
          <span translate={false} {...stylex.props(ui.ellipsis)}>
            {level}
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
          aria-label="Reasoning"
          {...stylex.props(ui.menu, styles.small)}
        >
          <Menu.Label {...stylex.props(ui.menuLabel)}>Reasoning</Menu.Label>
          <Menu.RadioGroup
            value={level}
            onValueChange={(next) => apply(setThinking(next), `Reasoning ${next}.`)}
          >
            {levels.map((entry) => (
              <Choice key={entry} value={entry}>
                <span translate={false} {...stylex.props(styles.name)}>
                  {entry}
                </span>
              </Choice>
            ))}
          </Menu.RadioGroup>
          <StatusLine status={status} />
        </Menu.Content>
      </Menu.Portal>
    </Menu.Root>
  );
}

/** The model button: the models, and the service tiers when there is a choice. `defaultOpen` is a test seam. */
export function ModelMenu({ defaultOpen = false }: { defaultOpen?: boolean }) {
  const session = useStore((current) => current.session);
  const [models, setModels] = useState<Model[] | null>(null);
  const [catalog, setCatalog] = useState(false);
  const [status, apply, setStatus] = useApply();
  const state = session?.state;
  const current = modelKey(state?.model);
  const tiers = serviceTiers(state);
  const tier = state?.serviceTier ?? session?.serviceTier ?? tiers[0] ?? "";

  const load = (all: boolean) => {
    setCatalog(all);
    listModels(all).then(setModels, (error: Error) =>
      setStatus({ text: `Models did not load. ${error.message}`, error: true }),
    );
  };

  return (
    <Menu.Root
      defaultOpen={defaultOpen}
      onOpenChange={(open) => {
        if (!open) return;
        setStatus(null);
        load(false);
      }}
    >
      <Menu.Trigger asChild disabled={!session}>
        <button
          type="button"
          {...stylex.props(ui.reset, ui.focusRing, styles.trigger, styles.model)}
        >
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
          aria-label="Model"
          {...stylex.props(ui.menu, styles.wide)}
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
              <Choice key={modelKey(model)} value={modelKey(model)}>
                <span {...stylex.props(ui.ellipsis, styles.name)}>{model.name || model.id}</span>
                <span translate={false} {...stylex.props(ui.menuTrail)}>
                  {model.provider}
                </span>
              </Choice>
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
          {tiers.length > 1 ? (
            <>
              <Menu.Separator {...stylex.props(ui.menuSeparator)} />
              <Menu.Label {...stylex.props(ui.menuLabel)}>Service tier</Menu.Label>
              <Menu.RadioGroup
                value={tier}
                onValueChange={(next) => apply(setTier(next), `Service tier ${next}.`)}
              >
                {tiers.map((entry) => (
                  <Choice key={entry} value={entry}>
                    <span translate={false} {...stylex.props(styles.name)}>
                      {entry}
                    </span>
                  </Choice>
                ))}
              </Menu.RadioGroup>
            </>
          ) : null}
          <StatusLine status={status} />
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
    height: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x2,
    borderRadius: radius.control,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
    cursor: { default: "pointer", ":disabled": "default" },
  },
  model: { flexShrink: 1, maxWidth: { default: "200px", [media.phone]: "132px" } },
  reasoning: { flexShrink: 0, maxWidth: "120px" },
  wide: { width: "320px" },
  small: { minWidth: "180px" },
  name: { flexGrow: 1, minWidth: 0 },
  checkSlot: { display: "flex", width: "16px", flexShrink: 0, justifyContent: "center" },
  quiet: { color: colors.secondary },
});
