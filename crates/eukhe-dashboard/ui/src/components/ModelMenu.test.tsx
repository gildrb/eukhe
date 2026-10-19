// The reasoning and model menus show the daemon's level and tier names
// verbatim, and a tier choice only when the model honors more than one.

import { render, type ComponentChild } from "preact";
import { act } from "preact/test-utils";
import { afterEach, describe, expect, test } from "vite-plus/test";
import { store } from "../lib/store.ts";
import { openSession } from "../lib/turn.ts";
import type { AgentState } from "../lib/types.ts";
import { ModelMenu, ReasoningMenu } from "./ModelMenu.tsx";

function bind(state: AgentState) {
  const reply = {
    session: { id: "s1", path: "/tmp/s1.jsonl" },
    state,
    summary: null,
    messages: [],
    cursor: null,
    replay: null,
  };
  store.set({ session: openSession(reply, null, 0) });
}

const hosts: HTMLElement[] = [];

/** Render `node` (its menu open); the texts of the open `menu`'s radio items. */
function openItems(node: ComponentChild, menu: string): string[] {
  const host = document.createElement("div");
  document.body.append(host);
  hosts.push(host);
  // A synchronous callback: act flushes the render before it returns.
  void act(() => render(node, host));
  const content = document.querySelector(`[role=menu][aria-label="${menu}"]`);
  if (!content) throw new Error(`the ${menu} menu did not open`);
  return [...content.querySelectorAll("[role=menuitemradio]")].map(
    (item) => item.textContent ?? "",
  );
}

/** The open model menu's text. */
function modelMenuText(): string {
  return document.querySelector('[role=menu][aria-label="Model"]')?.textContent ?? "";
}

afterEach(() => {
  void act(() => {
    for (const host of hosts.splice(0)) render(null, host);
  });
  document.body.innerHTML = "";
});

const qwen: AgentState = {
  model: { provider: "elpis", id: "qwen3.8", name: "qwen3.8" },
  thinkingLevel: "xhigh",
  availableThinkingLevels: ["off", "low", "medium", "xhigh"],
};

describe("reasoning menu", () => {
  test("lists exactly the daemon's levels, verbatim", () => {
    bind({ ...qwen, availableServiceTiers: ["default"] });
    expect(openItems(<ReasoningMenu defaultOpen />, "Reasoning")).toEqual([
      "off",
      "low",
      "medium",
      "xhigh",
    ]);
    expect(document.querySelector('button[aria-label="Reasoning: xhigh"]')?.textContent).toBe(
      "xhigh",
    );
  });
});

describe("model menu", () => {
  test("has no tier control when the model honors one tier", () => {
    bind({ ...qwen, availableServiceTiers: ["default"] });
    expect(openItems(<ModelMenu defaultOpen />, "Model")).toEqual([]);
    expect(modelMenuText()).not.toContain("Service tier");
  });

  test("lists exactly the daemon's tiers when there is a choice", () => {
    bind({
      ...qwen,
      serviceTier: "default",
      availableServiceTiers: ["auto", "default", "flex", "scale", "priority"],
    });
    expect(openItems(<ModelMenu defaultOpen />, "Model")).toEqual([
      "auto",
      "default",
      "flex",
      "scale",
      "priority",
    ]);
    expect(modelMenuText()).toContain("Service tier");
  });
});
