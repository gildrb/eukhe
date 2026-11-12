#!/usr/bin/env python3
"""Tests for the models.dev catalog mapping (scripts/release/models_dev.py).

Offline: the mapping rules on hand-made models.dev rows, the overrides and
the compiled-catalog exclusion, the snapshot pin, and the committed catalog
fixture against the committed snapshot and overrides.

Run: python3 scripts/release/test_models_dev.py  (or: make catalog-assets-gates)
"""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

import models_dev  # noqa: E402  (same release-scripts directory)

ROUTE = {"api": "openai-completions", "baseUrl": "https://api.example/v1"}


def row(**fields) -> dict:
    """A models.dev v1 model row with the fields the mapping reads."""
    model = {
        "name": "Model",
        "tool_call": True,
        "reasoning": False,
        "modalities": {"input": ["text"]},
        "limit": {"context": 200_000, "output": 32_000},
        "cost": {"input": 1, "output": 2},
    }
    model.update(fields)
    return model


def reasoning(*options) -> dict:
    return row(reasoning=True, reasoning_options=list(options))


def effort(*values) -> dict:
    return {"type": "effort", "values": list(values)}


def quietly(function, *args):
    """Run `function`, expecting it to fail (SystemExit), with stderr kept."""
    with contextlib.redirect_stderr(io.StringIO()) as stderr:
        with unittest.TestCase().assertRaises(SystemExit):
            function(*args)
    return stderr.getvalue()


class ThinkingLadder(unittest.TestCase):

    def ladder(self, model, api="openai-completions"):
        return models_dev.thinking_level_map(model, api)

    def test_an_effort_list_with_none_turns_off_with_none(self):
        self.assertEqual(
            self.ladder(reasoning(effort("none", "low", "medium", "high", "xhigh"))),
            {"minimal": None, "xhigh": "xhigh", "off": "none"})

    def test_an_effort_list_with_a_toggle_keeps_the_apis_off(self):
        self.assertEqual(
            self.ladder(reasoning({"type": "toggle"}, effort("low", "high", "max"))),
            {"minimal": None, "medium": None, "max": "max"})

    def test_an_effort_list_without_off_control_has_no_off(self):
        self.assertEqual(
            self.ladder(reasoning(effort("low", "medium", "high", "xhigh", "max")),
                        "anthropic-messages"),
            {"minimal": None, "xhigh": "xhigh", "max": "max", "off": None})

    def test_an_unknown_effort_value_is_ignored(self):
        self.assertEqual(self.ladder(reasoning(effort("default", "high"))),
                         {"minimal": None, "low": None, "medium": None, "off": None})

    def test_a_budget_that_cannot_reach_zero_has_no_off(self):
        self.assertEqual(
            self.ladder(reasoning({"type": "budget_tokens", "min": 128, "max": 32768}),
                        "google-generative-ai"),
            {"off": None})

    def test_a_budget_keeps_the_default_ladder_where_thinking_is_opt_in(self):
        self.assertIsNone(self.ladder(reasoning({"type": "budget_tokens", "min": 1024}),
                                      "anthropic-messages"))
        self.assertIsNone(self.ladder(reasoning({"type": "budget_tokens", "min": 1024}),
                                      "bedrock-converse-stream"))

    def test_a_budget_with_a_toggle_or_a_zero_floor_keeps_the_default_ladder(self):
        self.assertIsNone(self.ladder(reasoning(
            {"type": "toggle"}, {"type": "budget_tokens", "min": 512})))
        self.assertIsNone(self.ladder(reasoning({"type": "budget_tokens", "min": 0})))

    def test_a_toggle_alone_keeps_the_default_ladder(self):
        self.assertIsNone(self.ladder(reasoning({"type": "toggle"})))

    def test_an_always_on_model_offers_no_level(self):
        expected = {"off": None, "minimal": None, "low": None, "medium": None, "high": None}
        self.assertEqual(self.ladder(reasoning()), expected)
        self.assertEqual(self.ladder(row(reasoning=True)), expected)

    def test_a_model_without_reasoning_has_no_ladder(self):
        self.assertIsNone(self.ladder(row(reasoning_options=[effort("low")])))


class Mapping(unittest.TestCase):

    def test_an_entry_takes_the_models_dev_facts(self):
        model = row(name="Big", reasoning=True,
                    reasoning_options=[effort("low", "medium", "high")],
                    modalities={"input": ["text", "image", "pdf"]},
                    limit={"context": 400_000, "output": 128_000},
                    cost={"input": 1.25, "output": 10, "cache_read": 0.125})
        self.assertEqual(models_dev.map_model("prov", ROUTE, "big", model), {
            "id": "big",
            "name": "Big",
            "api": "openai-completions",
            "provider": "prov",
            "baseUrl": "https://api.example/v1",
            "reasoning": True,
            "input": ["text", "image"],
            "cost": {"input": 1.25, "output": 10, "cacheRead": 0.125, "cacheWrite": 0},
            "contextWindow": 400_000,
            "maxTokens": 128_000,
            "thinkingLevelMap": {"minimal": None, "off": None},
        })

    def test_an_output_limit_falls_back_to_the_context(self):
        entry = models_dev.map_model("prov", ROUTE, "m", row(limit={"context": 8192}))
        self.assertEqual(entry["maxTokens"], 8192)

    def test_routes_pick_by_sdk_and_id_prefix_and_rewrite_the_id(self):
        spec = {"routes": [
            {"npm": "@ai-sdk/anthropic", "api": "anthropic-messages", "baseUrl": "a",
             "stripPrefix": "anthropic/", "dotsToDashes": True},
            {"npm": None, "idPrefix": "eu.", "api": "x", "baseUrl": "eu"},
            {"npm": None, "api": "x", "baseUrl": "us"},
        ]}
        claude = row(provider={"npm": "@ai-sdk/anthropic"})
        route = models_dev.route_for(spec, "anthropic/claude-opus-4.6", claude)
        self.assertEqual(route["api"], "anthropic-messages")
        self.assertEqual(models_dev.route_id(route, "anthropic/claude-opus-4.6"),
                         "claude-opus-4-6")
        self.assertEqual(models_dev.route_for(spec, "eu.m", row())["baseUrl"], "eu")
        self.assertEqual(models_dev.route_for(spec, "m", row())["baseUrl"], "us")
        # A per-model SDK no route names has no transport: no entry.
        self.assertIsNone(models_dev.route_for(
            spec, "m", row(provider={"npm": "@ai-sdk/mistral"})))

    def test_only_active_tool_calling_chat_models_are_kept(self):
        self.assertTrue(models_dev.kept(row()))
        self.assertTrue(models_dev.kept(row(type="chat", status="beta")))
        self.assertFalse(models_dev.kept(row(tool_call=False)))
        self.assertFalse(models_dev.kept(row(status="deprecated")))
        self.assertFalse(models_dev.kept(row(type="image")))


class Catalog(unittest.TestCase):

    snapshot = {"md": {"name": "MD", "models": {
        "kept": row(),
        "compiled": row(),
        "old": row(status="deprecated"),
        "fixed": row(limit={"context": 1000, "output": 4000}),
    }}}

    def overrides(self, models=None):
        return {"providers": {"prov": {"modelsDev": "md", "routes": [ROUTE]}},
                "models": models or {}}

    def ids(self, catalog):
        return [entry["id"] for entry in catalog["models"]]

    def test_the_bundle_leaves_out_compiled_models(self):
        catalog = models_dev.generate_catalog(
            self.snapshot, self.overrides(), {("prov", "compiled")})
        self.assertEqual(catalog["schemaVersion"], 1)
        self.assertEqual(self.ids(catalog), ["fixed", "kept"])

    def test_overrides_replace_delete_or_drop(self):
        catalog = models_dev.generate_catalog(self.snapshot, self.overrides({
            "prov/fixed": {"maxTokens": 1000, "thinkingLevelMap": None},
            "prov/kept": {"skip": True},
        }), {("prov", "compiled")})
        self.assertEqual(self.ids(catalog), ["fixed"])
        self.assertEqual(catalog["models"][0]["maxTokens"], 1000)
        self.assertNotIn("thinkingLevelMap", catalog["models"][0])

    def test_an_override_the_bundle_does_not_carry_fails(self):
        error = quietly(models_dev.generate_catalog, self.snapshot,
                        self.overrides({"prov/compiled": {"maxTokens": 1}}),
                        {("prov", "compiled")})
        self.assertIn("prov/compiled", error)
        error = quietly(models_dev.generate_catalog, self.snapshot,
                        self.overrides({"prov/gone": {"skip": True}}), set())
        self.assertIn("prov/gone", error)

    def test_two_models_that_map_to_one_id_fail(self):
        snapshot = {"md": {"models": {"a.1": row(), "a-1": row()}}}
        overrides = {"providers": {"prov": {"modelsDev": "md", "routes": [
            dict(ROUTE, dotsToDashes=True)]}}}
        self.assertIn("prov/a-1", quietly(models_dev.generate_catalog,
                                          snapshot, overrides, set()))


class Snapshot(unittest.TestCase):

    def test_a_snapshot_that_does_not_match_its_pin_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            snapshot = Path(tmp) / "models-dev.json"
            pin = Path(tmp) / "models-dev.pin.json"
            snapshot.write_text(models_dev.canonical_json({"md": {"models": {}}}))
            pin.write_text(json.dumps({
                "repository": models_dev.REPOSITORY, "commit": "0" * 40,
                "date": "2026-01-01T00:00:00Z",
                "sha256": models_dev.sha256_text(snapshot.read_text()),
            }))
            self.assertEqual(models_dev.load_snapshot(snapshot, pin), {"md": {"models": {}}})
            snapshot.write_text(snapshot.read_text().replace("{}", '{"x": {}}'))
            self.assertIn("does not match the pin",
                          quietly(models_dev.load_snapshot, snapshot, pin))

    def test_the_projection_keeps_only_what_the_mapping_reads(self):
        api = {"md": {"id": "md", "name": "MD", "npm": "@ai-sdk/x", "env": ["KEY"],
                      "models": {"b": row(description="long", family="f",
                                          cost={"input": 1, "output": 2,
                                                "tiers": [{"input": 3}]}),
                                 "a": row()}}}
        projected = models_dev.project(api, ["md"])
        self.assertEqual(list(projected["md"]["models"]), ["a", "b"])
        self.assertEqual(set(projected["md"]), {"name", "npm", "models"})
        self.assertNotIn("description", projected["md"]["models"]["b"])
        self.assertEqual(projected["md"]["models"]["b"]["cost"], {"input": 1, "output": 2})

    def test_the_committed_snapshot_matches_its_pin(self):
        pin = json.loads(models_dev.PIN.read_text())
        self.assertEqual(pin["repository"], "anomalyco/models.dev")
        self.assertRegex(pin["commit"], r"^[0-9a-f]{40}$")
        snapshot = models_dev.load_snapshot()
        keys = {spec["modelsDev"] for spec in models_dev.load_overrides()["providers"].values()}
        self.assertEqual(set(snapshot), keys)

    def test_the_committed_fixture_is_the_generated_catalog(self):
        self.assertEqual(models_dev.FIXTURE.read_text(), models_dev.bundled_catalog_text())


if __name__ == "__main__":
    unittest.main(verbosity=2)
