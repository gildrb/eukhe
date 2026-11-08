---
name: mcp
description: Use external services over MCP (Notion, Linear, Slack and the rest of the catalog) from the REPL through the pre-imported mcp module - find whether a service is supported and connected, discover a connection's live tool schemas, and call its tools. Use when a task needs data or actions in an external service, or when the user asks which services they can connect.
---

# MCP Services

One pre-imported `mcp` module reaches every service; there are no per-service skills or packages.

## Steps

1. Connections: `await mcp.list_connections()`. A `connectionId` is the id every call below takes.
2. Not connected: search the catalog narrowly, `await mcp.search_plugins("notion")`. Do not page the whole catalog.
3. Discover before you call: `await mcp.search_tools("search documents", connection_id="notion")`, then `await mcp.describe_tool("notion", "notion-search")` for its `inputSchema`. Never guess tool names or arguments.
4. Call: `await mcp.call_tool("notion", "notion-search", {"query": "roadmap"})`. The result is parsed Python (a dict, else a string).

## Recommend, never connect

- An unconnected service that would help: name the catalog entry and tell the user to open `/plugins` or run `/mcp login <service>`. You cannot connect, log in or ask for scopes.
- `setup_required` needs a developer app or API key first: say so; do not promise one click.
- A connection the user adds mid-task works on the next call.

## Failures

- `PermissionError`: the user's tool policy excludes the tool. Do not retry; tell the user.
- `KeyError`: no such tool or connection; re-list, tools change between sessions.
- `McpToolError`: the server reported an error. Report it; never blindly retry a write that may have run.
- Credentials missing: ask the user to connect via `/plugins`, never through environment variables.

Catalog fields, search scope and every error: [references/api.md](references/api.md).
