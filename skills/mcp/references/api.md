# mcp API

- `mcp.list_connections() -> list[dict]`: the user's current connections; `connectionId` is the dispatch id.
- `mcp.list_plugins(connection_status: str | None = None, limit: int = 50, cursor: str | None = None) -> dict`: one bounded page of the supported-service catalog; more pages exist while `nextCursor` is not `None`.
- `mcp.search_plugins(query: str, limit: int = 10) -> dict`: bounded catalog search.
- `mcp.search_tools(query: str, connection_id: str | None = None, limit: int = 20) -> dict`: searches live tool names and descriptions. Without `connection_id` it searches at most 8 connected connections and reports its scope: `searched`, `unavailable` (per-connection failures as fixed, redaction-safe summaries) and `truncated` (narrow the query or pick a connection when set; the result never claims to be complete).
- `mcp.describe_tool(connection_id: str, tool: str) -> dict`: one live tool's `name`, `description`, `inputSchema`.
- `mcp.list_tools(server: str) -> list[dict]`: the complete tool list with schemas, or an error; never a silent partial list. Returned schemas are copies; mutate them freely.
- `mcp.call_tool(server: str, tool: str, arguments: dict | None = None) -> Any`: calls one tool; returns parsed Python.

Live tool metadata is cached per connection.

## Catalog entries

- `connectionStatus`: `connected` (a verified MCP handshake, not only stored credentials), `pending` (credentials exist, verification has not run or failed), `not_connected`, `setup_required` (needs a developer app or API key), `disabled`, `error`.
- `connectable`, `connectionIds` (empty when not dispatchable), `setupHint` (why it is not connectable yet), `unverified` (imported, not vetted), `verifiedAt`, `toolCount`.

## Errors

| Error | Meaning | Do |
|---|---|---|
| `PermissionError` | the user's `enabledTools`/`disabledTools` policy excludes the tool | tell the user; no retry |
| `KeyError` | the tool or connection does not exist | re-check with `list_tools`/`list_connections` |
| `McpDiscoveryError` | the server's tool listing could not complete (broken pagination); nothing partial is published | re-run; if it persists, ask the user to reconnect |
| `RuntimeError` (`McpCredentialsUnavailable`) | no credentials | ask the user to connect via `/plugins` or `/mcp login <service>` |
| `RuntimeError` (other) | a token refresh failed or the host bridge is unavailable | report it |
| `McpToolError` | the server flagged the call as an error | report the message; do not blindly retry a write |

Credentials never appear in inventory results, schemas or errors.
