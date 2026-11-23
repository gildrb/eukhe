#!/usr/bin/env node
/**
 * An HTTP server that streams eukhe turns as Server-Sent Events.
 *   node examples/sse-server.ts /path/to/project
 *   curl -N 'http://localhost:8787/prompt?text=list%20the%20TODOs'
 * Each request runs one session; closing the connection cancels its turn.
 * Every SSE event is named after the eukhe event's `$` tag, its data the event as JSON.
 */
import { createServer, type ServerResponse } from "node:http";

import { Eukhe, EukheError, type EukheEvent } from "eukhe";

const eukhe = await Eukhe.start({ cwd: process.argv[2] ?? process.cwd() });

function send(response: ServerResponse, event: EukheEvent): void {
  response.write(`event: ${event.$}\ndata: ${JSON.stringify(event)}\n\n`);
}

const server = createServer(async (request, response) => {
  const url = new URL(request.url ?? "/", "http://localhost");
  const text = url.searchParams.get("text");
  if (url.pathname !== "/prompt" || text === null) {
    response.writeHead(404).end("GET /prompt?text=...\n");
    return;
  }
  response.writeHead(200, { "content-type": "text/event-stream", "cache-control": "no-cache" });
  try {
    const session = await eukhe.session();
    try {
      for await (const event of session.prompt(text)) {
        if (response.destroyed) break; // leaving the loop cancels the turn
        send(response, event);
      }
    } finally {
      await session.close();
    }
  } catch (error) {
    const message = error instanceof EukheError ? `${error.$}: ${error.message}` : String(error);
    response.write(`event: error\ndata: ${JSON.stringify(message)}\n\n`);
  }
  response.end();
});

server.listen(8787, () => console.log("listening on http://localhost:8787/prompt?text=..."));
process.once("SIGINT", () => {
  server.close();
  void eukhe.close();
});
