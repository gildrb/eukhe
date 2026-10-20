// eukhe.com: the installer endpoint.
//
//   GET /install, /install.sh  the install.sh that the newest GitHub release
//                               attaches (the copy CI passed with that release)
//   GET /                       redirect to the repository
//   anything else               404
//   any http:// request         301 to its https:// URL (a script piped into
//                               sh must never come over plain HTTP)
//
// The script is fetched from GitHub and served as text, so
// `curl -fsSL https://eukhe.com/install | sh` needs no redirect. If GitHub
// does not answer with the script, the reply is a 502 whose body is a shell
// script that prints the error and exits 1, so a pipe into sh never runs an
// HTML error page.

const REPO = "https://github.com/gildrb/eukhe";
const SCRIPT = `${REPO}/releases/latest/download/install.sh`;
const CACHE_SECONDS = 300;

function failure(message) {
  const body = `#!/bin/sh\necho 'error: ${message.replace(/'/g, "")}' >&2\nexit 1\n`;
  return new Response(body, {
    status: 502,
    headers: { "content-type": "text/x-shellscript; charset=utf-8", "cache-control": "no-store" },
  });
}

async function installer(method) {
  let upstream;
  try {
    upstream = await fetch(SCRIPT, { redirect: "follow", cf: { cacheTtl: CACHE_SECONDS, cacheEverything: true } });
  } catch (error) {
    return failure(`cannot reach GitHub for the installer (${error.message})`);
  }
  if (!upstream.ok) {
    return failure(`GitHub answered ${upstream.status} for ${SCRIPT}`);
  }
  const text = await upstream.text();
  if (!text.startsWith("#!/bin/sh")) {
    return failure(`${SCRIPT} is not a shell script`);
  }
  return new Response(method === "HEAD" ? null : text, {
    status: 200,
    headers: {
      "content-type": "text/x-shellscript; charset=utf-8",
      "cache-control": `public, max-age=${CACHE_SECONDS}`,
      "x-content-type-options": "nosniff",
    },
  });
}

export default {
  async fetch(request) {
    const url = new URL(request.url);
    if (url.protocol === "http:") {
      url.protocol = "https:";
      return Response.redirect(url.toString(), 301);
    }
    const { pathname } = url;
    if (request.method !== "GET" && request.method !== "HEAD") {
      return new Response("method not allowed\n", { status: 405, headers: { allow: "GET, HEAD" } });
    }
    switch (pathname) {
      case "/install":
      case "/install.sh":
        return installer(request.method);
      case "/":
        return Response.redirect(REPO, 302);
      default:
        return new Response("not found\n", { status: 404, headers: { "content-type": "text/plain; charset=utf-8" } });
    }
  },
};
