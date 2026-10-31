/**
 * eukhe.com: `curl … | sh` gets the installer, a browser the page, an agent the page's Markdown.
 * Every other path is a static file from `dist/` (`env.ASSETS`); asked for Markdown, a page
 * answers with its `.md` twin, and a missing one with the 404 page's Markdown.
 */
type Env = { ASSETS: Fetcher };

const apex = "eukhe.com";
const installer = "https://github.com/gildrb/eukhe/releases/latest/download/install.sh";

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    if (url.hostname === `www.${apex}`)
      return Response.redirect(`https://${apex}${url.pathname}${url.search}`, 301);
    if (url.pathname === "/install")
      return new Response(null, { status: 302, headers: { Location: installer } });
    if (url.pathname === "/") {
      // `curl` sends `Accept: */*`; a browser asks for HTML, an agent for Markdown.
      const accept = request.headers.get("Accept") ?? "";
      if (accept.includes("text/markdown"))
        return markdown(env.ASSETS.fetch(new URL("/index.md", url)));
      if (!accept.includes("text/html"))
        return new Response(null, {
          status: 302,
          headers: { Location: installer, Vary: "Accept" },
        });
    }
    if ((request.headers.get("Accept") ?? "").includes("text/markdown")) {
      const twin = await env.ASSETS.fetch(new URL(`${url.pathname.replace(/\/$/, "")}.md`, url));
      if (twin.ok) return markdown(Promise.resolve(twin));
      const page = await env.ASSETS.fetch(request);
      if (page.status === 404) return markdown(env.ASSETS.fetch(new URL("/404.md", url)), 404);
      return page;
    }
    return env.ASSETS.fetch(request);
  },
} satisfies ExportedHandler<Env>;

async function markdown(response: Promise<Response>, status?: number): Promise<Response> {
  const file = await response;
  const headers = new Headers(file.headers);
  headers.set("Content-Type", "text/markdown; charset=utf-8");
  headers.set("Vary", "Accept");
  return new Response(file.body, { status: status ?? file.status, headers });
}
