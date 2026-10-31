/**
 * eukhe.com: `curl … | sh` gets the installer, a browser the page, an agent the page's Markdown.
 * Every other path is a static file from `dist/` (`env.ASSETS`).
 */
type Env = { ASSETS: Fetcher };

const apex = "eukhe.com";
const installer = "https://github.com/gildrb/eukhe/releases/latest/download/install.sh";

export default {
  fetch(request, env) {
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
    return env.ASSETS.fetch(request);
  },
} satisfies ExportedHandler<Env>;

async function markdown(response: Promise<Response>): Promise<Response> {
  const file = await response;
  const headers = new Headers(file.headers);
  headers.set("Content-Type", "text/markdown; charset=utf-8");
  headers.set("Vary", "Accept");
  return new Response(file.body, { status: file.status, headers });
}
