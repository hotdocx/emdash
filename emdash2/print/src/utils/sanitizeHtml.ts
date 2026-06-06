import createDOMPurify from "dompurify";

let purifier: ReturnType<typeof createDOMPurify> | null = null;

export function sanitizeHtml(html: string): string {
  if (typeof window === "undefined") return html;
  if (!purifier) purifier = createDOMPurify(window);

  return purifier.sanitize(html, {
    USE_PROFILES: { html: true, svg: true, svgFilters: true },
    ADD_TAGS: ["text", "tspan", "foreignObject"],
    ADD_ATTR: ["dominant-baseline", "text-anchor"],
    FORBID_TAGS: ["script", "iframe", "object", "embed"],
    FORBID_ATTR: ["srcdoc"],
  });
}
