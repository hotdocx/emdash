import ReactDOMServer from "react-dom/server";
import showdown from "showdown";
import katex from "katex";
import { sanitizeHtml } from "../utils/sanitizeHtml";
import { ArrowGramStatic } from "../components/ArrowGramStatic";

export type ArrowgramHydrationTarget = { id: string; spec: string };

export type MarkdownRenderModel = {
  html: string;
  metadata: Record<string, any>;
  arrowgrams: ArrowgramHydrationTarget[];
};

export type MarkdownPipelineOptions = {
  idPrefix?: string;
  includeTitleBlock?: boolean;
  arrowgrams?: {
    mode: "static-only" | "static+hydrate";
  };
};

type VegaRuntime = { vega: any; vegaLite: any };

let vegaRuntimePromise: Promise<VegaRuntime | null> | null = null;
let mermaidRuntimePromise: Promise<any | null> | null = null;

async function loadVegaRuntime(): Promise<VegaRuntime | null> {
  if (import.meta.env.SSR) return null;
  if (!vegaRuntimePromise) {
    vegaRuntimePromise = Promise.all([import("vega"), import("vega-lite")])
      .then(([vega, vegaLite]) => ({ vega, vegaLite }))
      .catch((e) => {
        console.error("Failed to load Vega runtime:", e);
        return null;
      });
  }
  return await vegaRuntimePromise;
}

async function loadMermaidRuntime(): Promise<any | null> {
  if (import.meta.env.SSR) return null;
  if (!mermaidRuntimePromise) {
    mermaidRuntimePromise = import("mermaid")
      .then((m) => (m as any).default ?? m)
      .catch((e) => {
        console.error("Failed to load Mermaid runtime:", e);
        return null;
      });
  }
  return await mermaidRuntimePromise;
}

function protectMathBlocks(markdown: string) {
  const protectedMathBlocks = new Map<string, string>();
  let mathPlaceholderId = 0;
  const protectMath = (block: string) => {
    const placeholder = `AGPROTMATH${mathPlaceholderId++}AGPROT`;
    protectedMathBlocks.set(placeholder, block);
    return placeholder;
  };

  let out = markdown;
  out = out.replace(/\$\$[\s\S]+?\$\$/g, protectMath);
  out = out.replace(/\$(?!\$)(?:\\.|[^$\\\n])+\$/g, protectMath);
  return { text: out, protectedMathBlocks };
}

function restoreProtectedBlocks(text: string, blocks: Map<string, string>) {
  let out = text;
  for (const [placeholder, original] of blocks.entries()) {
    out = out.split(placeholder).join(original);
  }
  return out;
}

function protectCodeHtml(html: string) {
  const protectedBlocks = new Map<string, string>();
  let placeholderId = 0;
  const protectBlock = (block: string) => {
    const placeholder = `AGPROTCODE${placeholderId++}AGPROT`;
    protectedBlocks.set(placeholder, block);
    return placeholder;
  };

  return {
    html: html.replace(/<(pre|code)[^>]*>[\s\S]*?<\/\1>/g, protectBlock),
    protectedBlocks,
  };
}

function renderKatex(html: string) {
  let out = html;
  out = out.replace(/\$\$([\s\S]+?)\$\$/g, (_match: string, latex: string) => {
    const cleaned = latex
      .trim()
      .replace(/\\\\([A-Za-z_])/g, "\\$1")
      .replace(/\\\\([,;:.!])/g, "\\$1");
    try {
      return `<span class="katex-display">${katex.renderToString(cleaned, {
        displayMode: true,
        throwOnError: false,
      })}</span>`;
    } catch (e: any) {
      return `<span class="katex-error">${String(e?.message ?? e)}</span>`;
    }
  });

  out = out.replace(/\$([^$]+?)\$/g, (_match: string, latex: string) => {
    const cleaned = latex
      .trim()
      .replace(/\\\\([A-Za-z_])/g, "\\$1")
      .replace(/\\\\([,;:.!])/g, "\\$1");
    try {
      return katex.renderToString(cleaned, { displayMode: false, throwOnError: false });
    } catch (e: any) {
      return `<span class="katex-error">${String(e?.message ?? e)}</span>`;
    }
  });

  return out;
}

export async function renderMarkdownToHtml(
  markdown: string,
  opts: MarkdownPipelineOptions = {}
): Promise<MarkdownRenderModel> {
  let processedText = markdown ?? "";
  const staticArrowgramHtmlById = new Map<string, string>();
  const staticMermaidHtmlById = new Map<string, string>();

  const vegaRegex = /<div class="vega-lite"([^>]*)>([\s\S]*?)<\/div>/g;
  const vegaMatches = Array.from(processedText.matchAll(vegaRegex));
  const vegaRuntime = await loadVegaRuntime();
  const vegaResults = await Promise.all(
    vegaMatches.map(async (match) => {
      if (!vegaRuntime) {
        return {
          original: match[0],
          replacement: '<div class="vega-error">Chart rendering unavailable in this environment.</div>',
        };
      }

      try {
        const spec = JSON.parse(match[2].trim());
        const vegaSpec = (vegaRuntime.vegaLite as any).compile(spec).spec;
        const view = new (vegaRuntime.vega as any).View((vegaRuntime.vega as any).parse(vegaSpec), {
          renderer: "svg",
        });
        const svg = await view.toSVG();
        return { original: match[0], replacement: `<div class="vega-container"${match[1]}>${svg}</div>` };
      } catch (e: any) {
        return {
          original: match[0],
          replacement: `<div class="vega-error">Chart Error: ${String(e?.message ?? e)}</div>`,
        };
      }
    })
  );
  for (const result of vegaResults) processedText = processedText.replace(result.original, result.replacement);

  const mermaid = await loadMermaidRuntime();
  if (mermaid) (mermaid as any).initialize({ startOnLoad: false, theme: "base" });

  const mermaidRegex = /<div class="mermaid"([^>]*)>([\s\S]*?)<\/div>/g;
  const mermaidMatches = Array.from(processedText.matchAll(mermaidRegex));
  const mermaidResults = await Promise.all(
    mermaidMatches.map(async (match, i) => {
      if (!mermaid) {
        return {
          original: match[0],
          replacement: '<div class="mermaid-error">Diagram rendering unavailable in this environment.</div>',
        };
      }

      const id = `${opts.idPrefix ?? "ag"}-mermaid-${Date.now()}-${i}`;
      try {
        const { svg } = await (mermaid as any).render(id, match[2].trim());
        const fullHtml = `<div class="mermaid-container"${match[1]}>${svg}</div>`;
        staticMermaidHtmlById.set(id, fullHtml);
        return { original: match[0], replacement: `<div id="${id}" class="mermaid-hydrate-target"></div>` };
      } catch {
        return { original: match[0], replacement: '<div class="mermaid-error">Diagram Error</div>' };
      }
    })
  );
  for (const result of mermaidResults) processedText = processedText.replace(result.original, result.replacement);

  const arrowgrams: ArrowgramHydrationTarget[] = [];
  let agCounter = 0;
  const arrowgramRegex = /<div class="arrowgram"([^>]*)>([\s\S]*?)<\/div>/g;
  processedText = processedText.replace(arrowgramRegex, (_match, _attrs, content) => {
    const id = `${opts.idPrefix ?? "ag"}-arrowgram-${Date.now()}-${agCounter++}`;
    const spec = String(content ?? "").trim();
    arrowgrams.push({ id, spec });

    try {
      const staticHtml = ReactDOMServer.renderToStaticMarkup(<ArrowGramStatic spec={spec} id={id} />);
      staticArrowgramHtmlById.set(id, staticHtml);
      return `<div id="${id}" class="arrowgram-hydrate-target"></div>`;
    } catch (e: any) {
      return `<div id="${id}" class="arrowgram-hydrate-target"><div class="arrowgram-error">Diagram Error: ${String(
        e?.message ?? e
      )}</div></div>`;
    }
  });

  const protectedMath = protectMathBlocks(processedText);
  const converter = new showdown.Converter({
    metadata: true,
    noHeaderId: true,
    literalMidWordUnderscores: true,
    tables: true,
  });
  let html = converter.makeHtml(protectedMath.text);
  const metadata = (converter.getMetadata() as any) ?? {};

  html = restoreProtectedBlocks(html, protectedMath.protectedMathBlocks);

  const protectedCode = protectCodeHtml(html);
  html = renderKatex(protectedCode.html);
  html = restoreProtectedBlocks(html, protectedCode.protectedBlocks);

  let safe = sanitizeHtml(html);
  for (const [id, staticHtml] of staticArrowgramHtmlById.entries()) {
    const needle = `<div id="${id}" class="arrowgram-hydrate-target"></div>`;
    const replacement = `<div id="${id}" class="arrowgram-hydrate-target">${staticHtml}</div>`;
    safe = safe.split(needle).join(replacement);
  }
  for (const [id, staticHtml] of staticMermaidHtmlById.entries()) {
    const needle = `<div id="${id}" class="mermaid-hydrate-target"></div>`;
    safe = safe.split(needle).join(staticHtml);
  }

  if (opts.includeTitleBlock) {
    const escapeHtml = (input: unknown) =>
      String(input ?? "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
    const titleBlockHtml = `<div class="title-block">${
      metadata.title ? `<div class="title">${escapeHtml(metadata.title)}</div>` : ""
    }${metadata.authors ? `<div class="authors">${escapeHtml(metadata.authors)}</div>` : ""}</div>`;
    return {
      html: `${titleBlockHtml}<div class="paper-body">${safe}</div>`,
      metadata,
      arrowgrams: opts.arrowgrams?.mode === "static-only" ? [] : arrowgrams,
    };
  }

  return {
    html: safe,
    metadata,
    arrowgrams: opts.arrowgrams?.mode === "static-only" ? [] : arrowgrams,
  };
}
