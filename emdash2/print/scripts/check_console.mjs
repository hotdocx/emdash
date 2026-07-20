import process from 'node:process';
import { chromium } from 'playwright';
import {
  documentQuery,
  selectDocuments,
} from './document_registry.mjs';
import {
  startPreviewServer,
  waitForCompletedPagination,
  withTimeout,
} from './preview_runtime.mjs';

async function findRenderedRawMarkdownTables(page) {
  return page.evaluate(() => {
    const roots = [...document.querySelectorAll('.paper-body')];
    if (roots.length === 0) return [];

    const clone = document.createElement('div');
    for (const root of roots) clone.append(root.cloneNode(true));
    clone.querySelectorAll('pre, code, table, script, style').forEach((element) => element.remove());
    const lines = (clone.textContent || '')
      .split(/\n/)
      .map((line) => line.trim())
      .filter(Boolean);

    const rawTables = [];
    for (let index = 0; index < lines.length - 1; index += 1) {
      const current = lines[index];
      const next = lines[index + 1];
      const looksLikePipeRow = /^\|.+\|$/.test(current);
      const looksLikeSeparator =
        /^\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?$/.test(next);
      if (looksLikePipeRow && looksLikeSeparator) rawTables.push(current);
    }
    return rawTables;
  });
}

async function auditHorizontalOverflow(page) {
  return page.evaluate(() => {
    const selector = [
      'p', 'li', 'pre', 'table', 'blockquote', 'h1', 'h2', 'h3',
      '.katex-display', '.mermaid-container', '.vega-container',
      '.arrowgram-container',
    ].join(',');
    const tolerance = 2.5;
    const issues = [];
    const pages = [...document.querySelectorAll('.pagedjs_page_content')];
    pages.forEach((content, pageIndex) => {
      const contentRect = content.getBoundingClientRect();
      for (const element of content.querySelectorAll(selector)) {
        const visibleRects = [...element.getClientRects()].filter((rect) =>
          rect.width > 0 && rect.height > 0 &&
          rect.right > contentRect.left && rect.left < contentRect.right &&
          rect.bottom > contentRect.top && rect.top < contentRect.bottom
        );
        if (visibleRects.length === 0) continue;
        const left = Math.max(
          0,
          ...visibleRects.map((rect) => contentRect.left - rect.left)
        );
        const right = Math.max(
          0,
          ...visibleRects.map((rect) => rect.right - contentRect.right)
        );
        if (left <= tolerance && right <= tolerance) continue;
        const identifier = [
          element.tagName.toLowerCase(),
          ...String(element.className || '').split(/\s+/).filter(Boolean).slice(0, 2),
        ].join('.');
        const style = getComputedStyle(element);
        const excerpt = (element.textContent || '').replace(/\s+/g, ' ').trim().slice(0, 90);
        issues.push(
          'page ' + (pageIndex + 1) + ' ' + identifier +
          ' overflows left=' + left.toFixed(1) + 'px right=' + right.toFixed(1) +
          'px position=' + style.position + ' overflow-x=' + style.overflowX +
          ' text=' + JSON.stringify(excerpt)
        );
        if (issues.length >= 12) return;
      }
    });
    return issues;
  });
}

async function auditRenderedBook(page) {
  return page.evaluate(() => {
    const issues = [];
    const root = document.querySelector('.pagedjs_pages');
    if (!root) return ['paged output root is missing'];

    const parseColor = (value) => {
      const channels = value.match(/[\d.]+/g)?.map(Number) ?? [];
      if (channels.length < 3) return null;
      return {
        red: channels[0],
        green: channels[1],
        blue: channels[2],
        alpha: channels.length > 3 ? channels[3] : 1,
      };
    };
    const luminance = (color) => {
      const channel = (value) => {
        const normalized = value / 255;
        return normalized <= 0.04045
          ? normalized / 12.92
          : ((normalized + 0.055) / 1.055) ** 2.4;
      };
      return 0.2126 * channel(color.red) +
        0.7152 * channel(color.green) +
        0.0722 * channel(color.blue);
    };
    const contrast = (foreground, background) => {
      const light = Math.max(luminance(foreground), luminance(background));
      const dark = Math.min(luminance(foreground), luminance(background));
      return (light + 0.05) / (dark + 0.05);
    };
    const backgroundFor = (element) => {
      let current = element;
      while (current) {
        const color = parseColor(getComputedStyle(current).backgroundColor);
        if (color && color.alpha > 0.99) return color;
        current = current.parentElement;
      }
      return { red: 255, green: 255, blue: 255, alpha: 1 };
    };

    for (const image of root.querySelectorAll('img')) {
      if (!(image.getAttribute('alt') || '').trim()) {
        issues.push('rendered image has no non-empty alt text');
      }
    }
    for (const diagram of root.querySelectorAll(
      '.arrowgram-container, .mermaid-container, .vega-container'
    )) {
      if (diagram.getAttribute('role') !== 'img') {
        issues.push('rendered diagram is missing role="img"');
      }
      if (!(diagram.getAttribute('aria-label') || '').trim()) {
        issues.push('rendered diagram is missing a non-empty aria-label');
      }
    }
    for (const link of root.querySelectorAll('a[href^="#"]')) {
      const href = link.getAttribute('href') || '';
      if (href === '#' || href.length < 2) continue;
      let id;
      try {
        id = decodeURIComponent(href.slice(1));
      } catch {
        issues.push('internal link has invalid percent encoding: ' + href);
        continue;
      }
      if (!document.getElementById(id)) {
        issues.push('rendered internal link has no target: ' + href);
      }
    }
    for (const element of root.querySelectorAll(
      '.document-book .paper-body p, .document-book .paper-body li, ' +
      '.document-book .paper-body a, .document-book .paper-body blockquote, ' +
      '.document-book .edition'
    )) {
      const foreground = parseColor(getComputedStyle(element).color);
      const background = backgroundFor(element);
      if (foreground && contrast(foreground, background) < 4.5) {
        issues.push(
          'text contrast is below 4.5:1 for ' + element.tagName.toLowerCase() +
          (element.className ? '.' + String(element.className).trim().replace(/\s+/g, '.') : '')
        );
      }
    }
    for (const link of root.querySelectorAll('.document-book .paper-body a')) {
      if (!getComputedStyle(link).textDecorationLine.includes('underline')) {
        issues.push('book link is distinguished only by color');
      }
    }
    if ((root.textContent || '').includes('\uFFFD')) {
      issues.push('rendered text contains the Unicode replacement character');
    }
    return [...new Set(issues)].slice(0, 20);
  });
}

async function auditBookSourceStarts(page) {
  return page.evaluate(() => {
    const issues = [];
    const starts = [...document.querySelectorAll(
      '.book-source-section[data-book-section]:not([data-split-from])'
    )];
    const numbered = starts.map((section) => ({
      section,
      number: Number(section.getAttribute('data-book-section')),
    }));
    const numbers = numbered.map(({ number }) => number);
    const unique = new Set(numbers);
    const maximum = Math.max(0, ...numbers);

    if (starts.length < 2) issues.push('fewer than two generated source starts rendered');
    if (unique.size !== starts.length) issues.push('a generated source start is duplicated');
    for (let expected = 1; expected <= maximum; expected += 1) {
      if (!unique.has(expected)) issues.push('generated source start ' + expected + ' is missing');
    }

    const pages = [...document.querySelectorAll('.pagedjs_page')];
    // Paged.js leaves a small leading-line inset for the source anchor
    // paragraph (14px normally, 24px on the edition leaf). Anything beyond
    // this bounded top matter indicates that the source began mid-page.
    const tolerance = 32;
    for (const { section, number } of numbered) {
      const pagedPage = section.closest('.pagedjs_page');
      const content = pagedPage?.querySelector('.pagedjs_page_content');
      if (!pagedPage || !content) {
        issues.push('source ' + number + ' is outside a paged content box');
        continue;
      }
      const offset = section.getBoundingClientRect().top - content.getBoundingClientRect().top;
      if (Math.abs(offset) > tolerance) {
        issues.push(
          'source ' + number + ' begins ' + offset.toFixed(1) +
          'px below the top of page ' + (pages.indexOf(pagedPage) + 1)
        );
      }
    }
    return issues.slice(0, 20);
  });
}

async function runDocument(
  page,
  baseUrl,
  document,
  errors,
  warnings,
  requestFailures,
  externalRequests
) {
  const label = document.file;
  const localOrigin = new URL(baseUrl).origin;

  page.on('pageerror', (error) => {
    errors.push('[' + label + '] pageerror: ' + (error.message || String(error)));
  });
  page.on('console', (message) => {
    const type = message.type();
    const text = message.text();
    if (type === 'error') errors.push('[' + label + '] console.error: ' + text);
    if (type === 'warning') {
      if (text.includes('LaTeX-incompatible input') || text.includes('[mathVsTextAccents]')) {
        errors.push('[' + label + '] console.warn (katex): ' + text);
      } else {
        warnings.push('[' + label + '] console.warn: ' + text);
      }
    }
  });
  page.on('requestfailed', (request) => {
    const failure = request.failure();
    requestFailures.push(
      '[' + label + '] requestfailed: ' + request.url() + ' ' +
      (failure?.errorText || '')
    );
  });
  page.on('request', (request) => {
    const rawUrl = request.url();
    let parsed;
    try {
      parsed = new URL(rawUrl);
    } catch {
      externalRequests.push('[' + label + '] malformed request URL: ' + rawUrl);
      return;
    }
    if (['data:', 'blob:', 'about:'].includes(parsed.protocol)) return;
    if (parsed.origin !== localOrigin) {
      externalRequests.push('[' + label + '] external request: ' + rawUrl);
    }
  });

  const url = baseUrl + documentQuery(document);
  await page.goto(url, { waitUntil: 'domcontentloaded' });
  const pageCount = await waitForCompletedPagination(
    page,
    Math.min(document.timeoutMs, 30000)
  );

  const rawMarkdownTables = await findRenderedRawMarkdownTables(page);
  if (rawMarkdownTables.length > 0) {
    errors.push(
      '[' + label + '] raw Markdown table syntax rendered as text: ' +
      rawMarkdownTables.slice(0, 3).join(' / ')
    );
  }

  const renderErrors = await page.locator(
    '.katex-error, .vega-error, .mermaid-error, .arrowgram-error'
  ).allTextContents();
  if (renderErrors.length > 0) {
    errors.push(
      '[' + label + '] rendered error box: ' +
      renderErrors.slice(0, 3).join(' / ')
    );
  }

  const overflowIssues = await auditHorizontalOverflow(page);
  for (const overflow of overflowIssues) {
    errors.push('[' + label + '] horizontal overflow: ' + overflow);
  }

  if (document.kind === 'book') {
    const accessibilityIssues = await auditRenderedBook(page);
    for (const accessibilityIssue of accessibilityIssues) {
      errors.push('[' + label + '] accessibility/link audit: ' + accessibilityIssue);
    }
    const sourceStartIssues = await auditBookSourceStarts(page);
    for (const sourceStartIssue of sourceStartIssues) {
      errors.push('[' + label + '] source pagination audit: ' + sourceStartIssue);
    }
  }

  if (pageCount < 1) errors.push('[' + label + '] pagination produced no pages');
  console.log('render check: file=' + label + ', pages=' + pageCount + ', status=OK');
}

async function main() {
  const documents = selectDocuments(process.argv.slice(2), 'render');
  let preview = null;
  let browser = null;
  let cleanupPromise = null;

  const cleanup = () => {
    if (!cleanupPromise) {
      cleanupPromise = (async () => {
        if (browser) {
          await browser.close().catch(() => {});
          browser = null;
        }
        if (preview) {
          await preview.stop().catch(() => {});
          preview = null;
        }
      })();
    }
    return cleanupPromise;
  };

  const onSignal = (signal, exitCode) => {
    void cleanup().finally(() => {
      console.error('Console check interrupted by ' + signal);
      process.exit(exitCode);
    });
  };
  const onSigint = () => onSignal('SIGINT', 130);
  const onSigterm = () => onSignal('SIGTERM', 143);
  process.once('SIGINT', onSigint);
  process.once('SIGTERM', onSigterm);

  try {
    preview = await startPreviewServer();
    const { baseUrl } = preview;

    browser = await chromium.launch({ headless: true });
    const errors = [];
    const warnings = [];
    const requestFailures = [];
    const externalRequests = [];

    for (const document of documents) {
      const page = await browser.newPage();
      page.setDefaultTimeout(Math.min(document.timeoutMs, 30000));
      page.setDefaultNavigationTimeout(Math.min(document.timeoutMs, 30000));
      try {
        await withTimeout(
          runDocument(
            page,
            baseUrl,
            document,
            errors,
            warnings,
            requestFailures,
            externalRequests
          ),
          document.timeoutMs,
          document.file + ' render'
        );
      } finally {
        await page.close({ runBeforeUnload: false }).catch(() => {});
      }
    }

    if (externalRequests.length > 0) {
      console.error('Console check: external network requests detected:');
      for (const line of externalRequests) console.error('- ' + line.trim());
      throw new Error('external network requests=' + externalRequests.length);
    }

    if (requestFailures.length > 0) {
      console.error('Console check: network failures detected:');
      for (const line of requestFailures) console.error('- ' + line.trim());
      throw new Error('network request failures=' + requestFailures.length);
    }
    if (errors.length > 0) {
      console.error('Console check: rendering errors detected:');
      for (const line of errors) console.error('- ' + line);
      throw new Error('rendering errors=' + errors.length);
    }
    if (warnings.length > 0) {
      console.log('Console check: warnings=' + warnings.length + ' (not failing)');
    }
    console.log(
      'Console check: OK (' + documents.length +
      ' document(s), no console/page/request/render errors)'
    );
  } finally {
    process.off('SIGINT', onSigint);
    process.off('SIGTERM', onSigterm);
    await cleanup();
  }
}

main().catch((error) => {
  console.error('Console check failed: ' + (error?.message || error));
  process.exitCode = 1;
});
