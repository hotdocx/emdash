import { spawn } from 'node:child_process';
import fs from 'node:fs';
import net from 'node:net';
import process from 'node:process';
import { chromium } from 'playwright';

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function isPortOpen(host, port) {
  return new Promise((resolve) => {
    const socket = new net.Socket();
    const onError = () => {
      socket.destroy();
      resolve(false);
    };
    socket.setTimeout(500);
    socket.once('error', onError);
    socket.once('timeout', onError);
    socket.connect(port, host, () => {
      socket.end();
      resolve(true);
    });
  });
}

async function findOpenPort(host, startPort, attempts) {
  for (let i = 0; i < attempts; i++) {
    const port = startPort + i;
    const server = net.createServer();
    const ok = await new Promise((resolve) => {
      server.once('error', () => resolve(false));
      server.listen(port, host, () => resolve(true));
    });
    if (ok) {
      await new Promise((resolve) => server.close(resolve));
      return port;
    }
  }
  throw new Error(`Could not find open port starting at ${startPort}`);
}

function killProcess(child) {
  if (!child || child.killed) return;
  child.kill('SIGTERM');
  setTimeout(() => {
    if (!child.killed) child.kill('SIGKILL');
  }, 2000).unref();
}

function discoverPaperRuns() {
  const publicDir = new URL('../public/', import.meta.url);
  const files = fs
    .readdirSync(publicDir, { withFileTypes: true })
    .filter((d) => d.isFile() && /^index(?:_[A-Za-z0-9]+)*\.md$/.test(d.name))
    .map((d) => d.name)
    .sort((a, b) => {
      if (a === 'index.md') return -1;
      if (b === 'index.md') return 1;
      if (a === 'index_0.md') return -1;
      if (b === 'index_0.md') return 1;
      return a.localeCompare(b);
    });

  if (files.length === 0) {
    throw new Error('No public/index*.md paper files found');
  }

  return files.map((file) => ({
    name: file === 'index.md' ? 'index.md (default)' : file,
    query: file === 'index.md' ? '' : `?paper=${encodeURIComponent(file)}`,
  }));
}

async function findRenderedRawMarkdownTables(page) {
  return page.evaluate(() => {
    const root = document.querySelector('.paper-body');
    if (!root) return [];

    const clone = root.cloneNode(true);
    clone.querySelectorAll('pre, code, table, script, style').forEach((el) => el.remove());
    const lines = (clone.textContent || '')
      .split(/\n/)
      .map((line) => line.trim())
      .filter(Boolean);

    const rawTables = [];
    for (let i = 0; i < lines.length - 1; i++) {
      const current = lines[i];
      const next = lines[i + 1];
      const looksLikePipeRow = /^\|.+\|$/.test(current);
      const looksLikeSeparator = /^\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)+\|?$/.test(next);
      if (looksLikePipeRow && looksLikeSeparator) rawTables.push(current);
    }
    return rawTables;
  });
}

async function main() {
  const host = '127.0.0.1';
  const port = await findOpenPort(host, 4173, 30);
  const baseUrl = `http://${host}:${port}/`;

  // Start a preview server for the built output.
  const preview = spawn(
    'npm',
    ['run', 'preview', '--', '--host', host, '--port', String(port), '--strictPort'],
    { stdio: 'inherit', shell: false }
  );

  const onExit = () => killProcess(preview);
  process.on('SIGINT', onExit);
  process.on('SIGTERM', onExit);

  // Wait for the port to become reachable.
  const deadline = Date.now() + 30_000;
  while (Date.now() < deadline) {
    if (await isPortOpen(host, port)) break;
    await sleep(200);
  }
  if (!(await isPortOpen(host, port))) {
    killProcess(preview);
    throw new Error(`Preview server did not start on ${baseUrl}`);
  }

  const browser = await chromium.launch({ headless: true });
  const runs = discoverPaperRuns();

  const errors = [];
  const warnings = [];
  const requestFailures = [];

  for (const run of runs) {
    const page = await browser.newPage();

    page.on('pageerror', (err) => {
      errors.push(`[${run.name}] pageerror: ${err.message || String(err)}`);
    });

    page.on('console', (msg) => {
      const type = msg.type();
      const text = msg.text();
      if (type === 'error') errors.push(`[${run.name}] console.error: ${text}`);
      if (type === 'warning') {
        // Treat KaTeX strict-mode warnings as failures: they indicate malformed TeX input.
        if (text.includes('LaTeX-incompatible input') || text.includes('[mathVsTextAccents]')) {
          errors.push(`[${run.name}] console.warn (katex): ${text}`);
        } else {
          warnings.push(`[${run.name}] console.warn: ${text}`);
        }
      }
    });

    page.on('requestfailed', (req) => {
      const failure = req.failure();
      requestFailures.push(`[${run.name}] requestfailed: ${req.url()} ${failure?.errorText || ''}`.trim());
    });

    // Navigate and wait for paged.js to render pages.
    await page.goto(`${baseUrl}${run.query}`, { waitUntil: 'domcontentloaded' });
    await page.waitForSelector('.pagedjs_pages', { timeout: 30_000 });
    await sleep(1500);

    const rawMarkdownTables = await findRenderedRawMarkdownTables(page);
    if (rawMarkdownTables.length) {
      errors.push(
        `[${run.name}] raw Markdown table syntax rendered as text: ${rawMarkdownTables.slice(0, 3).join(' / ')}`
      );
    }

    await page.close();
  }

  await browser.close();
  killProcess(preview);

  if (requestFailures.length) {
    console.error('Console check: network failures detected:');
    for (const line of requestFailures) console.error(`- ${line}`);
    process.exit(1);
  }

  if (errors.length) {
    console.error('Console check: JavaScript errors detected:');
    for (const line of errors) console.error(`- ${line}`);
    process.exit(1);
  }

  // Warnings are reported but do not fail by default (pagedjs/mermaid can be chatty).
  if (warnings.length) {
    console.log(`Console check: warnings=${warnings.length} (not failing)`);
  }

  console.log('Console check: OK (no console errors / pageerrors / request failures)');
}

main().catch((e) => {
  console.error(`Console check failed: ${e?.message || e}`);
  process.exit(1);
});
