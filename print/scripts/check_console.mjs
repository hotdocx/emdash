import { spawn } from 'node:child_process';
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

async function main() {
  const host = '127.0.0.1';
  const port = await findOpenPort(host, 4173, 30);
  const url = `http://${host}:${port}/`;

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
    throw new Error(`Preview server did not start on ${url}`);
  }

  const browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();

  const errors = [];
  const warnings = [];
  const requestFailures = [];

  page.on('pageerror', (err) => {
    errors.push(`pageerror: ${err.message || String(err)}`);
  });

  page.on('console', (msg) => {
    const type = msg.type();
    const text = msg.text();
    if (type === 'error') errors.push(`console.error: ${text}`);
    if (type === 'warning') warnings.push(`console.warn: ${text}`);
  });

  page.on('requestfailed', (req) => {
    const failure = req.failure();
    requestFailures.push(`requestfailed: ${req.url()} ${failure?.errorText || ''}`.trim());
  });

  // Navigate and wait for paged.js to render pages.
  await page.goto(url, { waitUntil: 'domcontentloaded' });
  await page.waitForSelector('.pagedjs_pages', { timeout: 30_000 });
  await sleep(1500);

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

