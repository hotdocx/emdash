import { spawn } from 'node:child_process';
import net from 'node:net';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const PRINT_ROOT = fileURLToPath(new URL('../', import.meta.url));

export function sleep(milliseconds) {
  return new Promise((resolve) => setTimeout(resolve, milliseconds));
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
  for (let offset = 0; offset < attempts; offset += 1) {
    const port = startPort + offset;
    const server = net.createServer();
    const available = await new Promise((resolve) => {
      server.once('error', () => resolve(false));
      server.listen(port, host, () => resolve(true));
    });
    if (available) {
      await new Promise((resolve) => server.close(resolve));
      return port;
    }
  }
  throw new Error('Could not find an open port starting at ' + startPort);
}

function childHasExited(child) {
  return !child || child.exitCode !== null || child.signalCode !== null;
}

function signalProcessTree(child, signal) {
  if (childHasExited(child) || !child.pid) return;
  try {
    if (process.platform === 'win32') {
      child.kill(signal);
    } else {
      process.kill(-child.pid, signal);
    }
  } catch (error) {
    if (error.code !== 'ESRCH') throw error;
  }
}

async function waitForChildExit(child, timeoutMs) {
  if (childHasExited(child)) return true;
  return new Promise((resolve) => {
    const onExit = () => finish(true);
    const timer = setTimeout(() => finish(false), timeoutMs);
    const finish = (exited) => {
      clearTimeout(timer);
      child.off('exit', onExit);
      resolve(exited);
    };
    child.once('exit', onExit);
  });
}

async function stopProcessTree(child) {
  if (childHasExited(child)) return;
  signalProcessTree(child, 'SIGTERM');
  if (await waitForChildExit(child, 2000)) return;
  signalProcessTree(child, 'SIGKILL');
  await waitForChildExit(child, 2000);
}

export async function withTimeout(operation, timeoutMs, label) {
  let timer;
  try {
    return await Promise.race([
      operation,
      new Promise((_, reject) => {
        timer = setTimeout(
          () => reject(new Error(label + ' exceeded ' + timeoutMs + 'ms')),
          timeoutMs
        );
      }),
    ]);
  } finally {
    clearTimeout(timer);
  }
}

export async function waitForCompletedPagination(page, timeoutMs = 30000) {
  const selector = '.preview-content-area[data-pagination-complete="true"]';
  await page.waitForSelector(selector, { timeout: timeoutMs });
  await page.evaluate(() => document.fonts.ready);

  const readState = () => page.evaluate((completedSelector) => {
    const container = document.querySelector(completedSelector);
    return {
      declared: Number(container?.getAttribute('data-page-count') || 0),
      actual: document.querySelectorAll('.pagedjs_page').length,
      hasLoadingIndicator: Boolean(document.querySelector('.loading-indicator')),
    };
  }, selector);
  const first = await readState();
  await sleep(200);
  const second = await readState();
  if (
    first.hasLoadingIndicator || second.hasLoadingIndicator ||
    first.declared < 1 || first.actual !== first.declared ||
    second.declared !== first.declared || second.actual !== first.actual
  ) {
    throw new Error(
      'Completed pagination marker is inconsistent: first=' +
      JSON.stringify(first) + ', second=' + JSON.stringify(second)
    );
  }
  return second.actual;
}

export async function startPreviewServer(options = {}) {
  const host = options.host ?? '127.0.0.1';
  const startPort = options.startPort ?? 4173;
  const attempts = options.attempts ?? 30;
  const startupTimeoutMs = options.startupTimeoutMs ?? 30000;
  const port = await findOpenPort(host, startPort, attempts);
  const baseUrl = 'http://' + host + ':' + port + '/';
  const child = spawn(
    'npm',
    ['run', 'preview', '--', '--host', host, '--port', String(port), '--strictPort'],
    {
      cwd: PRINT_ROOT,
      stdio: options.stdio ?? 'inherit',
      shell: false,
      detached: process.platform !== 'win32',
    }
  );

  const stop = async () => stopProcessTree(child);
  try {
    const startupDeadline = Date.now() + startupTimeoutMs;
    while (Date.now() < startupDeadline && !childHasExited(child)) {
      if (await isPortOpen(host, port)) break;
      await sleep(200);
    }
    if (!(await isPortOpen(host, port))) {
      throw new Error('Preview server did not start on ' + baseUrl);
    }
    return { baseUrl, child, host, port, stop };
  } catch (error) {
    await stop().catch(() => {});
    throw error;
  }
}
