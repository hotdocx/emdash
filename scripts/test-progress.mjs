import { relative } from 'node:path';
import { performance } from 'node:perf_hooks';
import { Transform } from 'node:stream';

// Runs in node --test's parent, separately from CPU-bound test workers.
// Declaration-ordered test:start/pass/fail events are intentionally not used.
const interval = Number(process.env.EMDASH_TEST_PROGRESS_INTERVAL_MS ?? 30_000);
if (!Number.isSafeInteger(interval) || interval < 50 || interval > 3_600_000) {
  throw new Error('EMDASH_TEST_PROGRESS_INTERVAL_MS must be an integer from 50 to 3600000');
}
const started = performance.now();
let lastAt = started;
let last = 'waiting for execution events';
let completed = 0;
let first = true;
const label = (data) => `${JSON.stringify(data.name)} (${data.file ? relative(process.cwd(), data.file) : 'unknown file'}:${data.line ?? '?'})`;

const reporter = new Transform({
  writableObjectMode: true,
  transform({ type, data }, _encoding, callback) {
    let line;
    if (type === 'test:dequeue') {
      last = `dequeued ${label(data)}`;
      lastAt = performance.now();
      if (first) {
        line = `[progress] ${last}\n`;
        first = false;
      }
    } else if (type === 'test:complete') {
      completed += 1;
      const outcome = data.skip ? 'skipped' : data.todo ? 'todo'
        : data.details.passed ? 'passed' : 'not-passed';
      last = `completed ${outcome} ${label(data)}`;
      lastAt = performance.now();
      if (!data.details.passed || data.details.duration_ms >= 5_000) {
        line = `[progress] ${last}; duration=${data.details.duration_ms.toFixed(1)}ms\n`;
      }
    }
    callback(null, line);
  },
  final(callback) {
    clearInterval(timer);
    callback();
  },
});

const timer = setInterval(() => {
  const now = performance.now();
  reporter.push(`[progress] parent alive; elapsed=${((now - started) / 1000).toFixed(1)}s; completed_events=${completed}; last=${last}; event_age=${((now - lastAt) / 1000).toFixed(1)}s\n`);
}, interval);
timer.unref();
reporter.on('close', () => clearInterval(timer));

export default reporter;
