import { View, parse } from 'vega';
import { compile } from 'vega-lite';
import { calculateFamily, sampleFamily, curveSpec, viewports, type FamilyCalculation } from './model.js';
import { createPlotSlot } from './plot-slot.js';

function element<T extends HTMLElement>(id: string): T {
  const found = document.getElementById(id);
  if (!found) throw new Error(`Missing element: ${id}`);
  return found as T;
}

const form = element<HTMLFormElement>('controls');
const parameter = element<HTMLInputElement>('parameter');
const viewport = element<HTMLSelectElement>('viewport');
const chart = element('chart');
const plotStatus = element('plot-status');
const exact = element('exact');
const inputError = element('input-error');
const slot = createPlotSlot();
let calculation: FamilyCalculation | undefined;

function clearPlot() {
  const revision = slot.invalidate();
  chart.replaceChildren();
  delete chart.dataset.source;
  chart.setAttribute('aria-busy', 'false');
  return revision;
}

async function render(calculated: FamilyCalculation) {
  const revision = clearPlot();
  plotStatus.textContent = 'Sampling the current curves…';
  chart.setAttribute('aria-busy', 'true');
  try {
    const samples = sampleFamily(calculated, viewports[viewport.value]);
    const segments = samples.curves.reduce((count, curve) => count + curve.segments.length, 0);
    const omitted = samples.curves.reduce((count, curve) => count + curve.ambiguousCells, 0);
    const spec = curveSpec(samples, Math.max(240, Math.min(860, chart.clientWidth)));
    const shown = await slot.show(revision, async () => {
      const container = document.createElement('div');
      const view = new View(parse(compile(spec).spec), { renderer: 'svg', container });
      try { await view.runAsync(); } catch (error) { view.finalize(); throw error; }
      return {
        mount() {
          chart.replaceChildren(container);
          chart.dataset.source = samples.source;
        },
        dispose() { view.finalize(); container.remove(); },
      };
    });
    if (shown) {
      plotStatus.textContent = `${segments} sampled segments · ${omitted} ambiguous cells omitted`;
      chart.setAttribute('aria-busy', 'false');
    }
  } catch (error) {
    if (!slot.isCurrent(revision)) return;
    plotStatus.textContent = `Plot unavailable: ${error instanceof Error ? error.message : String(error)}`;
    chart.setAttribute('aria-busy', 'false');
  }
}

function update() {
  clearPlot();
  calculation = undefined;
  exact.hidden = true;
  inputError.textContent = '';
  parameter.removeAttribute('aria-invalid');
  try {
    calculation = calculateFamily(parameter.value);
    exact.hidden = false;
    exact.dataset.source = calculation.source;
    element('current-parameter').textContent = `c = ${calculation.parameter}`;
    element('generators').textContent = calculation.generators.map((value, index) => `f${index + 1} = ${value}`).join('\n');
    element('query').textContent = calculation.query;
    element('identity').textContent = calculation.identity;
    void render(calculation);
  } catch {
    delete exact.dataset.source;
    inputError.textContent = 'Enter an integer or fraction with a positive denominator, such as 1/2 (up to 512 characters).';
    parameter.setAttribute('aria-invalid', 'true');
    plotStatus.textContent = 'Apply a valid parameter to draw the curves.';
  }
}

form.addEventListener('submit', event => { event.preventDefault(); update(); });
parameter.addEventListener('input', () => {
  clearPlot();
  calculation = undefined;
  exact.hidden = true;
  delete exact.dataset.source;
  inputError.textContent = '';
  parameter.removeAttribute('aria-invalid');
  plotStatus.textContent = 'Apply this parameter to update the calculation.';
});
viewport.addEventListener('change', () => { if (calculation) void render(calculation); });
document.querySelectorAll<HTMLButtonElement>('[data-parameter]').forEach(button => {
  button.addEventListener('click', () => { parameter.value = button.dataset.parameter!; update(); });
});
let resizeTimer: ReturnType<typeof setTimeout> | undefined;
window.addEventListener('resize', () => {
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => { if (calculation) void render(calculation); }, 80);
});
window.addEventListener('pagehide', () => { clearTimeout(resizeTimer); slot.invalidate(); });
update();
