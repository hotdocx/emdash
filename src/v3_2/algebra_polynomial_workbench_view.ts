/** Standalone result view; all formulas and curves come from the workspace. */

import {
    AlgebraPolynomialWorkspace, assertAlgebraPolynomialWorkbenchCurrent,
    computeAlgebraPolynomialWorkbench, prepareAlgebraPolynomialWorkbenchGoal
} from './algebra_polynomial_workbench';
import {
    algebraWorkbenchEscapeHtml as escape, renderAlgebraPolynomialCurveSvg
} from './algebra_polynomial_plot';
import { AlgebraRationalPolynomial } from './algebra_ideal_witness';

const displayPolynomial = (polynomial: AlgebraRationalPolynomial): string =>
    polynomial.terms.map((term, index) => {
        const absolute = term.coefficient.numerator < 0n
            ? -term.coefficient.numerator : term.coefficient.numerator;
        const coefficient = term.coefficient.denominator === 1n
            ? String(absolute) : `${absolute}/${term.coefficient.denominator}`;
        const factors = term.monomial.exponents.flatMap((exponent, i) =>
            exponent === 0n ? [] : [polynomial.parent.variables[i] +
                (exponent === 1n ? '' : String(exponent).replace(/[0-9]/gu,
                    digit => '⁰¹²³⁴⁵⁶⁷⁸⁹'[Number(digit)]))]);
        const monomial = factors.join('·');
        const body = !monomial ? coefficient : coefficient === '1'
            ? monomial : `${coefficient}·${monomial}`;
        const sign = term.coefficient.numerator < 0n ? (index === 0 ? '−' : ' − ')
            : (index === 0 ? '' : ' + ');
        return sign + body;
    }).join('') || '0';

export function renderAlgebraPolynomialWorkbenchHtml(
    workspace: AlgebraPolynomialWorkspace,
    result: Awaited<ReturnType<typeof computeAlgebraPolynomialWorkbench>>,
    formal: Awaited<ReturnType<typeof prepareAlgebraPolynomialWorkbenchGoal>>
): string {
    assertAlgebraPolynomialWorkbenchCurrent(workspace, result);
    if (formal.source !== result.source) throw new Error('Formal goal belongs to stale workspace source');
    const text = (polynomial: AlgebraRationalPolynomial) => escape(displayPolynomial(polynomial));
    const equations = workspace.ideal.generators.map((generator, index) =>
        `<li><span class="curve curve-${index % 4}">f${index + 1}</span><code>${text(generator)} = 0</code></li>`).join('');
    const witness = (coefficients: readonly AlgebraRationalPolynomial[]) =>
        `<ol>${coefficients.map((coefficient, index) =>
            `<li><code>a${index + 1} = ${text(coefficient)}</code></li>`).join('')}</ol>`;
    const omitted = result.view.curves.reduce((sum, curve) => sum + curve.ambiguousCells, 0);
    const zeroLoci = result.view.curves.filter(curve => curve.zeroPolynomial).length;
    const native = result.nativeWitness ? witness(result.nativeWitness.coefficients)
        : `<p>Native remainder: <code>${text(result.native.remainder)}</code></p>`;
    const external = result.external.kind === 'witness'
        ? witness(result.external.witness.coefficients)
        : '<p>External nonmembership observation; no positive witness was returned.</p>';
    return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Emdash · Polynomial workbench</title><link rel="icon" href="data:,">
<style>
*{box-sizing:border-box}body{margin:0;background:#edf1f6;color:#24344a;font:16px/1.6 system-ui,sans-serif}
main{max-width:1160px;margin:36px auto;padding:0 24px}header{margin-bottom:28px}h1{font-size:32px;line-height:1.2;margin:8px 0}
h2{font-size:19px;margin:0 0 14px}h3{font-size:15px;margin:18px 0 5px}p{margin:8px 0}.eyebrow{font-size:12px;font-weight:700;letter-spacing:.13em;color:#63758d}
.layout{display:grid;grid-template-columns:1.2fr 1fr;gap:20px;align-items:start}.card{background:white;border:1px solid #dce3ed;border-radius:14px;padding:24px;margin-bottom:20px;box-shadow:0 3px 12px #1a335808}
.muted{color:#5e6d80;font-size:14px}.status{display:inline-block;border-radius:20px;background:#e8f4ee;color:#246448;padding:3px 11px;font-size:13px;font-weight:650}.open{background:#fff1d6;color:#8a5910}.observation{background:#edf0f8;color:#485575}
svg{width:100%;height:auto;border-radius:8px}code{font:14px/1.7 ui-monospace,monospace;overflow-wrap:anywhere}ul,ol{padding-left:24px}li{margin:7px 0}.equations{list-style:none;padding:0}.curve{display:inline-block;font-weight:700;width:34px}.curve-0{color:#286bd6}.curve-1{color:#d46326}.curve-2{color:#1d866c}.curve-3{color:#8c48ba}
details{margin-top:16px}summary{cursor:pointer;color:#425d82}.target{font-size:20px;background:#f6f8fc;padding:15px;border-radius:8px;margin:14px 0}.wide{grid-column:1/-1}.footer{font-size:13px;color:#64748b;margin:22px 0}pre{white-space:pre-wrap;word-break:break-word;font-size:12px;max-height:240px;overflow:auto}
@media(max-width:800px){main{margin:24px auto;padding:0 16px}.layout{display:block}.card{padding:18px}h1{font-size:27px}}
</style></head><body><main>
<header><div class="eyebrow">EMDASH / ALGEBRA WORKBENCH</div><h1>One source, several mathematical views</h1>
<p class="muted">Exact computation, a real-locus plot and a formal goal share the same polynomial objects.</p></header>
<div class="layout"><div>
<section class="card"><h2>Input curves</h2><p>Ring <code>Q[${workspace.ideal.ring.variables.map(escape).join(', ')}]</code> · ${escape(workspace.ideal.ring.monomialOrder)} order</p>
<ul class="equations">${equations}</ul>${renderAlgebraPolynomialCurveSvg(result.view)}
<p class="muted">${result.view.viewport.cells} × ${result.view.viewport.cells} cells · approximate rational-to-real view.</p>
<details><summary>Sampling scope</summary><p class="muted">${escape(result.view.limitation)} ${omitted} ambiguous cells omitted. ${zeroLoci} zero polynomials have the entire plane as their locus.</p></details></section>
</div><div>
<section class="card"><h2>Ideal membership</h2><p>Query <code>g = ${text(result.input.polynomial)}</code></p>
<p><span class="status ${result.nativeWitness ? '' : 'observation'}">${result.nativeWitness ? 'Native witness checked' : 'Native nonmembership result'}</span></p>
<p><span class="status ${result.external.kind === 'witness' ? '' : 'observation'}">${result.external.kind === 'witness' ? 'Singular witness checked' : 'Singular observation'}</span></p>
<p class="muted">Native and external membership decisions ${result.agrees ? 'agree' : 'disagree'}. Positive witnesses are independently recombined using exact rational arithmetic.</p>
<details open><summary>Original-generator coefficients</summary><p><code>g = Σ aᵢ fᵢ</code></p><h3>Native TypeScript</h3>${native}<h3>Singular ${escape(result.external.version)}</h3>${external}</details></section>
<section class="card"><h2>Formal goal <span class="status open">Open</span></h2>
<p>Assuming the displayed input equations vanish in the selected commutative ring:</p>
<div class="target"><code>${text(workspace.left)} = ${text(workspace.right)}</code></div>
<p class="muted">The goal and reified data check. Formal proof reconstruction is still required. No computation assumption has been adopted.</p>
<details><summary>Inspect the formal boundary</summary><p class="muted">${escape(formal.reason)}</p><p>Goal: <code>${escape(formal.goal.goalId)}</code></p><pre>${escape(formal.goal.targetCore)}</pre></details></section>
</div></div><p class="footer">Derived from the source-owned workspace. Re-run after changing a polynomial; earlier results are rejected as stale. A plot or arithmetic witness does not close the formal goal.</p>
</main></body></html>\n`;
}
