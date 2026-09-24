/** Approximate real-locus views sampled directly from source polynomial terms. */

import {
    AlgebraIdealWitnessInput, algebraIdealWitnessSource, normalizeAlgebraIdealWitnessInput
} from './algebra_ideal_witness';
import { algebraPolynomialText } from './algebra_polynomial';

export interface AlgebraCurveViewport {
    readonly xMin: number;
    readonly xMax: number;
    readonly yMin: number;
    readonly yMax: number;
    readonly cells: number;
}

export const ALGEBRA_CURVE_VIEWPORT: AlgebraCurveViewport = Object.freeze({
    xMin: -2, xMax: 2, yMin: -2, yMax: 3, cells: 128
});

type Point = readonly [number, number];
type Segment = readonly [Point, Point];

export function sampleAlgebraPolynomialCurves(
    input: AlgebraIdealWitnessInput,
    viewport: AlgebraCurveViewport = ALGEBRA_CURVE_VIEWPORT
) {
    const normalized = normalizeAlgebraIdealWitnessInput(input);
    if (normalized.ideal.ring.variables.length !== 2) {
        throw new Error('A plane curve view requires exactly two ordered variables');
    }
    const { xMin, xMax, yMin, yMax, cells } = viewport;
    if (![xMin, xMax, yMin, yMax, xMax - xMin, yMax - yMin].every(Number.isFinite) ||
        xMin >= xMax || yMin >= yMax || !Number.isSafeInteger(cells) || cells < 8 || cells > 256) {
        throw new Error('Invalid finite viewport or cell count (8–256)');
    }
    const terms = normalized.ideal.generators.reduce((sum, p) => sum + p.terms.length, 0);
    if (terms * (cells + 1) ** 2 > 2_000_000 || normalized.ideal.generators.length > 64) {
        throw new Error('Curve sampling exceeds the bounded term-evaluation budget');
    }
    const point = (column: number, row: number): Point => Object.freeze([
        xMin + (xMax - xMin) * column / cells,
        yMin + (yMax - yMin) * row / cells
    ]);
    const curves = normalized.ideal.generators.map(polynomial => {
        const numeric = polynomial.terms.map(term => {
            const coefficient = Number(term.coefficient.numerator) / Number(term.coefficient.denominator);
            const exponents = term.monomial.exponents.map(Number);
            if (!Number.isFinite(coefficient) ||
                exponents.some(e => !Number.isSafeInteger(e) || e > 4096)) {
                throw new Error('Polynomial exceeds the numerical interpretation profile');
            }
            return { coefficient, exponents };
        });
        const evaluate = ([x, y]: Point): number => numeric.reduce((sum, term) =>
            sum + term.coefficient * x ** term.exponents[0] * y ** term.exponents[1], 0);
        const values = Array.from({ length: cells + 1 }, (_, row) =>
            Array.from({ length: cells + 1 }, (_, column) => evaluate(point(column, row))));
        if (values.some(row => row.some(value => !Number.isFinite(value)))) {
            throw new Error('Nonfinite sample; choose a smaller viewport or another interpretation');
        }
        const segments: Segment[] = [];
        let ambiguousCells = 0;
        for (let row = 0; row < cells; row++) {
            for (let column = 0; column < cells; column++) {
                const corners = [point(column, row), point(column + 1, row),
                    point(column + 1, row + 1), point(column, row + 1)];
                const samples = [values[row][column], values[row][column + 1],
                    values[row + 1][column + 1], values[row + 1][column]];
                const crossings: Point[] = [];
                for (let edge = 0; edge < 4; edge++) {
                    const next = (edge + 1) % 4;
                    const a = samples[edge], b = samples[next];
                    if ((a < 0) === (b < 0)) continue;
                    // Scaling first avoids overflow in a-b for finite large samples.
                    const scale = Math.max(Math.abs(a), Math.abs(b));
                    const fraction = (a / scale) / (a / scale - b / scale);
                    crossings.push(Object.freeze([
                        corners[edge][0] + fraction * (corners[next][0] - corners[edge][0]),
                        corners[edge][1] + fraction * (corners[next][1] - corners[edge][1])
                    ]));
                }
                if (crossings.length === 2) {
                    segments.push(Object.freeze([crossings[0], crossings[1]]));
                } else if (crossings.length > 2) {
                    ambiguousCells++;
                }
            }
        }
        return Object.freeze({
            polynomial, label: `${algebraPolynomialText(polynomial)} = 0`,
            segments: Object.freeze(segments), ambiguousCells,
            zeroPolynomial: polynomial.terms.length === 0
        });
    });
    return Object.freeze({
        authority: 'approximate-real-locus-view' as const,
        interpretation: 'rational coefficients to IEEE-754 numbers; uniform grid and edge interpolation',
        limitation: 'Sampling can miss components, tangencies and singularities. Ambiguous cells are omitted. No topology is certified.',
        source: algebraIdealWitnessSource(normalized),
        variables: normalized.ideal.ring.variables,
        viewport: Object.freeze({ ...viewport }), curves: Object.freeze(curves)
    });
}

export const algebraWorkbenchEscapeHtml = (text: string): string => text
    .replace(/&/gu, '&amp;').replace(/</gu, '&lt;').replace(/>/gu, '&gt;')
    .replace(/"/gu, '&quot;').replace(/'/gu, '&#39;');

const colors = ['#286bd6', '#d46326', '#1d866c', '#8c48ba'];

export function renderAlgebraPolynomialCurveSvg(
    view: ReturnType<typeof sampleAlgebraPolynomialCurves>
): string {
    const { xMin, xMax, yMin, yMax } = view.viewport;
    const width = 680, height = 530, margin = 45;
    const x = (value: number) => margin + (value - xMin) / (xMax - xMin) * (width - 2 * margin);
    const y = (value: number) => height - margin - (value - yMin) / (yMax - yMin) * (height - 2 * margin);
    const n = (value: number) => value.toFixed(3);
    const grid = Array.from({ length: 6 }, (_, index) => {
        const xv = xMin + (xMax - xMin) * index / 5;
        const yv = yMin + (yMax - yMin) * index / 5;
        return `<path d="M${n(x(xv))},${margin}V${height - margin} M${margin},${n(y(yv))}H${width - margin}" stroke="#dce3ed"/>
<text x="${n(x(xv))}" y="${height - 22}" text-anchor="middle">${xv.toFixed(1)}</text>
<text x="${margin - 9}" y="${n(y(yv) + 4)}" text-anchor="end">${yv.toFixed(1)}</text>`;
    }).join('\n');
    const axes = [
        xMin <= 0 && xMax >= 0 ? `M${n(x(0))},${margin}V${height - margin}` : '',
        yMin <= 0 && yMax >= 0 ? `M${margin},${n(y(0))}H${width - margin}` : ''
    ].join(' ');
    const paths = view.curves.map((curve, index) => {
        const path = curve.segments.map(([a, b]) =>
            `M${n(x(a[0]))},${n(y(a[1]))}L${n(x(b[0]))},${n(y(b[1]))}`).join(' ');
        return `<path aria-label="${algebraWorkbenchEscapeHtml(curve.label)}" d="${path}" fill="none" stroke="${colors[index % colors.length]}" stroke-width="2.2"/>`;
    }).join('\n');
    return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${width} ${height}" role="img" aria-label="Approximate real loci of the input polynomials">
<title>Shared polynomial curve view</title><desc>${algebraWorkbenchEscapeHtml(view.limitation)}</desc>
<rect width="100%" height="100%" fill="#f9fbfe"/>
<g font-family="sans-serif" font-size="12" fill="#58657a">${grid}</g>
<path d="${axes}" stroke="#8b98ac"/>${paths}
<g font-family="sans-serif" font-size="14" fill="#28364b">
<text x="${width - 22}" y="${height - 42}">${algebraWorkbenchEscapeHtml(view.variables[0])}</text>
<text x="23" y="26">${algebraWorkbenchEscapeHtml(view.variables[1])}</text></g></svg>`;
}
