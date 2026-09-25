import {
  RATIONAL_DOMAIN, algebraRational, algebraPolynomialRing,
  algebraPolynomialVariable, algebraPolynomialConstant, algebraPolynomialPower,
  algebraPolynomialSubtract, algebraPolynomialMultiply, algebraPolynomialText,
  algebraPolynomialIdeal, algebraGroebnerBasis, algebraIdealMembership,
  algebraIdealWitnessSource, checkAlgebraIdealWitness, sampleAlgebraPolynomialCurves,
  type AlgebraCurveViewport,
} from '@hotdocx/emdash/algebra';
import type { TopLevelSpec } from 'vega-lite';

export const viewports: Readonly<Record<string, AlgebraCurveViewport>> = {
  standard: { xMin: -2, xMax: 2, yMin: -2, yMax: 3, cells: 96 },
  wide: { xMin: -4, xMax: 4, yMin: -4, yMax: 6, cells: 96 },
  close: { xMin: 0, xMax: 2, yMin: 0, yMax: 2, cells: 96 },
};

/** The one mathematical source for exact computation and sampled views. */
export function calculateFamily(parameter: string) {
  if (parameter.length > 512) throw new Error('Use a rational parameter of at most 512 characters.');
  const rational = algebraRational(parameter.trim());
  const normalizedParameter = rational.denominator === 1n
    ? String(rational.numerator) : `${rational.numerator}/${rational.denominator}`;
  const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
  const x = algebraPolynomialVariable(ring, 0), y = algebraPolynomialVariable(ring, 1);
  const c = algebraPolynomialConstant(ring, rational);
  const input = Object.freeze({
    ideal: algebraPolynomialIdeal(ring, [
      algebraPolynomialSubtract(y, algebraPolynomialPower(x, 2n)),
      algebraPolynomialSubtract(algebraPolynomialMultiply(x, y), c),
    ]),
    polynomial: algebraPolynomialSubtract(algebraPolynomialPower(x, 3n), c),
  });
  const source = algebraIdealWitnessSource(input);
  const membership = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal, {
    maximumPairs: 128, maximumBasisSize: 32, maximumTotalReductionSteps: 10_000,
  }));
  if (!membership.member) throw new Error('This family should have a membership witness.');
  const checked = checkAlgebraIdealWitness(input, { source, coefficients: membership.coefficients });
  const generators = input.ideal.generators.map(algebraPolynomialText);
  const query = algebraPolynomialText(input.polynomial);
  const identity = `${query} = ` + checked.coefficients.map((coefficient, index) =>
    `(${algebraPolynomialText(coefficient)}) · (${generators[index]})`).join(' + ');
  return Object.freeze({ parameter: normalizedParameter, input, source, checked, generators, query, identity });
}

export type FamilyCalculation = ReturnType<typeof calculateFamily>;

/** Sampling failure leaves the independently usable exact calculation intact. */
export function sampleFamily(calculation: FamilyCalculation, viewport: AlgebraCurveViewport) {
  if (algebraIdealWitnessSource(calculation.input) !== calculation.source) {
    throw new Error('The calculation belongs to a different mathematical source.');
  }
  return sampleAlgebraPolynomialCurves(calculation.input, viewport);
}

export type FamilySamples = ReturnType<typeof sampleFamily>;

/** Mathematical samples become ordinary plotting rows; Vega-Lite owns rendering. */
export function curveSpec(samples: FamilySamples, width: number): TopLevelSpec {
  if (!Number.isFinite(width) || width < 240) throw new Error('A plot needs at least 240 finite pixels.');
  const { xMin, xMax, yMin, yMax } = samples.viewport;
  return {
    $schema: 'https://vega.github.io/schema/vega-lite/v5.json',
    description: `Approximate real loci: ${samples.curves.map(curve => curve.label).join('; ')}. ${samples.limitation}`,
    usermeta: { source: samples.source, interpretation: samples.interpretation, viewport: samples.viewport },
    width, height: Math.max(280, Math.min(520, Math.round(width * 0.72))),
    autosize: { type: 'fit', contains: 'padding' },
    padding: 8,
    data: { values: samples.curves.flatMap(curve => curve.segments.map(([start, end]) => ({
      curve: curve.label, x: start[0], y: start[1], x2: end[0], y2: end[1],
    }))) },
    mark: { type: 'rule', strokeWidth: 2, clip: true, aria: false },
    encoding: {
      x: { field: 'x', type: 'quantitative', title: samples.variables[0],
        scale: { domain: [xMin, xMax], zero: false } },
      x2: { field: 'x2' },
      y: { field: 'y', type: 'quantitative', title: samples.variables[1],
        scale: { domain: [yMin, yMax], zero: false } },
      y2: { field: 'y2' },
      color: { field: 'curve', type: 'nominal', title: null,
        scale: { domain: samples.curves.map(curve => curve.label), range: ['#21645e', '#be653b'] },
        legend: { orient: 'bottom', direction: 'vertical', labelLimit: Math.max(180, width - 40) } },
      tooltip: [{ field: 'curve', type: 'nominal', title: 'Curve' }],
    },
    config: {
      font: 'system-ui', background: '#ffffff', view: { stroke: null },
      axis: { gridColor: '#e5ebe7', labelColor: '#475750', titleColor: '#263e36', tickCount: 6 },
      legend: { labelColor: '#263e36', labelFontSize: 12, symbolStrokeWidth: 3 },
    },
  };
}
