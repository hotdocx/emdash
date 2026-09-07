/** Ring-scoped whole-operation bindings for bounded homological computation. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraPolynomialRing } from './algebra_polynomial';
import {
    AlgebraOperation, AlgebraRuntimeSchema, algebraAlgorithmIdentity,
    defineAlgebraOperation, defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraReferenceImplementation, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex
} from './algebra_polynomial_freyd_bounded_complex';
import {
    AlgebraPolynomialFreydBoundedShortExactSequence,
    algebraPolynomialFreydBoundedShortExactSequence
} from './algebra_polynomial_freyd_bounded_short_exact';
import {
    AlgebraPolynomialFreydHomologyConnecting,
    algebraPolynomialFreydHomologyConnecting
} from './algebra_polynomial_freyd_homology_connecting';
import { AlgebraPolynomialFreydHomologyWindow, algebraPolynomialFreydHomologyWindow } from './algebra_polynomial_freyd_homology_window';
import {
    AlgebraPolynomialFreydBoundedLongExactHomology,
    algebraPolynomialFreydBoundedLongExactHomology,
    algebraPolynomialFreydLongExactWindowAt
} from './algebra_polynomial_freyd_long_exact';
import { AlgebraPolynomialFreydSnakeConnecting } from './algebra_polynomial_freyd_snake';
import {
    AlgebraPolynomialFreydSnakeExactSequence,
    algebraPolynomialFreydSnakeExactSequenceFromConnecting
} from './algebra_polynomial_freyd_snake_exact';
import { serializeAlgebraPolynomialFreydBoundedLongExactHomology } from './algebra_polynomial_freyd_long_exact_serialization';
import { serializeAlgebraPolynomialFreydSnakeExactSequence } from './algebra_polynomial_freyd_snake_exact_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-long-exact-reference-v1' as const,
    algorithmRevision: 'typescript-polynomial-freyd-long-exact-v1' as const,
    wholeResults: true as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydBoundedShortExactInput<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = Parameters<typeof algebraPolynomialFreydBoundedShortExactSequence<P, C, I>>[0];

export interface AlgebraPolynomialFreydHomologyDegreeInput<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>;
    readonly degree: number;
}

export interface AlgebraPolynomialFreydLongExactWindowInput<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly result: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>;
    readonly degree: number;
}

/** Explicitly gate this method-specific view; other connecting algorithms need their own view. */
export function algebraPolynomialFreydHomologyConnectingSnakeReference<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydHomologyConnecting<P, C, I>) {
    if (value.trace.kind !== 'snake-homology-connecting-v1') {
        throw new Error('The requested reference view requires the snake homology method');
    }
    return value.trace.snake;
}

/** A method-specific reference view, not part of the intrinsic homology API. */
export function algebraPolynomialFreydLongExactSnakeReferences<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(result: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>) {
    const sequences = result.windows.map(window => algebraPolynomialFreydSnakeExactSequenceFromConnecting(
        algebraPolynomialFreydHomologyConnectingSnakeReference(window.connecting)));
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-long-exact-snake-references' as const,
        result, sequences: Object.freeze(sequences)
    });
}

export type AlgebraPolynomialFreydLongExactSnakeReferences<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydLongExactSnakeReferences<P, C, I>>;

export function serializeAlgebraPolynomialFreydLongExactSnakeReferences<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>): string {
    if (value.sequences.length !== value.result.windows.length || value.sequences.some((sequence, degree) =>
        sequence.connecting !== value.result.windows[degree].connecting.trace.snake)) {
        throw new Error('Snake references must retain the actual connecting constructions');
    }
    return serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        result: serializeAlgebraPolynomialFreydBoundedLongExactHomology(value.result),
        sequences: value.sequences.map(serializeAlgebraPolynomialFreydSnakeExactSequence)
    }, 'polynomialFreydLongExactSnakeReferences');
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

export function algebraPolynomialFreydLongExactReferenceOperations<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(ring: AlgebraPolynomialRing<P, C, I>, snakeConnectingSchema: AlgebraRuntimeSchema<AlgebraPolynomialFreydSnakeConnecting<P, C, I>>) {
    const revision = ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_REFERENCE_PROFILE.revision;
    const prefix = 'algebra.polynomial-freyd-long-exact/' + ring.identity.id;
    const wholeSchema = <T extends { readonly kind: string }>(
        name: string, kind: T['kind'], ringOf: (value: T) => AlgebraParent
    ): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
        id: prefix + '/schema/' + name, revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== kind || !sameAlgebraParent(ringOf(value as T), ring)) {
                throw new Error(kind + ' for the selected ring expected at ' + path);
            }
            return value as T;
        }
    });
    const complexSchema = wholeSchema<AlgebraPolynomialFreydBoundedComplex<P, C, I>>(
        'complex', 'algebra-polynomial-freyd-bounded-complex', value => value.ring);
    const mapSchema = wholeSchema<AlgebraPolynomialFreydBoundedChainMap<P, C, I>>(
        'chain-map', 'algebra-polynomial-freyd-bounded-chain-map', value => value.source.ring);
    const sequenceSchema = wholeSchema<AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>>(
        'sequence', 'algebra-polynomial-freyd-bounded-short-exact-sequence', value => value.ring);
    const connectingSchema = wholeSchema<AlgebraPolynomialFreydHomologyConnecting<P, C, I>>(
        'connecting', 'algebra-polynomial-freyd-homology-connecting', value => value.sequence.ring);
    const windowSchema = wholeSchema<AlgebraPolynomialFreydHomologyWindow<P, C, I>>(
        'window', 'algebra-polynomial-freyd-homology-window', value => value.sequence.ring);
    const resultSchema = wholeSchema<AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>>(
        'result', 'algebra-polynomial-freyd-bounded-long-exact-homology', value => value.sequence.ring);
    const snakeExactSchema = wholeSchema<AlgebraPolynomialFreydSnakeExactSequence<P, C, I>>(
        'snake-exact', 'algebra-polynomial-freyd-snake-exact-sequence', value => value.connecting.triple.delta.source.ambient.ring);
    const snakeReferencesSchema = wholeSchema<AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>>(
        'snake-references', 'algebra-polynomial-freyd-long-exact-snake-references', value => value.result.sequence.ring);
    const sequenceInputSchema = defineAlgebraRuntimeSchema<AlgebraPolynomialFreydBoundedShortExactInput<P, C, I>>({
        id: prefix + '/schema/sequence-input', revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error('Bounded sequence input expected at ' + path);
            return Object.freeze({
                subcomplex: complexSchema.normalize(value.subcomplex, path + '.subcomplex'),
                middleComplex: complexSchema.normalize(value.middleComplex, path + '.middleComplex'),
                quotientComplex: complexSchema.normalize(value.quotientComplex, path + '.quotientComplex'),
                inclusion: mapSchema.normalize(value.inclusion, path + '.inclusion'),
                projection: mapSchema.normalize(value.projection, path + '.projection')
            });
        }
    });
    const degree = (value: unknown, path: string): number => {
        if (typeof value !== 'number' || !Number.isSafeInteger(value)) throw new Error('Integer degree expected at ' + path);
        return value;
    };
    const degreeInputSchema = defineAlgebraRuntimeSchema<AlgebraPolynomialFreydHomologyDegreeInput<P, C, I>>({
        id: prefix + '/schema/degree-input', revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error('Homology degree input expected at ' + path);
            return Object.freeze({
                sequence: sequenceSchema.normalize(value.sequence, path + '.sequence'),
                degree: degree(value.degree, path + '.degree')
            });
        }
    });
    const windowInputSchema = defineAlgebraRuntimeSchema<AlgebraPolynomialFreydLongExactWindowInput<P, C, I>>({
        id: prefix + '/schema/window-input', revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error('Retained window input expected at ' + path);
            return Object.freeze({
                result: resultSchema.normalize(value.result, path + '.result'),
                degree: degree(value.degree, path + '.degree')
            });
        }
    });
    const operation = <Input, Output>(name: string, input: AlgebraRuntimeSchema<Input>, output: AlgebraRuntimeSchema<Output>) =>
        defineAlgebraOperation({ id: prefix + '/' + name, revision, input, output });
    const boundedShortExact = operation('bounded-short-exact', sequenceInputSchema, sequenceSchema);
    const homologyConnecting = operation('homology-connecting', degreeInputSchema, connectingSchema);
    const homologyWindow = operation('homology-window', degreeInputSchema, windowSchema);
    const boundedLongExact = operation('bounded-long-exact', sequenceSchema, resultSchema);
    const windowAt = operation('window-at', windowInputSchema, windowSchema);
    const windowConnecting = operation('window-connecting', windowSchema, connectingSchema);
    const connectingSnake = operation('connecting-reference-snake', connectingSchema, snakeConnectingSchema);
    const snakeExactSequence = operation('snake-exact-sequence', snakeConnectingSchema, snakeExactSchema);
    const snakeReferences = operation('snake-reference-family', resultSchema, snakeReferencesSchema);
    const implementation = <Input, Output>(op: AlgebraOperation<Input, Output>, execute: (input: Input) => Output): AlgebraReferenceImplementation =>
        defineAlgebraReferenceImplementation({
            operation: op,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/' + op.identity.id,
                ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_REFERENCE_PROFILE.algorithmRevision),
            execute
        });
    return Object.freeze({
        sequenceInputSchema, degreeInputSchema, windowInputSchema,
        boundedShortExact, homologyConnecting, homologyWindow, boundedLongExact,
        windowAt, windowConnecting, connectingSnake, snakeExactSequence, snakeReferences,
        implementations: Object.freeze([
            implementation(boundedShortExact, algebraPolynomialFreydBoundedShortExactSequence),
            implementation(homologyConnecting, input => algebraPolynomialFreydHomologyConnecting(input.sequence, input.degree)),
            implementation(homologyWindow, input => algebraPolynomialFreydHomologyWindow(input.sequence, input.degree)),
            implementation(boundedLongExact, algebraPolynomialFreydBoundedLongExactHomology),
            implementation(windowAt, input => algebraPolynomialFreydLongExactWindowAt(input.result, input.degree)),
            implementation(windowConnecting, input => input.connecting),
            implementation(connectingSnake, algebraPolynomialFreydHomologyConnectingSnakeReference),
            implementation(snakeExactSequence, algebraPolynomialFreydSnakeExactSequenceFromConnecting),
            implementation(snakeReferences, algebraPolynomialFreydLongExactSnakeReferences)
        ])
    });
}

export type AlgebraPolynomialFreydLongExactReferenceOperations<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydLongExactReferenceOperations<P, C, I>>;
