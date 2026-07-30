/**
 * Narrow text adapter for the reviewed ordinary categorical syntax slice.
 *
 * The located parser is deliberately private. Resolution constructs terms
 * only through the existing CoreCategoricalProgram and therefore owns no
 * categorical action table, checker, conversion, or Core representation.
 */

import {
    CoreCategoricalCategory,
    CoreCategoricalDisplayedFamily,
    CoreCategoricalProgram,
    CoreCategoricalSourceSite
} from './categorical_program';
import {
    CoreCategoricalHomBoundary,
    CoreCategoricalSlotToken,
    CoreCategoricalTerm
} from './categorical_surface';
import {
    CoreCategoricalExpectedShape
} from './categorical_surface_spec';
import {
    SourceSpan,
    formatSourceSpan
} from './kernel';

export const CORE_CATEGORICAL_TEXT_REVISION =
    'SYNTAX-PARITY-1A-CATEGORICAL-TEXT-1' as const;

export type CoreCategoricalTextBinding =
    | {
        readonly name: string;
        readonly kind: 'category';
        readonly value: CoreCategoricalCategory;
    }
    | {
        readonly name: string;
        readonly kind: 'term';
        readonly value: CoreCategoricalTerm;
    }
    | {
        readonly name: string;
        readonly kind: 'displayed-family';
        readonly value: CoreCategoricalDisplayedFamily;
    }
    | {
        readonly name: string;
        readonly kind: 'hom-boundary';
        readonly value: CoreCategoricalHomBoundary;
    };

export type CoreCategoricalTextExpected =
    | {
        readonly kind: 'term';
        readonly applicationShape?: CoreCategoricalExpectedShape;
    }
    | {
        readonly kind: 'ordinary-functor';
        readonly source: CoreCategoricalCategory;
        readonly target: CoreCategoricalCategory;
    }
    | {
        readonly kind: 'dependent-section';
        readonly base: CoreCategoricalCategory;
        readonly target: CoreCategoricalDisplayedFamily;
    }
    | {
        readonly kind: 'displayed-functor';
        readonly source: CoreCategoricalDisplayedFamily;
        readonly target: CoreCategoricalDisplayedFamily;
    }
    | {
        readonly kind: 'displayed-transfor';
        readonly base: CoreCategoricalCategory;
        readonly source: CoreCategoricalTerm;
        readonly target: CoreCategoricalTerm;
    };

export interface CoreCategoricalTextRequest {
    readonly source: string;
    readonly sourceFile?: string;
    readonly environment: readonly CoreCategoricalTextBinding[];
    readonly expected: CoreCategoricalTextExpected;
}

export type CoreCategoricalTextErrorPhase =
    | 'parsing'
    | 'resolution';

export type CoreCategoricalTextErrorCode =
    | 'UNEXPECTED_TOKEN'
    | 'UNEXPECTED_END'
    | 'INVALID_IDENTIFIER'
    | 'DUPLICATE_BINDING'
    | 'UNKNOWN_IDENTIFIER'
    | 'EXPECTED_CATEGORY'
    | 'EXPECTED_DISPLAYED_FAMILY'
    | 'EXPECTED_TERM'
    | 'EXPECTED_ARGUMENT'
    | 'MISSING_ABSTRACTION_EXPECTATION'
    | 'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
    | 'UNSUPPORTED_BINDER_MODE'
    | 'UNSUPPORTED_NESTED_ABSTRACTION'
    | 'CATEGORICAL_REJECTION';

export class CoreCategoricalTextError extends Error {
    constructor(
        public readonly phase: CoreCategoricalTextErrorPhase,
        public readonly code: CoreCategoricalTextErrorCode,
        public readonly span: SourceSpan,
        public readonly detail: string,
        public readonly underlying?: unknown
    ) {
        super(`${detail} at ${formatSourceSpan(span)}`);
        this.name = 'CoreCategoricalTextError';
    }
}

interface TextPoint {
    readonly offset: number;
    readonly line: number;
    readonly column: number;
}

interface TextRange {
    readonly start: TextPoint;
    readonly end: TextPoint;
}

interface LocatedIdentifier {
    readonly tag: 'identifier';
    readonly name: string;
    readonly range: TextRange;
}

interface LocatedApplication {
    readonly tag: 'application';
    readonly subject: LocatedExpression;
    readonly argument: LocatedExpression;
    readonly range: TextRange;
}

interface LocatedLambda {
    readonly tag: 'lambda';
    readonly name: string;
    readonly nameRange: TextRange;
    readonly mode: string;
    readonly modeRange: TextRange;
    readonly annotation?: LocatedIdentifier;
    readonly body: LocatedExpression;
    readonly range: TextRange;
}

type LocatedExpression =
    | LocatedIdentifier
    | LocatedApplication
    | LocatedLambda;

interface InternalTermBinding {
    readonly name: string;
    readonly kind: 'term';
    readonly value: CoreCategoricalTerm;
    readonly callbackLocal: boolean;
}

type InternalBinding =
    | Exclude<CoreCategoricalTextBinding, { readonly kind: 'term' }>
    | InternalTermBinding;

type InternalEnvironment = ReadonlyMap<string, InternalBinding>;

const portableIdentifier = /^[A-Za-z][A-Za-z0-9_]*$/;
const identifierStart = /^[A-Za-z]$/;
const identifierContinue = /^[A-Za-z0-9_]$/;
const identifierLike = /^[A-Za-z0-9_$?_]$/;

const freezePoint = (
    offset: number,
    line: number,
    column: number
): TextPoint => Object.freeze({ offset, line, column });

const textRange = (
    start: TextPoint,
    end: TextPoint
): TextRange => Object.freeze({ start, end });

const sourceSpanFor = (
    file: string,
    range: TextRange
): SourceSpan => Object.freeze({
    file,
    start: Object.freeze({
        line: range.start.line,
        column: range.start.column
    }),
    end: Object.freeze({
        line: range.end.line,
        column: range.end.column
    })
});

const sourceSiteFor = (
    file: string,
    range: TextRange,
    detail: string
): CoreCategoricalSourceSite => Object.freeze({
    file,
    line: range.start.line,
    column: range.start.column,
    endLine: range.end.line,
    endColumn: range.end.column,
    detail
});

class CoreCategoricalTextParser {
    private offset = 0;
    private line = 1;
    private column = 1;

    constructor(
        private readonly source: string,
        private readonly sourceFile: string
    ) {}

    parse(): LocatedExpression {
        this.skipWhitespace();
        if (this.atEnd()) {
            this.failHere(
                'UNEXPECTED_END',
                'Expected a categorical expression'
            );
        }
        const expression = this.parseExpression();
        this.skipWhitespace();
        if (!this.atEnd()) {
            this.failHere(
                'UNEXPECTED_TOKEN',
                `Unexpected token '${this.current()}' after expression`
            );
        }
        return expression;
    }

    private point(): TextPoint {
        return freezePoint(this.offset, this.line, this.column);
    }

    private atEnd(): boolean {
        return this.offset >= this.source.length;
    }

    private current(): string | undefined {
        return this.source[this.offset];
    }

    private advance(): string {
        const character = this.source[this.offset];
        this.offset += 1;
        if (character === '\n') {
            this.line += 1;
            this.column = 1;
        } else {
            this.column += 1;
        }
        return character;
    }

    private pointAfterCurrent(): TextPoint {
        const character = this.current();
        if (character === undefined) return this.point();
        return character === '\n'
            ? freezePoint(this.offset + 1, this.line + 1, 1)
            : freezePoint(
                this.offset + 1,
                this.line,
                this.column + 1
            );
    }

    private fail(
        code: CoreCategoricalTextErrorCode,
        range: TextRange,
        detail: string
    ): never {
        throw new CoreCategoricalTextError(
            'parsing',
            code,
            sourceSpanFor(this.sourceFile, range),
            detail
        );
    }

    private failHere(
        code: CoreCategoricalTextErrorCode,
        detail: string
    ): never {
        this.fail(
            code,
            textRange(this.point(), this.pointAfterCurrent()),
            detail
        );
    }

    private skipWhitespace(): boolean {
        const start = this.offset;
        while (/\s/u.test(this.current() ?? '')) {
            this.advance();
        }
        return this.offset !== start;
    }

    private consume(text: string): boolean {
        if (!this.source.startsWith(text, this.offset)) return false;
        for (let index = 0; index < text.length; index += 1) {
            this.advance();
        }
        return true;
    }

    private expect(text: string): TextRange {
        const start = this.point();
        if (!this.consume(text)) {
            this.failHere(
                this.atEnd() ? 'UNEXPECTED_END' : 'UNEXPECTED_TOKEN',
                `Expected '${text}'`
            );
        }
        return textRange(start, this.point());
    }

    private parseExpression(): LocatedExpression {
        this.skipWhitespace();
        return this.current() === 'λ' || this.current() === '\\'
            ? this.parseLambda()
            : this.parseApplication();
    }

    private parseIdentifier(): LocatedIdentifier {
        this.skipWhitespace();
        const start = this.point();
        const first = this.current();
        if (first === undefined) {
            this.fail(
                'UNEXPECTED_END',
                textRange(start, start),
                'Expected a portable identifier'
            );
        }
        if (!identifierStart.test(first)) {
            this.fail(
                identifierLike.test(first)
                    ? 'INVALID_IDENTIFIER'
                    : 'UNEXPECTED_TOKEN',
                textRange(start, this.pointAfterCurrent()),
                identifierLike.test(first)
                    ? `Identifier cannot start with '${first}'`
                    : `Expected an identifier, found '${first}'`
            );
        }
        let name = this.advance();
        while (identifierContinue.test(this.current() ?? '')) {
            name += this.advance();
        }
        const invalidSuffix = this.current();
        if (
            invalidSuffix !== undefined &&
            /^[?$]$/.test(invalidSuffix)
        ) {
            this.fail(
                'INVALID_IDENTIFIER',
                textRange(start, this.pointAfterCurrent()),
                `Identifier '${name}${invalidSuffix}' is not portable`
            );
        }
        return Object.freeze({
            tag: 'identifier' as const,
            name,
            range: textRange(start, this.point())
        });
    }

    private parseMode(): {
        readonly value: string;
        readonly range: TextRange;
    } {
        const start = this.point();
        this.expect('^');
        let suffix = '';
        while (/^[A-Za-z]$/.test(this.current() ?? '')) {
            suffix += this.advance();
        }
        if (suffix.length === 0) {
            this.failHere(
                this.atEnd() ? 'UNEXPECTED_END' : 'UNEXPECTED_TOKEN',
                'Expected a categorical binder mode after ^'
            );
        }
        return Object.freeze({
            value: suffix,
            range: textRange(start, this.point())
        });
    }

    private parseLambda(): LocatedLambda {
        this.skipWhitespace();
        const start = this.point();
        this.advance();
        const mode = this.parseMode();
        const name = this.parseIdentifier();
        this.skipWhitespace();
        const annotation = this.current() === ':'
            ? (() => {
                this.advance();
                return this.parseIdentifier();
            })()
            : undefined;
        this.skipWhitespace();
        this.expect('.');
        this.skipWhitespace();
        if (this.atEnd()) {
            this.failHere(
                'UNEXPECTED_END',
                'Expected a lambda body'
            );
        }
        const body = this.parseExpression();
        return Object.freeze({
            tag: 'lambda' as const,
            name: name.name,
            nameRange: name.range,
            mode: mode.value,
            modeRange: mode.range,
            annotation,
            body,
            range: textRange(start, body.range.end)
        });
    }

    private canStartAtom(): boolean {
        const character = this.current();
        return character === '(' ||
            identifierLike.test(character ?? '');
    }

    private parseApplication(): LocatedExpression {
        let subject = this.parseAtom();
        while (true) {
            const separated = this.skipWhitespace();
            if (!separated || !this.canStartAtom()) return subject;
            const argument = this.parseAtom();
            subject = Object.freeze({
                tag: 'application' as const,
                subject,
                argument,
                range: textRange(
                    subject.range.start,
                    argument.range.end
                )
            });
        }
    }

    private parseAtom(): LocatedExpression {
        this.skipWhitespace();
        if (this.current() !== '(') {
            return this.parseIdentifier();
        }
        const start = this.point();
        this.advance();
        this.skipWhitespace();
        if (this.atEnd()) {
            this.failHere(
                'UNEXPECTED_END',
                'Expected an expression after opening parenthesis'
            );
        }
        const inner = this.parseExpression();
        this.skipWhitespace();
        this.expect(')');
        const range = textRange(start, this.point());
        return Object.freeze({
            ...inner,
            range
        });
    }
}

const resolutionError = (
    code: CoreCategoricalTextErrorCode,
    file: string,
    range: TextRange,
    detail: string,
    underlying?: unknown
): CoreCategoricalTextError => new CoreCategoricalTextError(
    'resolution',
    code,
    sourceSpanFor(file, range),
    detail,
    underlying
);

const invokeProgram = <T>(
    file: string,
    range: TextRange,
    detail: string,
    action: () => T
): T => {
    try {
        return action();
    } catch (error: unknown) {
        if (error instanceof CoreCategoricalTextError) throw error;
        const message = error instanceof Error
            ? `${detail}: ${error.message}`
            : detail;
        throw resolutionError(
            'CATEGORICAL_REJECTION',
            file,
            range,
            message,
            error
        );
    }
};

const initialEnvironment = (
    request: CoreCategoricalTextRequest,
    sourceFile: string,
    start: TextPoint
): Map<string, InternalBinding> => {
    const environment = new Map<string, InternalBinding>();
    const startRange = textRange(start, start);
    for (const binding of request.environment) {
        if (!portableIdentifier.test(binding.name)) {
            throw resolutionError(
                'INVALID_IDENTIFIER',
                sourceFile,
                startRange,
                `Host binding '${binding.name}' is not a portable identifier`
            );
        }
        if (environment.has(binding.name)) {
            throw resolutionError(
                'DUPLICATE_BINDING',
                sourceFile,
                startRange,
                `Host environment contains duplicate name '${binding.name}'`
            );
        }
        environment.set(
            binding.name,
            binding.kind === 'term'
                ? Object.freeze({
                    ...binding,
                    callbackLocal: false
                })
                : binding
        );
    }
    return environment;
};

class CoreCategoricalTextResolver {
    constructor(
        private readonly program: CoreCategoricalProgram,
        private readonly sourceFile: string
    ) {}

    resolve(
        expression: LocatedExpression,
        environment: InternalEnvironment,
        expected: CoreCategoricalTextExpected
    ): CoreCategoricalTerm {
        let term: CoreCategoricalTerm;
        if (expression.tag === 'lambda') {
            term = this.resolveRootLambda(
                expression,
                environment,
                expected
            );
        } else {
            if (expected.kind !== 'term') {
                throw resolutionError(
                    'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                    this.sourceFile,
                    expression.range,
                    `A ${expected.kind} expectation requires a root lambda`
                );
            }
            term = this.resolveTerm(
                expression,
                environment,
                expected.applicationShape,
                0
            );
        }
        invokeProgram(
            this.sourceFile,
            expression.range,
            'Resolved term does not belong to this categorical program',
            () => this.program.inspect(term)
        );
        return term;
    }

    private lookup(
        identifier: LocatedIdentifier,
        environment: InternalEnvironment
    ): InternalBinding {
        const binding = environment.get(identifier.name);
        if (binding === undefined) {
            throw resolutionError(
                'UNKNOWN_IDENTIFIER',
                this.sourceFile,
                identifier.range,
                `Unknown identifier '${identifier.name}'`
            );
        }
        return binding;
    }

    private inspectTerm(
        term: InternalTermBinding,
        range: TextRange
    ): CoreCategoricalTerm {
        if (!term.callbackLocal) {
            invokeProgram(
                this.sourceFile,
                range,
                `Host term '${term.name}' is foreign or invalid`,
                () => this.program.inspect(term.value)
            );
        }
        return term.value;
    }

    private resolveTerm(
        expression: LocatedExpression,
        environment: InternalEnvironment,
        rootApplicationShape: CoreCategoricalExpectedShape | undefined,
        lambdaDepth: number
    ): CoreCategoricalTerm {
        switch (expression.tag) {
            case 'identifier': {
                const binding = this.lookup(expression, environment);
                if (binding.kind !== 'term') {
                    throw resolutionError(
                        'EXPECTED_TERM',
                        this.sourceFile,
                        expression.range,
                        `Identifier '${expression.name}' denotes a ` +
                            `${binding.kind}, not a categorical term`
                    );
                }
                return this.inspectTerm(binding, expression.range);
            }
            case 'application': {
                const composition = this.composeCellsSpine(expression);
                if (composition !== undefined) {
                    const outer = this.resolveTerm(
                        composition.outer,
                        environment,
                        undefined,
                        lambdaDepth
                    );
                    const inner = this.resolveTerm(
                        composition.inner,
                        environment,
                        undefined,
                        lambdaDepth
                    );
                    return invokeProgram(
                        this.sourceFile,
                        expression.range,
                        'Categorical cell composition was rejected',
                        () => this.program.composeCells(
                            outer,
                            inner,
                            sourceSiteFor(
                                this.sourceFile,
                                expression.range,
                                'parsed categorical cell composition'
                            )
                        )
                    );
                }
                const subject = this.resolveTerm(
                    expression.subject,
                    environment,
                    undefined,
                    lambdaDepth
                );
                const argument = this.resolveArgument(
                    expression.argument,
                    environment,
                    lambdaDepth
                );
                return invokeProgram(
                    this.sourceFile,
                    expression.range,
                    'Categorical application was rejected',
                    () => this.program.apply(
                        subject,
                        argument,
                        {
                            ...(rootApplicationShape === undefined
                                ? {}
                                : {
                                    expectedShape:
                                        rootApplicationShape
                                }),
                            source: sourceSiteFor(
                                this.sourceFile,
                                expression.range,
                                'parsed categorical application'
                            )
                        }
                    )
                );
            }
            case 'lambda':
                throw resolutionError(
                    lambdaDepth > 0
                        ? 'UNSUPPORTED_NESTED_ABSTRACTION'
                        : 'MISSING_ABSTRACTION_EXPECTATION',
                    this.sourceFile,
                    expression.range,
                    lambdaDepth > 0
                        ? 'Nested text abstraction requires a later ' +
                            'recursive expected-classifier contract'
                        : 'Text abstraction requires an ordinary-functor ' +
                            'expectation'
                );
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    }

    private composeCellsSpine(
        expression: LocatedApplication
    ): {
        readonly outer: LocatedExpression;
        readonly inner: LocatedExpression;
    } | undefined {
        if (
            expression.subject.tag !== 'application' ||
            expression.subject.subject.tag !== 'identifier' ||
            expression.subject.subject.name !== 'composeCells'
        ) {
            return undefined;
        }
        return Object.freeze({
            outer: expression.subject.argument,
            inner: expression.argument
        });
    }

    private resolveArgument(
        expression: LocatedExpression,
        environment: InternalEnvironment,
        lambdaDepth: number
    ): CoreCategoricalTerm | CoreCategoricalHomBoundary {
        if (expression.tag !== 'identifier') {
            return this.resolveTerm(
                expression,
                environment,
                undefined,
                lambdaDepth
            );
        }
        const binding = this.lookup(expression, environment);
        if (
            binding.kind === 'category' ||
            binding.kind === 'displayed-family'
        ) {
            throw resolutionError(
                'EXPECTED_ARGUMENT',
                this.sourceFile,
                expression.range,
                `${binding.kind === 'category'
                    ? 'Category'
                    : 'Displayed family'} '${expression.name}' is not an ` +
                    'admissible ' +
                    'categorical application argument'
            );
        }
        return binding.kind === 'term'
            ? this.inspectTerm(binding, expression.range)
            : binding.value;
    }

    private resolveRootLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: CoreCategoricalTextExpected
    ): CoreCategoricalTerm {
        switch (expression.mode) {
            case 'f':
                return this.resolveOrdinaryLambda(
                    expression,
                    environment,
                    this.requireExpected(
                        expression,
                        expected,
                        'ordinary-functor'
                    )
                );
            case 'n':
                return this.resolveDependentLambda(
                    expression,
                    environment,
                    this.requireExpected(
                        expression,
                        expected,
                        'dependent-section'
                    )
                );
            case 'fd':
                return this.resolveDisplayedFunctorLambda(
                    expression,
                    environment,
                    this.requireExpected(
                        expression,
                        expected,
                        'displayed-functor'
                    )
                );
            case 'nd':
                return this.resolveDisplayedTransforLambda(
                    expression,
                    environment,
                    this.requireExpected(
                        expression,
                        expected,
                        'displayed-transfor'
                    )
                );
            default:
                throw resolutionError(
                    'UNSUPPORTED_BINDER_MODE',
                    this.sourceFile,
                    expression.modeRange,
                    `Binder mode '^${expression.mode}' is outside the ` +
                        'reviewed syntax-parity profile'
                );
        }
    }

    private requireExpected<
        Kind extends Exclude<
            CoreCategoricalTextExpected['kind'],
            'term'
        >
    >(
        expression: LocatedLambda,
        expected: CoreCategoricalTextExpected,
        kind: Kind
    ): Extract<CoreCategoricalTextExpected, { readonly kind: Kind }> {
        if (expected.kind !== kind) {
            throw resolutionError(
                expected.kind === 'term'
                    ? 'MISSING_ABSTRACTION_EXPECTATION'
                    : 'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.range,
                `Root ^${expression.mode} abstraction requires a ` +
                    `${kind} expectation, not ${expected.kind}`
            );
        }
        return expected as Extract<
            CoreCategoricalTextExpected,
            { readonly kind: Kind }
        >;
    }

    private requireCategoryAnnotation(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: CoreCategoricalCategory,
        role: string
    ): void {
        if (expression.annotation === undefined) return;
        const annotationBinding = this.lookup(
            expression.annotation,
            environment
        );
        if (annotationBinding.kind !== 'category') {
            throw resolutionError(
                'EXPECTED_CATEGORY',
                this.sourceFile,
                expression.annotation.range,
                `Binder annotation '${expression.annotation.name}' ` +
                    'does not denote a category'
            );
        }
        const comparison = invokeProgram(
            this.sourceFile,
            expression.annotation.range,
            `Binder ${role} category comparison was rejected`,
            () => this.program.compareCategories(
                annotationBinding.value,
                expected
            )
        );
        if (comparison.status !== 'equal') {
            throw resolutionError(
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.annotation.range,
                `Binder category '${expression.annotation.name}' does not ` +
                    `match the expected ${role} ` +
                    `(comparison: ${comparison.status})`
            );
        }
    }

    private requireDisplayedFamilyAnnotation(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: CoreCategoricalDisplayedFamily
    ): void {
        if (expression.annotation === undefined) return;
        const annotationBinding = this.lookup(
            expression.annotation,
            environment
        );
        if (annotationBinding.kind !== 'displayed-family') {
            throw resolutionError(
                'EXPECTED_DISPLAYED_FAMILY',
                this.sourceFile,
                expression.annotation.range,
                `Binder annotation '${expression.annotation.name}' does ` +
                    'not denote a displayed family'
            );
        }
        const comparison = invokeProgram(
            this.sourceFile,
            expression.annotation.range,
            'Binder source-family comparison was rejected',
            () => this.program.compareDisplayedFamilies(
                annotationBinding.value,
                expected
            )
        );
        if (comparison.status !== 'equal') {
            throw resolutionError(
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.annotation.range,
                `Binder family '${expression.annotation.name}' does not ` +
                    'match the expected displayed-functor source ' +
                    `(comparison: ${comparison.status})`
            );
        }
    }

    private resolveOrdinaryLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            { readonly kind: 'ordinary-functor' }
        >
    ): CoreCategoricalTerm {
        this.requireCategoryAnnotation(
            expression,
            environment,
            expected.source,
            'functor source'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Categorical abstraction was rejected',
            () => this.program.lambda(
                expression.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    token,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private resolveDependentLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            { readonly kind: 'dependent-section' }
        >
    ): CoreCategoricalTerm {
        this.requireCategoryAnnotation(
            expression,
            environment,
            expected.base,
            'dependent-section base'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Dependent categorical abstraction was rejected',
            () => this.program.dependentLambda(
                expression.name,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    token,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private resolveDisplayedFunctorLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            { readonly kind: 'displayed-functor' }
        >
    ): CoreCategoricalTerm {
        this.requireDisplayedFamilyAnnotation(
            expression,
            environment,
            expected.source
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed-functor abstraction was rejected',
            () => this.program.displayedFunctorLambda(
                expression.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    token,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private resolveDisplayedTransforLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            { readonly kind: 'displayed-transfor' }
        >
    ): CoreCategoricalTerm {
        this.requireCategoryAnnotation(
            expression,
            environment,
            expected.base,
            'displayed-transfor base'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed-transfor abstraction was rejected',
            () => this.program.displayedTransforLambda(
                expression.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    token,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private lambdaSource(
        expression: LocatedLambda
    ): CoreCategoricalSourceSite {
        return sourceSiteFor(
            this.sourceFile,
            expression.range,
            `parsed ^${expression.mode} abstraction ${expression.name}`
        );
    }

    private resolveLambdaBody(
        expression: LocatedLambda,
        token: CoreCategoricalSlotToken,
        environment: InternalEnvironment
    ): CoreCategoricalTerm {
        const nested = new Map(environment);
        nested.set(expression.name, Object.freeze({
            name: expression.name,
            kind: 'term' as const,
            value: token,
            callbackLocal: true
        }));
        return this.resolveTerm(
            expression.body,
            nested,
            undefined,
            1
        );
    }
}

/**
 * Parse and recursively resolve one reviewed ordinary categorical expression.
 *
 * The returned value is an ordinary CoreCategoricalProgram term. Callers use
 * the existing `program.compile`, `inspect`, or `compare` operations exactly
 * as they do for direct TypeScript construction.
 */
export function elaborateCoreCategoricalText(
    program: CoreCategoricalProgram,
    request: CoreCategoricalTextRequest
): CoreCategoricalTerm {
    const sourceFile = request.sourceFile ?? '<categorical-text>';
    const start = freezePoint(0, 1, 1);
    const environment = initialEnvironment(
        request,
        sourceFile,
        start
    );
    const expression = new CoreCategoricalTextParser(
        request.source,
        sourceFile
    ).parse();
    return new CoreCategoricalTextResolver(
        program,
        sourceFile
    ).resolve(
        expression,
        environment,
        request.expected
    );
}
