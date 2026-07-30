/**
 * Narrow text adapter for the reviewed categorical syntax slices.
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
    'SYNTAX-PARITY-1C2B-CATEGORICAL-TEXT-1' as const;

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
        readonly kind: 'displayed-context-functor';
        readonly sources:
            readonly CoreCategoricalDisplayedFamily[];
        readonly target: CoreCategoricalDisplayedFamily;
    }
    | {
        readonly kind: 'displayed-dependent-context-functor';
        readonly sourceGroups:
            readonly (readonly CoreCategoricalDisplayedFamily[])[];
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

interface LocatedLambdaBinding {
    readonly name: string;
    readonly nameRange: TextRange;
    readonly annotation?: LocatedIdentifier;
}

interface LocatedLambda {
    readonly tag: 'lambda';
    readonly bindingGroups:
        readonly (readonly LocatedLambdaBinding[])[];
    readonly mode: string;
    readonly modeRange: TextRange;
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

    private parseLambdaBinding(): LocatedLambdaBinding {
        const name = this.parseIdentifier();
        this.skipWhitespace();
        const annotation = this.current() === ':'
            ? (() => {
                this.advance();
                return this.parseIdentifier();
            })()
            : undefined;
        return Object.freeze({
            name: name.name,
            nameRange: name.range,
            annotation
        });
    }

    private parseLambdaBindingGroups():
    readonly (readonly LocatedLambdaBinding[])[] {
        this.skipWhitespace();
        if (this.current() !== '(') {
            return Object.freeze([
                Object.freeze([this.parseLambdaBinding()])
            ]);
        }

        this.advance();
        this.skipWhitespace();
        if (this.current() === ')') {
            this.failHere(
                'UNEXPECTED_TOKEN',
                'A categorical binding group cannot be empty'
            );
        }
        if (this.atEnd()) {
            this.failHere(
                'UNEXPECTED_END',
                'Expected a categorical binding'
            );
        }

        const groups: (readonly LocatedLambdaBinding[])[] = [];
        let bindings: LocatedLambdaBinding[] = [];
        const names = new Set<string>();
        while (true) {
            const binding = this.parseLambdaBinding();
            if (names.has(binding.name)) {
                this.fail(
                    'DUPLICATE_BINDING',
                    binding.nameRange,
                    `Duplicate lambda binding '${binding.name}'`
                );
            }
            names.add(binding.name);
            bindings.push(binding);

            this.skipWhitespace();
            if (this.current() === ')') {
                this.advance();
                groups.push(Object.freeze(bindings));
                break;
            }
            if (this.current() === ';') {
                this.advance();
                groups.push(Object.freeze(bindings));
                bindings = [];
                this.skipWhitespace();
                if (this.current() === ')' || this.current() === ';') {
                    this.failHere(
                        'UNEXPECTED_TOKEN',
                        'A displayed dependency level cannot be empty'
                    );
                }
                if (this.atEnd()) {
                    this.failHere(
                        'UNEXPECTED_END',
                        'Expected a categorical binding after semicolon'
                    );
                }
                continue;
            }
            this.expect(',');
            this.skipWhitespace();
            if (
                this.current() === ')' ||
                this.current() === ';'
            ) {
                this.failHere(
                    'UNEXPECTED_TOKEN',
                    'A displayed sibling group cannot end with a comma'
                );
            }
            if (this.atEnd()) {
                this.failHere(
                    'UNEXPECTED_END',
                    'Expected a displayed sibling binding after comma'
                );
            }
        }

        if (groups.length === 1 && groups[0].length < 2) {
            this.fail(
                'UNEXPECTED_TOKEN',
                groups[0][0].nameRange,
                'A parenthesized displayed sibling group requires at ' +
                    'least two bindings or a semicolon dependency level'
            );
        }
        return Object.freeze(groups);
    }

    private parseLambda(): LocatedLambda {
        this.skipWhitespace();
        const start = this.point();
        this.advance();
        const mode = this.parseMode();
        const bindingGroups = this.parseLambdaBindingGroups();
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
            bindingGroups,
            mode: mode.value,
            modeRange: mode.range,
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
                const displayedInternalAction =
                    this.resolveDisplayedInternalActionOperation(
                        expression,
                        environment,
                        lambdaDepth
                    );
                if (displayedInternalAction !== undefined) {
                    return displayedInternalAction;
                }
                const displayedStructural =
                    this.resolveDisplayedStructuralOperation(
                        expression,
                        environment,
                        lambdaDepth
                    );
                if (displayedStructural !== undefined) {
                    return displayedStructural;
                }
                const ordinaryStructural =
                    this.resolveOrdinaryStructuralOperation(
                        expression,
                        environment,
                        lambdaDepth
                    );
                if (ordinaryStructural !== undefined) {
                    return ordinaryStructural;
                }
                const contextualIndex = this.fixedApplicationSpine(
                    expression,
                    'indexOf',
                    1
                );
                if (contextualIndex !== undefined) {
                    const [argument] = contextualIndex;
                    return invokeProgram(
                        this.sourceFile,
                        expression.range,
                        'Displayed contextual index was rejected',
                        () => this.program.indexOf(
                            this.resolveTerm(
                                argument,
                                environment,
                                undefined,
                                lambdaDepth
                            ),
                            sourceSiteFor(
                                this.sourceFile,
                                expression.range,
                                'parsed displayed contextual index'
                            )
                        )
                    );
                }
                const fibrePair = this.fixedApplicationSpine(
                    expression,
                    'fibrePair',
                    2
                );
                if (fibrePair !== undefined) {
                    const [leftExpression, rightExpression] = fibrePair;
                    return invokeProgram(
                        this.sourceFile,
                        expression.range,
                        'Displayed fibre pair was rejected',
                        () => this.program.fibrePair(
                            this.resolveTerm(
                                leftExpression,
                                environment,
                                undefined,
                                lambdaDepth
                            ),
                            this.resolveTerm(
                                rightExpression,
                                environment,
                                undefined,
                                lambdaDepth
                            ),
                            sourceSiteFor(
                                this.sourceFile,
                                expression.range,
                                'parsed displayed fibre pair'
                            )
                        )
                    );
                }
                const composition = this.fixedApplicationSpine(
                    expression,
                    'composeCells',
                    2
                );
                if (composition !== undefined) {
                    const [outerExpression, innerExpression] =
                        composition;
                    const outer = this.resolveTerm(
                        outerExpression,
                        environment,
                        undefined,
                        lambdaDepth
                    );
                    const inner = this.resolveTerm(
                        innerExpression,
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

    private resolveDisplayedInternalActionOperation(
        expression: LocatedApplication,
        environment: InternalEnvironment,
        lambdaDepth: number
    ): CoreCategoricalTerm | undefined {
        const source = (detail: string): CoreCategoricalSourceSite =>
            sourceSiteFor(
                this.sourceFile,
                expression.range,
                detail
            );
        const resolveTerm = (
            argument: LocatedExpression
        ): CoreCategoricalTerm => this.resolveTerm(
            argument,
            environment,
            undefined,
            lambdaDepth
        );

        const fullAction = this.fixedApplicationSpine(
            expression,
            'fullAction',
            3
        );
        if (fullAction !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed full action was rejected',
                () => this.program.displayedFunctorFullAction(
                    resolveTerm(fullAction[0]),
                    resolveTerm(fullAction[1]),
                    resolveTerm(fullAction[2]),
                    source('parsed displayed full action')
                )
            );
        }

        const internalCell = this.fixedApplicationSpine(
            expression,
            'cell',
            3
        );
        if (internalCell !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed internal cell was rejected',
                () => this.program.displayedFunctorInternalCell(
                    resolveTerm(internalCell[0]),
                    resolveTerm(internalCell[1]),
                    resolveTerm(internalCell[2]),
                    source('parsed displayed internal cell')
                )
            );
        }

        const naturality = this.fixedApplicationSpine(
            expression,
            'naturality',
            3
        );
        if (naturality !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed naturality cell was rejected',
                () => this.program.displayedTransforNaturality(
                    resolveTerm(naturality[0]),
                    resolveTerm(naturality[1]),
                    resolveTerm(naturality[2]),
                    source('parsed displayed naturality cell')
                )
            );
        }

        const internalHomAction = this.fixedApplicationSpine(
            expression,
            'internalHomAction',
            2
        );
        if (internalHomAction !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed internal Hom action was rejected',
                () =>
                    this.program.displayedTransforInternalHomAction(
                        resolveTerm(internalHomAction[0]),
                        resolveTerm(internalHomAction[1]),
                        source('parsed displayed internal Hom action')
                    )
            );
        }

        return undefined;
    }

    private resolveDisplayedStructuralOperation(
        expression: LocatedApplication,
        environment: InternalEnvironment,
        lambdaDepth: number
    ): CoreCategoricalTerm | undefined {
        const source = (detail: string): CoreCategoricalSourceSite =>
            sourceSiteFor(
                this.sourceFile,
                expression.range,
                detail
            );
        const resolveTerm = (
            argument: LocatedExpression
        ): CoreCategoricalTerm => this.resolveTerm(
            argument,
            environment,
            undefined,
            lambdaDepth
        );
        const resolveFamily = (
            argument: LocatedExpression
        ): CoreCategoricalDisplayedFamily =>
            this.resolveDisplayedFamilyArgument(
                argument,
                environment
            );

        for (const [head, side] of [
            ['pi1d', 'left'],
            ['pi2d', 'right']
        ] as const) {
            const projection = this.fixedApplicationSpine(
                expression,
                head,
                2
            );
            if (projection === undefined) continue;
            const left = resolveFamily(projection[0]);
            const right = resolveFamily(projection[1]);
            return invokeProgram(
                this.sourceFile,
                expression.range,
                `Displayed product ${side} projection was rejected`,
                () => side === 'left'
                    ? this.program.displayedProductLeftProjection(
                        left,
                        right,
                        source(
                            'parsed displayed product left projection'
                        )
                    )
                    : this.program.displayedProductRightProjection(
                        left,
                        right,
                        source(
                            'parsed displayed product right projection'
                        )
                    )
            );
        }

        const pair = this.fixedApplicationSpine(
            expression,
            'paird',
            2
        );
        if (pair !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed functor pairing was rejected',
                () => this.program.displayedProductPair(
                    resolveTerm(pair[0]),
                    resolveTerm(pair[1]),
                    source('parsed displayed functor pairing')
                )
            );
        }

        const swap = this.fixedApplicationSpine(
            expression,
            'swapd',
            2
        );
        if (swap !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed product exchange was rejected',
                () => this.program.displayedProductSwap(
                    resolveFamily(swap[0]),
                    resolveFamily(swap[1]),
                    source('parsed displayed product exchange')
                )
            );
        }

        const diagonal = this.fixedApplicationSpine(
            expression,
            'diagd',
            1
        );
        if (diagonal !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed product contraction was rejected',
                () => this.program.displayedProductDiagonal(
                    resolveFamily(diagonal[0]),
                    source('parsed displayed product contraction')
                )
            );
        }

        const sigmaProjection = this.fixedApplicationSpine(
            expression,
            'sigmaProj',
            1
        );
        if (sigmaProjection !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Sigma projection was rejected',
                () => this.program.sigmaProjection(
                    resolveFamily(sigmaProjection[0]),
                    source('parsed Sigma projection')
                )
            );
        }

        const pullbackFunctor = this.fixedApplicationSpine(
            expression,
            'pullbackFunctord',
            2
        );
        if (pullbackFunctor !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed functor pullback was rejected',
                () => this.program.pullbackDisplayedFunctor(
                    resolveTerm(pullbackFunctor[0]),
                    resolveTerm(pullbackFunctor[1]),
                    source('parsed displayed functor pullback')
                )
            );
        }

        const sigmaPair = this.fixedApplicationSpine(
            expression,
            'sigmaPair',
            3
        );
        if (sigmaPair !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Dependent pair was rejected',
                () => this.program.dependentPair(
                    resolveFamily(sigmaPair[0]),
                    resolveTerm(sigmaPair[1]),
                    resolveTerm(sigmaPair[2]),
                    source('parsed dependent pair')
                )
            );
        }

        const transport = this.fixedApplicationSpine(
            expression,
            'transport',
            2
        );
        if (transport !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed family transport was rejected',
                () => this.program.familyTransport(
                    resolveFamily(transport[0]),
                    resolveTerm(transport[1]),
                    source('parsed displayed family transport')
                )
            );
        }

        const sigmaArrow = this.fixedApplicationSpine(
            expression,
            'sigmaArrow',
            5
        );
        if (sigmaArrow !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Sigma arrow was rejected',
                () => this.program.sigmaArrow(
                    resolveFamily(sigmaArrow[0]),
                    resolveTerm(sigmaArrow[1]),
                    resolveTerm(sigmaArrow[2]),
                    resolveTerm(sigmaArrow[3]),
                    resolveTerm(sigmaArrow[4]),
                    source('parsed Sigma arrow')
                )
            );
        }

        const pullbackTotal = this.fixedApplicationSpine(
            expression,
            'pullbackTotal',
            2
        );
        if (pullbackTotal !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Pullback totalization was rejected',
                () => this.program.pullbackTotal(
                    resolveTerm(pullbackTotal[0]),
                    resolveFamily(pullbackTotal[1]),
                    source('parsed pullback totalization')
                )
            );
        }

        const transfdComposition = this.fixedApplicationSpine(
            expression,
            'composeTransfd',
            2
        );
        if (transfdComposition !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Displayed transformation composition was rejected',
                () => this.program.composeDisplayedTransfor(
                    resolveTerm(transfdComposition[0]),
                    resolveTerm(transfdComposition[1]),
                    source(
                        'parsed displayed transformation composition'
                    )
                )
            );
        }

        return undefined;
    }

    private resolveOrdinaryStructuralOperation(
        expression: LocatedApplication,
        environment: InternalEnvironment,
        lambdaDepth: number
    ): CoreCategoricalTerm | undefined {
        const source = (detail: string): CoreCategoricalSourceSite =>
            sourceSiteFor(
                this.sourceFile,
                expression.range,
                detail
            );
        const resolveTerm = (
            argument: LocatedExpression
        ): CoreCategoricalTerm => this.resolveTerm(
            argument,
            environment,
            undefined,
            lambdaDepth
        );

        const identity = this.fixedApplicationSpine(
            expression,
            'id',
            1
        );
        if (identity !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Ordinary identity functor was rejected',
                () => this.program.identityFunctor(
                    this.resolveCategoryArgument(
                        identity[0],
                        environment
                    ),
                    source('parsed ordinary identity functor')
                )
            );
        }

        const composition = this.fixedApplicationSpine(
            expression,
            'compose',
            2
        );
        if (composition !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Ordinary functor composition was rejected',
                () => this.program.composeFunctors(
                    resolveTerm(composition[0]),
                    resolveTerm(composition[1]),
                    source('parsed ordinary functor composition')
                )
            );
        }

        const pair = this.fixedApplicationSpine(
            expression,
            'pair',
            2
        );
        if (pair !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Ordinary functor pair was rejected',
                () => this.program.functorPair(
                    resolveTerm(pair[0]),
                    resolveTerm(pair[1]),
                    source('parsed ordinary functor pair')
                )
            );
        }

        const map = this.fixedApplicationSpine(
            expression,
            'map',
            2
        );
        if (map !== undefined) {
            return invokeProgram(
                this.sourceFile,
                expression.range,
                'Ordinary product map was rejected',
                () => this.program.productMap(
                    resolveTerm(map[0]),
                    resolveTerm(map[1]),
                    source('parsed ordinary product map')
                )
            );
        }

        for (const [head, side] of [
            ['pi1', 'left'],
            ['pi2', 'right']
        ] as const) {
            const projection = this.fixedApplicationSpine(
                expression,
                head,
                2
            );
            if (projection === undefined) continue;
            const left = this.resolveCategoryArgument(
                projection[0],
                environment
            );
            const right = this.resolveCategoryArgument(
                projection[1],
                environment
            );
            return invokeProgram(
                this.sourceFile,
                expression.range,
                `Ordinary product ${side} projection was rejected`,
                () => side === 'left'
                    ? this.program.productLeftProjection(
                        left,
                        right,
                        source(
                            'parsed ordinary product left projection'
                        )
                    )
                    : this.program.productRightProjection(
                        left,
                        right,
                        source(
                            'parsed ordinary product right projection'
                        )
                    )
            );
        }
        return undefined;
    }

    private resolveCategoryArgument(
        expression: LocatedExpression,
        environment: InternalEnvironment
    ): CoreCategoricalCategory {
        if (expression.tag !== 'identifier') {
            throw resolutionError(
                'EXPECTED_CATEGORY',
                this.sourceFile,
                expression.range,
                'This constructor position requires a checked category ' +
                    'identifier; category-valued expressions belong to ' +
                    'the separately gated SYNTAX-PARITY-1C3 row'
            );
        }
        const binding = this.lookup(expression, environment);
        if (binding.kind !== 'category') {
            throw resolutionError(
                'EXPECTED_CATEGORY',
                this.sourceFile,
                expression.range,
                `Identifier '${expression.name}' denotes a ` +
                    `${binding.kind}, not a category`
            );
        }
        return binding.value;
    }

    private resolveDisplayedFamilyArgument(
        expression: LocatedExpression,
        environment: InternalEnvironment
    ): CoreCategoricalDisplayedFamily {
        if (expression.tag !== 'identifier') {
            throw resolutionError(
                'EXPECTED_DISPLAYED_FAMILY',
                this.sourceFile,
                expression.range,
                'This constructor position requires a checked displayed-' +
                    'family identifier; family-valued expressions belong ' +
                    'to the separately gated SYNTAX-PARITY-1C3 row'
            );
        }
        const binding = this.lookup(expression, environment);
        if (binding.kind !== 'displayed-family') {
            throw resolutionError(
                'EXPECTED_DISPLAYED_FAMILY',
                this.sourceFile,
                expression.range,
                `Identifier '${expression.name}' denotes a ` +
                    `${binding.kind}, not a displayed family`
            );
        }
        return binding.value;
    }

    private fixedApplicationSpine(
        expression: LocatedApplication,
        headName: string,
        arity: number
    ): readonly LocatedExpression[] | undefined {
        const arguments_: LocatedExpression[] = [];
        let head: LocatedExpression = expression;
        while (head.tag === 'application') {
            arguments_.unshift(head.argument);
            head = head.subject;
        }
        if (
            head.tag !== 'identifier' ||
            head.name !== headName ||
            arguments_.length !== arity
        ) {
            return undefined;
        }
        return Object.freeze(arguments_);
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
        if (expression.bindingGroups.length > 1) {
            if (expression.mode !== 'fd') {
                throw resolutionError(
                    'UNSUPPORTED_BINDER_MODE',
                    this.sourceFile,
                    expression.modeRange,
                    'Displayed dependency levels require binder mode ' +
                        "'^fd'"
                );
            }
            return this.resolveDisplayedDependentContextLambda(
                expression,
                environment,
                this.requireExpected(
                    expression,
                    expected,
                    'displayed-dependent-context-functor'
                )
            );
        }
        const bindings = expression.bindingGroups[0];
        if (bindings.length > 1) {
            if (expression.mode !== 'fd') {
                throw resolutionError(
                    'UNSUPPORTED_BINDER_MODE',
                    this.sourceFile,
                    expression.modeRange,
                    'Independent displayed sibling groups require binder ' +
                        "mode '^fd'"
                );
            }
            return this.resolveDisplayedContextLambda(
                expression,
                bindings,
                environment,
                this.requireExpected(
                    expression,
                    expected,
                    'displayed-context-functor'
                )
            );
        }
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
        binding: LocatedLambdaBinding,
        environment: InternalEnvironment,
        expected: CoreCategoricalCategory,
        role: string
    ): void {
        if (binding.annotation === undefined) return;
        const annotationBinding = this.lookup(
            binding.annotation,
            environment
        );
        if (annotationBinding.kind !== 'category') {
            throw resolutionError(
                'EXPECTED_CATEGORY',
                this.sourceFile,
                binding.annotation.range,
                `Binder annotation '${binding.annotation.name}' ` +
                    'does not denote a category'
            );
        }
        const comparison = invokeProgram(
            this.sourceFile,
            binding.annotation.range,
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
                binding.annotation.range,
                `Binder category '${binding.annotation.name}' does not ` +
                    `match the expected ${role} ` +
                    `(comparison: ${comparison.status})`
            );
        }
    }

    private requireDisplayedFamilyAnnotation(
        binding: LocatedLambdaBinding,
        environment: InternalEnvironment,
        expected: CoreCategoricalDisplayedFamily,
        role = 'displayed-functor source'
    ): void {
        if (binding.annotation === undefined) return;
        const annotationBinding = this.lookup(
            binding.annotation,
            environment
        );
        if (annotationBinding.kind !== 'displayed-family') {
            throw resolutionError(
                'EXPECTED_DISPLAYED_FAMILY',
                this.sourceFile,
                binding.annotation.range,
                `Binder annotation '${binding.annotation.name}' does ` +
                    'not denote a displayed family'
            );
        }
        const comparison = invokeProgram(
            this.sourceFile,
            binding.annotation.range,
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
                binding.annotation.range,
                `Binder family '${binding.annotation.name}' does not ` +
                    `match the expected ${role} ` +
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
        const binding = expression.bindingGroups[0][0];
        this.requireCategoryAnnotation(
            binding,
            environment,
            expected.source,
            'functor source'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Categorical abstraction was rejected',
            () => this.program.lambda(
                binding.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    binding,
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
        const binding = expression.bindingGroups[0][0];
        this.requireCategoryAnnotation(
            binding,
            environment,
            expected.base,
            'dependent-section base'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Dependent categorical abstraction was rejected',
            () => this.program.dependentLambda(
                binding.name,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    binding,
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
        const binding = expression.bindingGroups[0][0];
        this.requireDisplayedFamilyAnnotation(
            binding,
            environment,
            expected.source
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed-functor abstraction was rejected',
            () => this.program.displayedFunctorLambda(
                binding.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    binding,
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
        const binding = expression.bindingGroups[0][0];
        this.requireCategoryAnnotation(
            binding,
            environment,
            expected.base,
            'displayed-transfor base'
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed-transfor abstraction was rejected',
            () => this.program.displayedTransforLambda(
                binding.name,
                expected.source,
                expected.target,
                token => this.resolveLambdaBody(
                    expression,
                    binding,
                    token,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private resolveDisplayedContextLambda(
        expression: LocatedLambda,
        bindings: readonly LocatedLambdaBinding[],
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            { readonly kind: 'displayed-context-functor' }
        >
    ): CoreCategoricalTerm {
        if (bindings.length !== expected.sources.length) {
            throw resolutionError(
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.range,
                `Displayed sibling group has ${bindings.length} bindings, ` +
                    `but its expectation supplies ${expected.sources.length} ` +
                    'source families'
            );
        }
        bindings.forEach((binding, index) =>
            this.requireDisplayedFamilyAnnotation(
                binding,
                environment,
                expected.sources[index],
                `displayed sibling source ${index + 1}`
            )
        );
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed contextual abstraction was rejected',
            () => this.program.displayedContextLambda(
                bindings.map((binding, index) => Object.freeze({
                    name: binding.name,
                    family: expected.sources[index]
                })),
                expected.target,
                tokens => this.resolveContextLambdaBody(
                    expression,
                    bindings,
                    tokens,
                    environment
                ),
                {
                    source: this.lambdaSource(expression)
                }
            )
        );
    }

    private resolveDisplayedDependentContextLambda(
        expression: LocatedLambda,
        environment: InternalEnvironment,
        expected: Extract<
            CoreCategoricalTextExpected,
            {
                readonly kind:
                    'displayed-dependent-context-functor';
            }
        >
    ): CoreCategoricalTerm {
        const groupSizes = expression.bindingGroups.map(
            group => group.length
        );
        const supportedShape =
            (
                groupSizes.length === 2 &&
                groupSizes[0] === 1 &&
                groupSizes[1] === 1
            ) ||
            (
                groupSizes.length === 3 &&
                groupSizes[0] === 1 &&
                groupSizes[1] === 2 &&
                groupSizes[2] === 1
            );
        if (!supportedShape) {
            throw resolutionError(
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.range,
                `Displayed dependent context has group sizes ` +
                    `[${groupSizes.join(',')}]; the reviewed direct ` +
                    'shapes are [1,1] and [1,2,1]'
            );
        }
        if (
            expected.sourceGroups.length !==
                expression.bindingGroups.length ||
            expression.bindingGroups.some((group, index) =>
                expected.sourceGroups[index] === undefined ||
                expected.sourceGroups[index].length !== group.length
            )
        ) {
            throw resolutionError(
                'INCOMPATIBLE_ABSTRACTION_EXPECTATION',
                this.sourceFile,
                expression.range,
                'Displayed dependency levels do not match the grouped ' +
                    'expected source families'
            );
        }

        expression.bindingGroups.forEach((group, groupIndex) =>
            group.forEach((binding, bindingIndex) =>
                this.requireDisplayedFamilyAnnotation(
                    binding,
                    environment,
                    expected.sourceGroups[groupIndex][bindingIndex],
                    `displayed dependency source ` +
                        `${groupIndex + 1}.${bindingIndex + 1}`
                )
            )
        );
        const bindings = expression.bindingGroups.flat();
        const sources = expected.sourceGroups.flat();
        return invokeProgram(
            this.sourceFile,
            expression.range,
            'Displayed dependent contextual abstraction was rejected',
            () => this.program.displayedDependentContextLambda(
                bindings.map((binding, index) => Object.freeze({
                    name: binding.name,
                    family: sources[index]
                })),
                expected.target,
                tokens => this.resolveContextLambdaBody(
                    expression,
                    bindings,
                    tokens,
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
        const names = expression.bindingGroups
            .map(group => group
                .map(binding => binding.name)
                .join(',')
            )
            .join(';');
        return sourceSiteFor(
            this.sourceFile,
            expression.range,
            `parsed ^${expression.mode} abstraction ${names}`
        );
    }

    private resolveLambdaBody(
        expression: LocatedLambda,
        binding: LocatedLambdaBinding,
        token: CoreCategoricalSlotToken,
        environment: InternalEnvironment
    ): CoreCategoricalTerm {
        const nested = new Map(environment);
        nested.set(binding.name, Object.freeze({
            name: binding.name,
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

    private resolveContextLambdaBody(
        expression: LocatedLambda,
        bindings: readonly LocatedLambdaBinding[],
        tokens: readonly CoreCategoricalSlotToken[],
        environment: InternalEnvironment
    ): CoreCategoricalTerm {
        const nested = new Map(environment);
        bindings.forEach((binding, index) => {
            nested.set(binding.name, Object.freeze({
                name: binding.name,
                kind: 'term' as const,
                value: tokens[index],
                callbackLocal: true
            }));
        });
        return this.resolveTerm(
            expression.body,
            nested,
            undefined,
            1
        );
    }
}

/**
 * Parse and recursively resolve one reviewed categorical expression.
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
