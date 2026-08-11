/**
 * Browser-safe PathOut presentation and qualification manifest.
 *
 * This module parses four finite expression forms. It performs no typing,
 * checking, normalization, transfer compilation, hashing, file access, or
 * Lambdapi execution. Its report says exactly that the corresponding
 * semantics were qualified at pinned checkpoints, not rerun in the browser.
 */

export const CORE_PATHOUT_PRESENTATION_1F_REVISION =
    'PATHOUT-LIBRARY-PRESENTATION-1F-BROWSER-SAFE-1' as const;

export type CorePathoutPresentationFormId =
    | 'pathout-category'
    | 'canonical-rho'
    | 'fixed-source-induction'
    | 'composition-normal-form';

export interface CorePathoutPresentationPoint {
    readonly offset: number;
    readonly line: number;
    readonly column: number;
}

export interface CorePathoutPresentationSpan {
    readonly file: string;
    readonly start: CorePathoutPresentationPoint;
    readonly end: CorePathoutPresentationPoint;
}

export interface CorePathoutPresentationForm {
    readonly id: CorePathoutPresentationFormId;
    readonly label: string;
    readonly head: 'PathOut' | 'rho' | 'Ind' | 'compose';
    readonly canonicalSource: string;
    readonly argumentRoles: readonly string[];
    readonly semanticTarget: string;
    readonly resultKind: string;
    readonly qualificationClaim: string;
}

export interface CorePathoutPresentationArgument {
    readonly name: string;
    readonly role: string;
    readonly span: CorePathoutPresentationSpan;
}

export interface CorePathoutPresentationRequest {
    readonly revision: typeof CORE_PATHOUT_PRESENTATION_1F_REVISION;
    readonly formId: CorePathoutPresentationFormId;
    readonly head: CorePathoutPresentationForm['head'];
    readonly arguments: readonly CorePathoutPresentationArgument[];
    readonly source: {
        readonly text: string;
        readonly file: string;
        readonly span: CorePathoutPresentationSpan;
    };
    readonly canonicalSource: string;
}

export type CorePathoutPresentationErrorCode =
    | 'UNEXPECTED_END'
    | 'UNEXPECTED_TOKEN'
    | 'UNKNOWN_HEAD'
    | 'INVALID_ARITY'
    | 'TRAILING_INPUT';

export class CorePathoutPresentationError extends Error {
    constructor(
        public readonly code: CorePathoutPresentationErrorCode,
        public readonly span: CorePathoutPresentationSpan,
        public readonly detail: string
    ) {
        super(
            `${detail} at ${span.file}:` +
            `${span.start.line}:${span.start.column}`
        );
        this.name = 'CorePathoutPresentationError';
    }
}

export interface CorePathoutQualificationReport {
    readonly revision: typeof CORE_PATHOUT_PRESENTATION_1F_REVISION;
    readonly status: 'qualified-at-pinned-checkpoint';
    readonly evidenceClass:
        'qualified-at-pinned-checkpoint-not-rerun-in-browser';
    readonly request: CorePathoutPresentationRequest;
    readonly semanticTarget: string;
    readonly resultKind: string;
    readonly qualificationClaim: string;
    readonly semanticCheckpoints: {
        readonly foundation: '550316a';
        readonly fixedSource: 'a361dc3';
        readonly internalized: 'b6005b3';
        readonly transitivity: '3b113ad';
        readonly ledger: '10432ba';
    };
    readonly freshSemanticCheck: false;
    readonly browserSemanticExecution: false;
    readonly productionBackend: 'typescript-emdash';
    readonly lambdapiRole: 'bounded-conformance-oracle';
    readonly freshCheckCommand: string;
    readonly boundaryNotice: string;
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const forms: readonly CorePathoutPresentationForm[] = deepFreeze([
    {
        id: 'pathout-category',
        label: 'Outgoing-arrow category',
        head: 'PathOut',
        canonicalSource: 'PathOut(Z, x)',
        argumentRoles: ['category', 'object-in-category'],
        semanticTarget: 'PathOut_cat',
        resultKind: 'category',
        qualificationClaim:
            'The outgoing-arrow category is the Sigma total of the ' +
            'fixed-source representable.'
    },
    {
        id: 'canonical-rho',
        label: 'Canonical rho arrow',
        head: 'rho',
        canonicalSource: 'rho(Z, x, y, p)',
        argumentRoles: [
            'category',
            'source-object',
            'target-object',
            'source-to-target-arrow'
        ],
        semanticTarget: 'pathout_refl_arrow',
        resultKind: 'arrow-in-pathout',
        qualificationClaim:
            'The canonical Sigma arrow runs from the reflexive outgoing ' +
            'arrow to the selected outgoing arrow.'
    },
    {
        id: 'fixed-source-induction',
        label: 'Fixed-source arrow induction',
        head: 'Ind',
        canonicalSource: 'Ind(Z, x, E, u)',
        argumentRoles: [
            'category',
            'source-object',
            'motive-over-pathout',
            'datum-at-reflexive-object'
        ],
        semanticTarget: 'path_ind_sec',
        resultKind: 'dependent-section',
        qualificationClaim:
            'Transport of the base datum along rho gives a section over ' +
            'all outgoing arrows.'
    },
    {
        id: 'composition-normal-form',
        label: 'Composition normal form',
        head: 'compose',
        canonicalSource: 'compose(Z, x, y, z, p, q)',
        argumentRoles: [
            'category',
            'source-object',
            'middle-object',
            'target-object',
            'source-to-middle-arrow',
            'middle-to-target-arrow'
        ],
        semanticTarget: 'path_comp_func-applied-at-q',
        resultKind: 'source-to-target-arrow',
        qualificationClaim:
            'The selected component of arrow-induced composition reduces ' +
            'to stable representable precomposition q after p.'
    }
]);

export const CORE_PATHOUT_PRESENTATION_1F_MANIFEST = deepFreeze({
    revision: CORE_PATHOUT_PRESENTATION_1F_REVISION,
    title: 'PathOut and arrow induction',
    grammar:
        'Expression := Head "(" Identifier ("," Identifier)* ")"',
    evidenceClass:
        'qualified-at-pinned-checkpoint-not-rerun-in-browser' as const,
    forms,
    semanticCheckpoints: {
        foundation: '550316a',
        fixedSource: 'a361dc3',
        internalized: 'b6005b3',
        transitivity: '3b113ad',
        ledger: '10432ba'
    } as const,
    semanticTransferSha256:
        'dd9484a58c6196fe5cc9c6c1ac941bea0a148c449855d011fc61fbcf3dc3fe9d',
    browser: {
        parsesExpressions: true,
        checksSemantics: false,
        loadsSemanticTransfer: false,
        nodeOrFilesystemDependency: false
    },
    freshCheck: {
        owner: 'typescript-emdash-node-adapter',
        command: './scripts/emdash pathout check',
        possibleColdCompilation: true
    },
    trustBoundary: {
        sealedTrustedPathIndProfile: true,
        transparentDerivedPathoutLibrary: true,
        parserAddsSemantics: false,
        ordinaryUsersMayInstallRules: false,
        productionBackend: 'typescript-emdash',
        lambdapiRole: 'bounded-conformance-oracle'
    }
});

interface InternalPoint {
    readonly offset: number;
    readonly line: number;
    readonly column: number;
}

interface ParsedIdentifier {
    readonly name: string;
    readonly start: InternalPoint;
    readonly end: InternalPoint;
}

const identifierStart = /^[A-Za-z]$/u;
const identifierContinue = /^[A-Za-z0-9_]$/u;

class Parser {
    private offset = 0;
    private line = 1;
    private column = 1;

    constructor(
        private readonly text: string,
        private readonly file: string
    ) {}

    parse(): CorePathoutPresentationRequest {
        const expressionStart = this.point();
        this.skipWhitespace();
        const head = this.identifier();
        const form = forms.find(candidate => candidate.head === head.name);
        if (form === undefined) {
            this.fail(
                'UNKNOWN_HEAD',
                head.start,
                head.end,
                `Unknown PathOut presentation head '${head.name}'`
            );
        }
        this.skipWhitespace();
        this.expect('(');
        this.skipWhitespace();
        const parsedArguments: ParsedIdentifier[] = [];
        if (this.peek() !== ')') {
            while (true) {
                parsedArguments.push(this.identifier());
                this.skipWhitespace();
                if (this.peek() !== ',') break;
                this.advance();
                this.skipWhitespace();
            }
        }
        this.expect(')');
        const expressionEnd = this.point();
        this.skipWhitespace();
        if (!this.atEnd()) {
            const start = this.point();
            this.advance();
            this.fail(
                'TRAILING_INPUT',
                start,
                this.point(),
                'Unexpected input after PathOut expression'
            );
        }
        if (parsedArguments.length !== form.argumentRoles.length) {
            this.fail(
                'INVALID_ARITY',
                head.start,
                expressionEnd,
                `${form.head} expects ${form.argumentRoles.length} ` +
                `arguments, received ${parsedArguments.length}`
            );
        }
        const arguments_ = parsedArguments.map((argument, index) => ({
            name: argument.name,
            role: form.argumentRoles[index] as string,
            span: this.span(argument.start, argument.end)
        }));
        const canonicalSource =
            `${form.head}(${arguments_.map(argument => argument.name)
                .join(', ')})`;
        return deepFreeze({
            revision: CORE_PATHOUT_PRESENTATION_1F_REVISION,
            formId: form.id,
            head: form.head,
            arguments: arguments_,
            source: {
                text: this.text,
                file: this.file,
                span: this.span(expressionStart, expressionEnd)
            },
            canonicalSource
        });
    }

    private point(): InternalPoint {
        return {
            offset: this.offset,
            line: this.line,
            column: this.column
        };
    }

    private span(
        start: InternalPoint,
        end: InternalPoint
    ): CorePathoutPresentationSpan {
        return {
            file: this.file,
            start: { ...start },
            end: { ...end }
        };
    }

    private atEnd(): boolean {
        return this.offset >= this.text.length;
    }

    private peek(): string | undefined {
        return this.text[this.offset];
    }

    private advance(): string | undefined {
        if (this.atEnd()) return undefined;
        const character = this.text[this.offset] as string;
        this.offset += 1;
        if (character === '\n') {
            this.line += 1;
            this.column = 1;
        } else {
            this.column += 1;
        }
        return character;
    }

    private skipWhitespace(): void {
        while (/\s/u.test(this.peek() ?? '')) this.advance();
    }

    private identifier(): ParsedIdentifier {
        const start = this.point();
        const first = this.peek();
        if (first === undefined) {
            this.fail(
                'UNEXPECTED_END',
                start,
                start,
                'Expected identifier, reached end of input'
            );
        }
        if (!identifierStart.test(first)) {
            this.advance();
            this.fail(
                'UNEXPECTED_TOKEN',
                start,
                this.point(),
                `Expected identifier, found '${first}'`
            );
        }
        let name = this.advance() as string;
        while (identifierContinue.test(this.peek() ?? '')) {
            name += this.advance() as string;
        }
        return { name, start, end: this.point() };
    }

    private expect(expected: '(' | ')'): void {
        const start = this.point();
        const actual = this.advance();
        if (actual === undefined) {
            this.fail(
                'UNEXPECTED_END',
                start,
                start,
                `Expected '${expected}', reached end of input`
            );
        }
        if (actual !== expected) {
            this.fail(
                'UNEXPECTED_TOKEN',
                start,
                this.point(),
                `Expected '${expected}', found '${actual}'`
            );
        }
    }

    private fail(
        code: CorePathoutPresentationErrorCode,
        start: InternalPoint,
        end: InternalPoint,
        detail: string
    ): never {
        throw new CorePathoutPresentationError(
            code,
            this.span(start, end),
            detail
        );
    }
}

/** Parse one finite PathOut expression into an inert request. */
export function parseCorePathoutPresentationText(
    source: string,
    sourceFile = '<pathout-presentation>'
): CorePathoutPresentationRequest {
    return new Parser(source, sourceFile).parse();
}

const formForRequest = (
    request: CorePathoutPresentationRequest
): CorePathoutPresentationForm => {
    const form = forms.find(candidate => candidate.id === request.formId);
    if (
        form === undefined ||
        request.revision !== CORE_PATHOUT_PRESENTATION_1F_REVISION ||
        request.head !== form.head ||
        request.arguments.length !== form.argumentRoles.length ||
        request.arguments.some((argument, index) =>
            argument.role !== form.argumentRoles[index] ||
            !/^[A-Za-z][A-Za-z0-9_]*$/u.test(argument.name)
        ) ||
        request.canonicalSource !==
            `${form.head}(${request.arguments.map(argument => argument.name)
                .join(', ')})`
    ) {
        throw new CorePathoutPresentationError(
            'UNEXPECTED_TOKEN',
            request.source.span,
            'Invalid or drifted PathOut presentation request'
        );
    }
    return form;
};

/** Canonically serialize a parsed request; no semantic check occurs. */
export function serializeCorePathoutPresentationRequest(
    request: CorePathoutPresentationRequest
): string {
    const form = formForRequest(request);
    return `${form.head}(${request.arguments.map(argument => argument.name)
        .join(', ')})`;
}

/** Create an honest pinned-qualification report for browser presentation. */
export function createCorePathoutQualificationReport(
    request: CorePathoutPresentationRequest
): CorePathoutQualificationReport {
    const form = formForRequest(request);
    const canonical = serializeCorePathoutPresentationRequest(request);
    return deepFreeze({
        revision: CORE_PATHOUT_PRESENTATION_1F_REVISION,
        status: 'qualified-at-pinned-checkpoint' as const,
        evidenceClass:
            'qualified-at-pinned-checkpoint-not-rerun-in-browser' as const,
        request,
        semanticTarget: form.semanticTarget,
        resultKind: form.resultKind,
        qualificationClaim: form.qualificationClaim,
        semanticCheckpoints:
            CORE_PATHOUT_PRESENTATION_1F_MANIFEST.semanticCheckpoints,
        freshSemanticCheck: false as const,
        browserSemanticExecution: false as const,
        productionBackend: 'typescript-emdash' as const,
        lambdapiRole: 'bounded-conformance-oracle' as const,
        freshCheckCommand:
            `./scripts/emdash pathout check ${form.id} ` +
            `--source '${canonical}'`,
        boundaryNotice:
            'This browser report parses the expression and displays ' +
            'checkpoint-qualified evidence. It did not rerun the PathOut ' +
            'semantic transfer or checker.'
    });
}

/** Format a reviewer-facing qualification report. */
export function formatCorePathoutQualificationReport(
    report: CorePathoutQualificationReport
): string {
    formForRequest(report.request);
    return [
        'QUALIFIED AT PINNED CHECKPOINT',
        `Expression: ${serializeCorePathoutPresentationRequest(
            report.request
        )}`,
        `Presentation: ${report.request.formId}`,
        `Semantic target: ${report.semanticTarget}`,
        `Result kind: ${report.resultKind}`,
        '',
        report.qualificationClaim,
        '',
        `TypeScript semantic checkpoint: ${report.semanticCheckpoints.transitivity}`,
        `Completion ledger: ${report.semanticCheckpoints.ledger}`,
        'Fresh semantic check in this browser: no',
        'Production backend: TypeScript/emdash',
        'Lambdapi role: bounded conformance oracle',
        '',
        report.boundaryNotice,
        '',
        'Explicit fresh-check command:',
        report.freshCheckCommand
    ].join('\n');
}
