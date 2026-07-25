/**
 * Pure, fail-closed inventory parser for Lambdapi's canonical `export -o lp`
 * output.
 *
 * This deliberately stops at top-level commands. Term, pattern, declaration,
 * and rule compilation belong to later scale-qualification slices.
 */

export type CanonicalLambdapiCommandKind =
    | 'require'
    | 'flag'
    | 'symbol'
    | 'inductive'
    | 'rule'
    | 'unif_rule'
    | 'builtin'
    | 'notation'
    | 'opaque';

export type CanonicalLambdapiSymbolModifier =
    | 'constant'
    | 'injective'
    | 'protected'
    | 'private'
    | 'opaque';

interface CanonicalLambdapiCommandBase {
    readonly ordinal: number;
    readonly kind: CanonicalLambdapiCommandKind;
    /** Canonical command text, including its terminating semicolon. */
    readonly text: string;
}

export interface CanonicalLambdapiRequireCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'require';
    readonly open: boolean;
    readonly modules: readonly string[];
}

export interface CanonicalLambdapiFlagCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'flag';
}

export interface CanonicalLambdapiSymbolCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'symbol';
    readonly name: string;
    readonly modifiers: readonly CanonicalLambdapiSymbolModifier[];
    readonly hasBody: boolean;
}

export interface CanonicalLambdapiInductiveCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'inductive';
    readonly name: string;
    readonly constructorCount: number;
}

export interface CanonicalLambdapiRuleCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'rule';
    readonly clauseCount: number;
}

export interface CanonicalLambdapiUnificationRuleCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'unif_rule';
}

export interface CanonicalLambdapiBuiltinCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'builtin';
}

export interface CanonicalLambdapiNotationCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'notation';
}

export interface CanonicalLambdapiOpaqueCommand
    extends CanonicalLambdapiCommandBase {
    readonly kind: 'opaque';
    readonly symbols: readonly string[];
}

export type CanonicalLambdapiCommand =
    | CanonicalLambdapiRequireCommand
    | CanonicalLambdapiFlagCommand
    | CanonicalLambdapiSymbolCommand
    | CanonicalLambdapiInductiveCommand
    | CanonicalLambdapiRuleCommand
    | CanonicalLambdapiUnificationRuleCommand
    | CanonicalLambdapiBuiltinCommand
    | CanonicalLambdapiNotationCommand
    | CanonicalLambdapiOpaqueCommand;

export type CanonicalLambdapiCommandCounts = Readonly<
    Record<CanonicalLambdapiCommandKind, number>
>;

export interface CanonicalLambdapiExportInventory {
    readonly moduleId: string;
    readonly commands: readonly CanonicalLambdapiCommand[];
    readonly imports: readonly string[];
    readonly counts: CanonicalLambdapiCommandCounts;
}

export type CanonicalLambdapiExportErrorCode =
    | 'INVALID_MODULE_ID'
    | 'MISMATCHED_DELIMITER'
    | 'UNTERMINATED_STRING'
    | 'UNTERMINATED_COMMENT'
    | 'MISMATCHED_TACTIC_BLOCK'
    | 'UNTERMINATED_COMMAND'
    | 'UNSUPPORTED_COMMAND'
    | 'MALFORMED_COMMAND';

export class CanonicalLambdapiExportError extends Error {
    constructor(
        public readonly code: CanonicalLambdapiExportErrorCode,
        message: string,
        public readonly commandOrdinal?: number
    ) {
        super(message);
        this.name = 'CanonicalLambdapiExportError';
    }
}

const commandKinds: readonly CanonicalLambdapiCommandKind[] = [
    'require',
    'flag',
    'symbol',
    'inductive',
    'rule',
    'unif_rule',
    'builtin',
    'notation',
    'opaque'
];

const symbolModifiers =
    new Set<CanonicalLambdapiSymbolModifier>([
        'constant',
        'injective',
        'protected',
        'private',
        'opaque'
    ]);

const matchingDelimiter: Readonly<Record<string, string>> = {
    ')': '(',
    ']': '[',
    '}': '{'
};

const isIdentifierWordCharacter = (
    character: string | undefined
): boolean =>
    character !== undefined &&
    /[\p{L}\p{N}\p{M}_]/u.test(character);

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(
            child => deepFreeze(child)
        );
        Object.freeze(value);
    }
    return value;
};

/**
 * Split top-level commands while removing comments. Canonical exporter output
 * currently contains no comments, but accepting them makes failure fixtures
 * and future exporter presentation changes unambiguous.
 */
const splitCanonicalCommands = (input: string): readonly string[] => {
    const source = input
        .replace(/^\uFEFF/u, '')
        .replace(/\r\n?/gu, '\n');
    const commands: string[] = [];
    const delimiters: string[] = [];
    let buffer = '';
    let inString = false;
    let escaped = false;
    let lineComment = false;
    let blockCommentDepth = 0;
    let tacticBlockDepth = 0;

    for (let index = 0; index < source.length; index += 1) {
        const character = source[index];
        const next = source[index + 1];

        if (lineComment) {
            if (character === '\n') {
                lineComment = false;
                buffer += '\n';
            }
            continue;
        }

        if (blockCommentDepth > 0) {
            if (character === '/' && next === '*') {
                blockCommentDepth += 1;
                index += 1;
                continue;
            }
            if (character === '*' && next === '/') {
                blockCommentDepth -= 1;
                index += 1;
                if (blockCommentDepth === 0) buffer += ' ';
                continue;
            }
            if (character === '\n') buffer += '\n';
            continue;
        }

        if (inString) {
            buffer += character;
            if (escaped) {
                escaped = false;
            } else if (character === '\\') {
                escaped = true;
            } else if (character === '"') {
                inString = false;
            }
            continue;
        }

        if (character === '/' && next === '/') {
            lineComment = true;
            buffer += ' ';
            index += 1;
            continue;
        }

        if (character === '/' && next === '*') {
            blockCommentDepth = 1;
            buffer += ' ';
            index += 1;
            continue;
        }

        if (character === '"') {
            inString = true;
            buffer += character;
            continue;
        }

        if (
            source.startsWith('begin', index) &&
            !isIdentifierWordCharacter(source[index - 1]) &&
            !isIdentifierWordCharacter(source[index + 5])
        ) {
            tacticBlockDepth += 1;
        } else if (
            source.startsWith('end', index) &&
            !isIdentifierWordCharacter(source[index - 1]) &&
            !isIdentifierWordCharacter(source[index + 3])
        ) {
            if (tacticBlockDepth === 0) {
                throw new CanonicalLambdapiExportError(
                    'MISMATCHED_TACTIC_BLOCK',
                    `Canonical Lambdapi export has unmatched tactic end ` +
                    `at offset ${index}`
                );
            }
            tacticBlockDepth -= 1;
        }

        if (
            character === '(' ||
            character === '[' ||
            character === '{'
        ) {
            delimiters.push(character);
            buffer += character;
            continue;
        }

        if (
            character === ')' ||
            character === ']' ||
            character === '}'
        ) {
            const expected = matchingDelimiter[character];
            const actual = delimiters.pop();
            if (actual !== expected) {
                throw new CanonicalLambdapiExportError(
                    'MISMATCHED_DELIMITER',
                    `Canonical Lambdapi export has mismatched delimiter ` +
                    `${character} at offset ${index}`
                );
            }
            buffer += character;
            continue;
        }

        buffer += character;
        if (
            character === ';' &&
            delimiters.length === 0 &&
            tacticBlockDepth === 0
        ) {
            const command = buffer.trim();
            if (command.length > 0) commands.push(command);
            buffer = '';
        }
    }

    if (inString) {
        throw new CanonicalLambdapiExportError(
            'UNTERMINATED_STRING',
            'Canonical Lambdapi export ends inside a string'
        );
    }
    if (blockCommentDepth > 0) {
        throw new CanonicalLambdapiExportError(
            'UNTERMINATED_COMMENT',
            'Canonical Lambdapi export ends inside a block comment'
        );
    }
    if (delimiters.length > 0) {
        throw new CanonicalLambdapiExportError(
            'MISMATCHED_DELIMITER',
            `Canonical Lambdapi export has unclosed delimiter ` +
            delimiters[delimiters.length - 1]
        );
    }
    if (tacticBlockDepth > 0) {
        throw new CanonicalLambdapiExportError(
            'MISMATCHED_TACTIC_BLOCK',
            'Canonical Lambdapi export ends inside a tactic block'
        );
    }
    if (buffer.trim().length > 0) {
        throw new CanonicalLambdapiExportError(
            'UNTERMINATED_COMMAND',
            'Canonical Lambdapi export has non-comment text without a ' +
            'terminating semicolon'
        );
    }

    return commands;
};

interface TopLevelScan {
    readonly definitionTokenCount: number;
    readonly constructorSeparatorCount: number;
    readonly withKeywordCount: number;
    readonly rewriteArrowCount: number;
}

const findTopLevelKeyword = (
    command: string,
    keyword: string
): number => {
    const delimiters: string[] = [];
    let inString = false;
    let escaped = false;
    for (let index = 0; index < command.length; index += 1) {
        const character = command[index];
        if (inString) {
            if (escaped) {
                escaped = false;
            } else if (character === '\\') {
                escaped = true;
            } else if (character === '"') {
                inString = false;
            }
            continue;
        }
        if (character === '"') {
            inString = true;
            continue;
        }
        if (
            character === '(' ||
            character === '[' ||
            character === '{'
        ) {
            delimiters.push(character);
            continue;
        }
        if (
            character === ')' ||
            character === ']' ||
            character === '}'
        ) {
            delimiters.pop();
            continue;
        }
        if (
            delimiters.length === 0 &&
            command.startsWith(keyword, index) &&
            !isIdentifierWordCharacter(command[index - 1]) &&
            !isIdentifierWordCharacter(
                command[index + keyword.length]
            )
        ) {
            return index;
        }
    }
    return -1;
};

/**
 * Lambdapi's canonical printer puts parameters of some inductives
 * before the keyword, for example `(A : Grpd)inductive PathRecordData`.
 */
const isCanonicalInductiveParameterPrefix = (
    prefix: string
): boolean => {
    let index = 0;
    while (index < prefix.length) {
        while (/\s/u.test(prefix[index] ?? '')) index += 1;
        if (index >= prefix.length) return true;
        const opening = prefix[index];
        if (opening !== '(' && opening !== '[') return false;
        const closing = opening === '(' ? ')' : ']';
        let depth = 0;
        let inString = false;
        let escaped = false;
        for (; index < prefix.length; index += 1) {
            const character = prefix[index];
            if (inString) {
                if (escaped) {
                    escaped = false;
                } else if (character === '\\') {
                    escaped = true;
                } else if (character === '"') {
                    inString = false;
                }
                continue;
            }
            if (character === '"') {
                inString = true;
                continue;
            }
            if (character === opening) depth += 1;
            if (character === closing) {
                depth -= 1;
                if (depth === 0) {
                    index += 1;
                    break;
                }
            }
        }
        if (depth !== 0 || inString) return false;
    }
    return true;
};

/**
 * Commands produced by the splitter have balanced delimiters and terminated
 * strings, so this scan only needs to identify tokens at delimiter depth zero.
 */
const scanTopLevel = (command: string): TopLevelScan => {
    const delimiters: string[] = [];
    let inString = false;
    let escaped = false;
    let definitionTokenCount = 0;
    let constructorSeparatorCount = 0;
    let withKeywordCount = 0;
    let rewriteArrowCount = 0;

    for (let index = 0; index < command.length; index += 1) {
        const character = command[index];

        if (inString) {
            if (escaped) {
                escaped = false;
            } else if (character === '\\') {
                escaped = true;
            } else if (character === '"') {
                inString = false;
            }
            continue;
        }

        if (character === '"') {
            inString = true;
            continue;
        }

        if (
            character === '(' ||
            character === '[' ||
            character === '{'
        ) {
            delimiters.push(character);
            continue;
        }
        if (
            character === ')' ||
            character === ']' ||
            character === '}'
        ) {
            delimiters.pop();
            continue;
        }
        if (delimiters.length > 0) continue;

        if (character === '≔') definitionTokenCount += 1;
        if (character === '|') constructorSeparatorCount += 1;
        if (character === '↪') rewriteArrowCount += 1;

        if (
            command.startsWith('with', index) &&
            !isIdentifierWordCharacter(command[index - 1]) &&
            !isIdentifierWordCharacter(command[index + 4])
        ) {
            withKeywordCount += 1;
            index += 3;
        }
    }

    return {
        definitionTokenCount,
        constructorSeparatorCount,
        withKeywordCount,
        rewriteArrowCount
    };
};

const malformed = (
    ordinal: number,
    description: string
): never => {
    throw new CanonicalLambdapiExportError(
        'MALFORMED_COMMAND',
        `Malformed canonical Lambdapi command ${ordinal}: ${description}`,
        ordinal
    );
};

const classifyCommand = (
    text: string,
    ordinal: number
): CanonicalLambdapiCommand => {
    if (/^require(?:\s|$)/u.test(text)) {
        const match =
            /^require\s+(?:(open)\s+)?([^;]+);$/u.exec(text);
        if (match === null) {
            return malformed(ordinal, 'invalid require command');
        }
        const modules = match[2].trim().split(/\s+/u);
        if (
            modules.length === 0 ||
            modules.some(module =>
                !/^[\p{L}\p{N}_]+(?:\.[\p{L}\p{N}_]+)*$/u
                    .test(module)
            )
        ) {
            return malformed(ordinal, 'invalid required module ID');
        }
        return {
            ordinal,
            kind: 'require',
            text,
            open: match[1] === 'open',
            modules
        };
    }

    if (/^flag(?:\s|$)/u.test(text)) {
        if (
            !/^flag\s+"(?:\\.|[^"\\])*"\s+(?:on|off);$/u.test(text)
        ) {
            return malformed(ordinal, 'invalid flag command');
        }
        return { ordinal, kind: 'flag', text };
    }

    const symbolMatch =
        /^((?:(?:constant|injective|protected|private|opaque)\s+)*)symbol\s+([^\s:[(;]+)(?:\s|:|\[|\(|;)/u
            .exec(text);
    if (symbolMatch !== null) {
        const modifiers = symbolMatch[1].trim().length === 0
            ? []
            : symbolMatch[1].trim().split(/\s+/u);
        if (
            modifiers.some(
                modifier => !symbolModifiers.has(
                    modifier as CanonicalLambdapiSymbolModifier
                )
            ) ||
            new Set(modifiers).size !== modifiers.length
        ) {
            return malformed(ordinal, 'invalid symbol modifiers');
        }
        const topLevel = scanTopLevel(text);
        return {
            ordinal,
            kind: 'symbol',
            text,
            name: symbolMatch[2],
            modifiers:
                modifiers as CanonicalLambdapiSymbolModifier[],
            // Later definition tokens may occur inside the body (for example
            // in canonical let syntax); the first separates type and body.
            hasBody: topLevel.definitionTokenCount >= 1
        };
    }

    const inductiveIndex = findTopLevelKeyword(text, 'inductive');
    if (
        inductiveIndex >= 0 &&
        isCanonicalInductiveParameterPrefix(
            text.slice(0, inductiveIndex)
        )
    ) {
        const inductiveText = text.slice(inductiveIndex);
        const match =
            /^inductive\s+([^\s:[(;]+)(?:\s|:|\[|\(|;)/u
                .exec(inductiveText);
        if (match === null) {
            return malformed(ordinal, 'invalid inductive command');
        }
        const topLevel = scanTopLevel(text);
        if (topLevel.definitionTokenCount < 1) {
            return malformed(
                ordinal,
                'inductive command must have one top-level definition token'
            );
        }
        return {
            ordinal,
            kind: 'inductive',
            text,
            name: match[1],
            constructorCount: topLevel.constructorSeparatorCount
        };
    }

    if (/^rule(?:\s|$)/u.test(text)) {
        const topLevel = scanTopLevel(text);
        if (
            topLevel.rewriteArrowCount !==
            1 + topLevel.withKeywordCount
        ) {
            return malformed(
                ordinal,
                'runtime rule clauses must each have one top-level arrow'
            );
        }
        return {
            ordinal,
            kind: 'rule',
            text,
            clauseCount: 1 + topLevel.withKeywordCount
        };
    }

    if (/^unif_rule(?:\s|$)/u.test(text)) {
        const topLevel = scanTopLevel(text);
        if (
            topLevel.rewriteArrowCount !== 1 ||
            !text.includes('≡')
        ) {
            return malformed(ordinal, 'invalid unification rule command');
        }
        return { ordinal, kind: 'unif_rule', text };
    }

    if (/^builtin(?:\s|$)/u.test(text)) {
        const topLevel = scanTopLevel(text);
        if (
            !/^builtin\s+"(?:\\.|[^"\\])*"\s+/u.test(text) ||
            topLevel.definitionTokenCount !== 1
        ) {
            return malformed(ordinal, 'invalid builtin command');
        }
        return { ordinal, kind: 'builtin', text };
    }

    if (/^notation(?:\s|$)/u.test(text)) {
        if (
            !/^notation\s+\S+\s+(?:(?:infix|prefix|postfix)\s+\d+|quantifier);$/u
                .test(text)
        ) {
            return malformed(ordinal, 'invalid notation command');
        }
        return { ordinal, kind: 'notation', text };
    }

    if (/^opaque(?:\s|$)/u.test(text)) {
        const match = /^opaque\s+([^;]+);$/u.exec(text);
        if (match === null) {
            return malformed(ordinal, 'invalid opaque command');
        }
        const symbols = match[1].trim().split(/\s+/u);
        if (
            symbols.length === 0 ||
            symbols.some(symbol => symbol.length === 0)
        ) {
            return malformed(ordinal, 'invalid opaque symbol list');
        }
        return { ordinal, kind: 'opaque', text, symbols };
    }

    const prefix = text.replace(/\s+/gu, ' ').slice(0, 80);
    throw new CanonicalLambdapiExportError(
        'UNSUPPORTED_COMMAND',
        `Unsupported canonical Lambdapi command ${ordinal}: ${prefix}`,
        ordinal
    );
};

export function parseCanonicalLambdapiExport(
    moduleId: string,
    source: string
): CanonicalLambdapiExportInventory {
    if (
        moduleId.trim() !== moduleId ||
        !/^[\p{L}\p{N}_]+(?:\.[\p{L}\p{N}_]+)*$/u.test(moduleId)
    ) {
        throw new CanonicalLambdapiExportError(
            'INVALID_MODULE_ID',
            `Invalid canonical Lambdapi module ID: ${moduleId}`
        );
    }

    const commands = splitCanonicalCommands(source).map(
        (text, index) => classifyCommand(text, index)
    );
    const counts = Object.fromEntries(
        commandKinds.map(kind => [kind, 0])
    ) as Record<CanonicalLambdapiCommandKind, number>;
    const imports: string[] = [];

    commands.forEach(command => {
        counts[command.kind] += 1;
        if (command.kind === 'require') {
            imports.push(...command.modules);
        }
    });

    return deepFreeze({
        moduleId,
        commands,
        imports,
        counts
    });
}
