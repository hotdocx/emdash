import * as P from 'parsimmon';
import { Term, Icit, Type, Var, Lam, App, Pi, Let } from './types';
import { replaceFreeVar } from './pattern';
import { globalDefs, isKernelConstantSymbolStructurally } from './state';

// Helper to create a parser that consumes trailing whitespace
function token<T>(parser: P.Parser<T>): P.Parser<T> {
    return parser.skip(P.optWhitespace);
}

const keywords = ['let', 'in', 'Type'];

// We need to pass the list of bound variables down the recursive calls
// to correctly parse variables. A variable is either a local bound variable
// or a global definition.
function buildParser(boundVars: string[]) {
    const lang = P.createLanguage({
        Expr: r => P.alt(r.Let, r.Lam, r.Pi, r.Arrow),

        Arrow: r => P.seq(r.App, P.seq(token(P.string('->')), r.Arrow).many()).map(([h, t]) => t.reduceRight((acc, [_, r]) => Pi('_', Icit.Expl, acc, () => r), h)),
        
        App: r => P.seq(r.Atom, r.Arg.many()).map(([h, args]) => args.reduce((acc, { term, icit }) => App(acc, term, icit), h)),
        
        Arg: r => P.alt(r.Atom.map(t => ({ term: t, icit: Icit.Expl })), r.Expr.wrap(token(P.string('{')), token(P.string('}'))).map(t => ({ term: t, icit: Icit.Impl }))),
        
        Atom: r => P.alt(r.Type, r.Var, r.Parens),

        Type: () => token(P.string('Type')).map(() => Type()),
        
        Identifier: () => token(P.regexp(/[a-zA-Z_][a-zA-Z0-9_$?]*/))
            .assert(name => !keywords.includes(name), name => `keyword '${name}' cannot be an identifier`),

        Var: r => r.Identifier.or(token(P.string('Type'))).chain(name => {
            if (boundVars.includes(name)) {
                return P.succeed(Var(name, true));
            }
            if (globalDefs.has(name) || isKernelConstantSymbolStructurally(Var(name)) || name === 'Type') {
                return P.succeed(Var(name, false));
            }
            return P.succeed(Var(name, false)); // Assume global, to be checked by elaboration
        }),

        Parens: r => r.Expr.wrap(token(P.string('(')), token(P.string(')'))),

        Binder: r => P.alt(
            P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('(')), token(P.string(')'))).map(([name, type]) => ({ name, type, icit: Icit.Expl })),
            P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('{')), token(P.string('}'))).map(([name, type]) => ({ name, type, icit: Icit.Impl })),
            r.Identifier.wrap(token(P.string('(')), token(P.string(')'))).map(name => ({ name, type: undefined, icit: Icit.Expl })),
            r.Identifier.wrap(token(P.string('{')), token(P.string('}'))).map(name => ({ name, type: undefined, icit: Icit.Impl })),
            r.Identifier.map(name => ({ name, type: undefined, icit: Icit.Expl }))
        ),

        Lam: r => P.seq(
            token(P.alt(P.string('λ'), P.string('\\'))),
            r.Binder.atLeast(1),
            token(P.string('.'))
        ).chain(([_lam, binders, _dot]) => {
            const newBounderNames = (binders as {name: string}[]).map(b => b.name);
            const bodyParser = buildParser([...boundVars, ...newBounderNames]).Expr;
            return bodyParser.map(body => 
                (binders as any[]).reduceRight((acc: Term, b: any) => {
                    const bodyFn = (v: Term) => replaceFreeVar(acc, b.name, v);
                    if (b.type) return Lam(b.name, b.icit, b.type, bodyFn);
                    return Lam(b.name, b.icit, bodyFn);
                }, body)
            );
        }),

        Pi: r => P.seq(
            token(P.string('Π')),
            r.Binder.atLeast(1),
            token(P.string('.'))
        ).chain(([_pi, binders, _dot]) => {
            const newBounderNames = (binders as {name: string}[]).map(b => b.name);
            const bodyTypeParser = buildParser([...boundVars, ...newBounderNames]).Expr;
            return bodyTypeParser.map(body => 
                (binders as any[]).reduceRight((acc: Term, b: any) => Pi(b.name, b.icit, b.type!, (v: Term) => replaceFreeVar(acc, b.name, v)), body)
            );
        }),

        Let: r => P.seq(
            token(P.string('let')),
            r.Identifier,
            P.alt(
                P.seq(token(P.string(':')), r.Arrow).map(res => res[1]),
                P.succeed(undefined)
            ),
            token(P.string('=')),
            r.Expr,
            token(P.string('in'))
        ).chain(([_, name, type, _eq, def, _in]) => {
            const bodyParser = buildParser([...boundVars, name as string]).Expr;
            return bodyParser.map(body => {
                const bodyFn = (v: Term) => replaceFreeVar(body, name as string, v);
                if (type) {
                    return Let(name as string, type as Term, def as Term, bodyFn);
                }
                return Let(name as string, def as Term, bodyFn);
            });
        }),
    });
    return lang;
}

export function parseToSyntaxTree(source: string): Term {
    const lang = buildParser([]);
    const result = lang.Expr.parse(source);
    if (result.status) return result.value;
    throw new Error(`Parsing failed: ${P.formatError(source, result)}`);
}