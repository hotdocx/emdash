import * as P from 'parsimmon';
import { Term, Icit, Type, Var, Lam, App, Pi, Let } from './types';
import { replaceFreeVar } from './pattern';

// Helper to create a parser that consumes trailing whitespace
function token<T>(parser: P.Parser<T>): P.Parser<T> {
    return parser.skip(P.optWhitespace);
}



// Language definition for Parsimmon.
const lang = P.createLanguage({
    Expr: r => P.alt(r.Let, r.Lam, r.Pi, r.Arrow),
    Arrow: r => P.seq(r.App, P.seq(token(P.string('->')), r.Arrow).many()).map(([h, t]) => t.reduceRight((acc, [_, r]) => Pi('_', Icit.Expl, acc, () => r), h)),
    App: r => P.seq(r.Atom, r.Arg.many()).map(([h, args]) => args.reduce((acc, { term, icit }) => App(acc, term, icit), h)),
    Arg: r => P.alt(r.Atom.map(t => ({ term: t, icit: Icit.Expl })), r.Expr.wrap(token(P.string('{')), token(P.string('}'))).map(t => ({ term: t, icit: Icit.Impl }))),
    Atom: r => P.alt(r.Type, r.Var, r.Parens),
    Type: () => token(P.string('Type')).map(() => Type()),
    Identifier: () => token(P.regexp(/[a-zA-Z_][a-zA-Z0-9_$?]*/)),
    Var: r => r.Identifier.map(name => Var(name)),
    Parens: r => r.Expr.wrap(token(P.string('(')), token(P.string(')'))),

    Lam: r => P.seq(token(P.alt(P.string('λ'), P.string('\\'))), r.Binder.atLeast(1), token(P.string('.')), r.Expr).map(([_, binders, _dot, body]) =>
        binders.reduceRight((acc, b) => {
            const bodyFn = (v: Term) => replaceFreeVar(acc, b.name, v);
            if (b.type) return Lam(b.name, b.icit, b.type, bodyFn);
            return Lam(b.name, b.icit, bodyFn);
        }, body)
    ),

    Pi: r => P.seq(token(P.string('Π')), r.Binder.atLeast(1), token(P.string('.')), r.Expr).map(([_, binders, _dot, body]) =>
        binders.reduceRight((acc, b) => Pi(b.name, b.icit, b.type!, (v: Term) => replaceFreeVar(acc, b.name, v)), body)
    ),

    Let: r => P.seq(
        token(P.string('let')),
        r.Identifier,
        P.alt(
            P.seq(token(P.string(':')), r.Arrow).map((res) => res[1]),
            P.succeed(undefined)
        ),
        token(P.string('=')),
        r.Arrow,
        token(P.string('in')),
        r.Expr
    ).map((res) => {
        const name: string = res[1];
        const type: Term | undefined = res[2];
        const def: Term = res[4];
        const body: Term = res[6];
        const bodyFn = (v: Term) => replaceFreeVar(body, name, v);
        if (type) {
            return Let(name, type, def, bodyFn);
        }
        return Let(name, def, bodyFn);
    }),

    Binder: r => P.alt(
        P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('(')), token(P.string(')'))).map(([name, type]) => ({ name, type, icit: Icit.Expl })),
        P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('{')), token(P.string('}'))).map(([name, type]) => ({ name, type, icit: Icit.Impl })),
        r.Identifier.wrap(token(P.string('(')), token(P.string(')'))).map(name => ({ name, type: undefined, icit: Icit.Expl })),
        r.Identifier.wrap(token(P.string('{')), token(P.string('}'))).map(name => ({ name, type: undefined, icit: Icit.Impl })),
        r.Identifier.map(name => ({ name, type: undefined, icit: Icit.Expl }))
    ),
});

export function parseToSyntaxTree(source: string): Term {
    const result = lang.Expr.parse(source);
    if (result.status) return result.value;
    throw new Error(`Parsing failed: ${P.formatError(source, result)}`);
}