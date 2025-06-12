import * as P from 'parsimmon';
import { Term, Icit, Type, Var, Lam, App, Pi } from './types';

// Helper to create a parser that consumes trailing whitespace
function token<T>(parser: P.Parser<T>): P.Parser<T> {
    return parser.skip(P.optWhitespace);
}

// Language definition for Parsimmon. Note: `_isAnnotated` etc. are not needed here.
// The output is a purely syntactic tree.
const lang = P.createLanguage({
    Expr: r => P.alt(r.Lam, r.Pi, r.Arrow),
    Arrow: r => P.seq(r.App, P.seq(token(P.string('->')), r.Arrow).many()).map(([h, t]) => t.reduceRight((acc, [_, r]) => Pi('_', Icit.Expl, acc, () => r), h)),
    App: r => P.seq(r.Atom, r.Arg.many()).map(([h, args]) => args.reduce((acc, { term, icit }) => App(acc, term, icit), h)),
    Arg: r => P.alt(r.Atom.map(t => ({ term: t, icit: Icit.Expl })), r.Expr.wrap(token(P.string('{')), token(P.string('}'))).map(t => ({ term: t, icit: Icit.Impl }))),
    Atom: r => P.alt(r.Type, r.Var, r.Parens),
    Type: () => token(P.string('Type')).map(() => Type()),
    Identifier: () => token(P.regexp(/[a-zA-Z_][a-zA-Z0-9_$?]*/)), // Allow $ and ? for pattern vars/holes later
    Var: r => r.Identifier.map(name => Var(name)),
    Parens: r => r.Expr.wrap(token(P.string('(')), token(P.string(')'))),
    Lam: r => P.seq(token(P.alt(P.string('λ'), P.string('\\'))), r.Binder.atLeast(1), token(P.string('.')), r.Expr).map(([_, binders, _dot, body]) => binders.reduceRight((acc, b) => Lam(b.name, b.icit, b.type, () => acc), body)),
    Pi: r => P.seq(token(P.string('Π')), r.Binder.atLeast(1), token(P.string('.')), r.Expr).map(([_, binders, _dot, body]) => binders.reduceRight((acc, b) => Pi(b.name, b.icit, b.type!, () => acc), body)),
    Binder: r => P.alt(
        P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('(')), token(P.string(')'))).map(([name, type]) => ({ name, type, icit: Icit.Expl })),
        P.seq(r.Identifier.skip(token(P.string(':'))), r.Expr).wrap(token(P.string('{')), token(P.string('}'))).map(([name, type]) => ({ name, type, icit: Icit.Impl })),
        r.Identifier.map(name => ({ name, type: undefined, icit: Icit.Expl }))
    ),
});

export function parseToSyntaxTree(source: string): Term {
    const result = lang.Expr.parse(source);
    if (result.status) return result.value;
    throw new Error(`Parsing failed: ${P.formatError(source, result)}`);
}