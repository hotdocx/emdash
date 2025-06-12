import * as P from 'parsimmon';
import { Term, Icit, Type, Var, Lam, App, Pi, Let } from './types';

// Helper to create a parser that consumes trailing whitespace
function token<T>(parser: P.Parser<T>): P.Parser<T> {
    return parser.skip(P.optWhitespace);
}

function replaceFreeVar(term: Term, name: string, repl: Term, bound: Set<string> = new Set()): Term {
    switch (term.tag) {
        case 'Var':
            return term.name === name && !bound.has(name) ? repl : term;
        case 'App':
            return App(
                replaceFreeVar(term.func, name, repl, bound),
                replaceFreeVar(term.arg, name, repl, bound),
                term.icit
            );
        case 'Lam': {
            const newBound = new Set(bound);
            if (term.paramName === name) return term; // Shadowing
            newBound.add(term.paramName);
            const ptype = term.paramType ? replaceFreeVar(term.paramType, name, repl, bound) : undefined;
            const body = term.body(Var(term.paramName, true));
            const newBody = replaceFreeVar(body, name, repl, newBound);
            if (ptype) {
                return Lam(term.paramName, term.icit, ptype, (v) => replaceFreeVar(newBody, term.paramName, v));
            }
            return Lam(term.paramName, term.icit, (v) => replaceFreeVar(newBody, term.paramName, v));
        }
        case 'Pi': {
            const newBound = new Set(bound);
            if (term.paramName === name) return term; // Shadowing
            newBound.add(term.paramName);
            const ptype = replaceFreeVar(term.paramType, name, repl, bound);
            const body = term.bodyType(Var(term.paramName, true));
            const newBody = replaceFreeVar(body, name, repl, newBound);
            return Pi(term.paramName, term.icit, ptype, (v) => replaceFreeVar(newBody, term.paramName, v));
        }
        case 'Let': {
            const ltype = term.letType ? replaceFreeVar(term.letType, name, repl, bound) : undefined;
            const ldef = replaceFreeVar(term.letDef, name, repl, bound);
            const newBound = new Set(bound);
            if (term.letName === name) { // Shadowing for body
                 if (ltype) return Let(term.letName, ltype, ldef, term.body);
                 return Let(term.letName, ldef, term.body);
            }
            newBound.add(term.letName);
            const body = term.body(Var(term.letName, true));
            const newBody = replaceFreeVar(body, name, repl, newBound);
            const bodyFn = (v: Term) => replaceFreeVar(newBody, term.letName, v);
            if (ltype) {
                return Let(term.letName, ltype, ldef, bodyFn);
            }
            return Let(term.letName, ldef, bodyFn);
        }
        case 'Type':
            return term;
        default:
            return term;
    }
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