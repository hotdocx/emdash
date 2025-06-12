/**
 * @file src/parser2.ts
 * @description A new parser for emdash with an alternative, more elaborate syntax.
 * This parser avoids Unicode characters and supports more complex binder structures.
 */

import * as P from 'parsimmon';
import { Term, Icit, Type, Var, Lam, App, Pi, Let, Hole } from './types';
import { replaceFreeVar } from './pattern';
import { globalDefs, isKernelConstantSymbolStructurally, freshHoleName } from './state';

// Helper to create a parser that consumes trailing whitespace
function token<T>(parser: P.Parser<T>): P.Parser<T> {
    return parser.skip(P.optWhitespace);
}

const keywords = ['let', 'in', 'Type', 'fun'];

// We need to pass the list of bound variables down the recursive calls
// to correctly parse variables. A variable is either a local bound variable
// or a global definition.
function buildParser(boundVars: string[]) {
    type BinderInfo = { name: string, type?: Term, icit: Icit };

    const lang = P.createLanguage({
        Expr: r => P.alt(r.Let, r.Lam, r.Pi, r.Arrow),

        Let: r => P.seq(
            token(P.string('let')),
            r.Identifier,
            P.alt(
                P.seq(token(P.string(':')), r.Expr).map(res => res[1]),
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
        
        Lam: r => P.seq(
            token(P.alt(P.string('\\'), P.string('fun'))),
            r.LamBinderList,
            token(P.string('.'))
        ).chain(([_lam, binders, _dot]) => {
            const newBounderNames = binders.map(b => b.name);
            const bodyParser = buildParser([...boundVars, ...newBounderNames]).Expr;
            return bodyParser.map(body => 
                binders.reduceRight((acc: Term, b: BinderInfo) => {
                    const bodyFn = (v: Term) => replaceFreeVar(acc, b.name, v);
                    if (b.type) return Lam(b.name, b.icit, b.type, bodyFn);
                    return Lam(b.name, b.icit, bodyFn);
                }, body)
            );
        }),

        Pi: r => P.seq(
            r.DefiniteBinderList,
            token(P.string('->'))
        ).chain(([binders, _arrow]) => {
            const newBounderNames = binders.map(b => b.name);
            const bodyParser = buildParser([...boundVars, ...newBounderNames]).Expr;
            return bodyParser.map(body => {
                return binders.reduceRight((acc: Term, b: BinderInfo) => {
                    if (!b.type) throw new Error(`Pi binder ${b.name} must have a type.`);
                    const bodyFn = (v: Term) => replaceFreeVar(acc, b.name, v);
                    return Pi(b.name, b.icit, b.type, bodyFn);
                }, body);
            });
        }),

        Arrow: r => r.App.chain(head => 
            P.seq(token(P.string('->')), r.Expr)
             .map(([_arrow, tail]) => Pi('_', Icit.Expl, head, () => tail))
             .fallback(head)
        ),

        App: r => P.seq(r.Atom, r.Arg.many()).map(([h, args]) => args.reduce((acc, { term, icit }) => App(acc, term, icit), h)),
        
        Arg: r => P.alt(
            r.Atom.map(t => ({ term: t, icit: Icit.Expl })), 
            r.Expr.wrap(token(P.string('{')), token(P.string('}'))).map(t => ({ term: t, icit: Icit.Impl }))
        ),
        
        Atom: r => P.alt(
            r.Hole,
            r.Type, 
            r.Var,
            r.Parens
        ),

        Type: () => token(P.string('Type')).map(() => Type()),
        
        Identifier: () => token(P.regexp(/[a-zA-Z_][a-zA-Z0-9_$?]*/))
            .assert(name => !keywords.includes(name), name => `keyword '${name}' cannot be an identifier`),

        Var: r => r.Identifier.chain(name => {
            if (name === '_') return P.fail('`_` cannot be used as a variable name here.');
            if (boundVars.includes(name)) return P.succeed(Var(name, true));
            if (globalDefs.has(name) || isKernelConstantSymbolStructurally(Var(name))) return P.succeed(Var(name, false));
            return P.succeed(Var(name, false));
        }),

        Hole: () => token(P.string('_')).map(() => Hole(freshHoleName())),

        Parens: r => r.Expr.wrap(token(P.string('(')), token(P.string(')'))),

        DefiniteBinder: r => P.alt(
            r.ExplicitTypedBinderGroup,
            r.ImplicitTypedBinderGroup,
            r.ImplicitUntypedBinderGroup
        ),

        DefiniteBinderList: r => r.DefiniteBinder.atLeast(1).map(b => b.flat()),

        LamBinder: r => P.alt(
            r.ExplicitTypedBinderGroup,
            r.ImplicitTypedBinderGroup,
            r.ImplicitUntypedBinderGroup,
            r.SingleUntypedExplicitBinder.map(b => [b])
        ),

        LamBinderList: r => r.LamBinder.atLeast(1).map(b => b.flat()),
        
        ExplicitTypedBinderGroup: r => P.seq(
            r.Identifier.atLeast(1).wrap(token(P.string('(')), token(P.string(':'))),
            r.Expr.skip(token(P.string(')')))
        ).map(([names, type]) => names.map(name => ({ name, type, icit: Icit.Expl }))),

        ImplicitTypedBinderGroup: r => P.seq(
            r.Identifier.atLeast(1).wrap(token(P.string('{')), token(P.string(':'))),
            r.Expr.skip(token(P.string('}')))
        ).map(([names, type]) => names.map(name => ({ name, type, icit: Icit.Impl }))),

        ImplicitUntypedBinderGroup: r => r.Identifier.atLeast(1)
            .wrap(token(P.string('{')), token(P.string('}')))
            .map(names => names.map(name => ({ name, type: undefined, icit: Icit.Impl }))),
            
        SingleUntypedExplicitBinder: r => r.Identifier.map(name => ({ name, type: undefined, icit: Icit.Expl })),
    });
    return lang;
}

/**
 * Parses a string into a Term syntax tree using the new syntax.
 * @param source The string to parse.
 * @returns The parsed Term.
 * @throws An error if parsing fails.
 */
export function parseToSyntaxTree2(source: string): Term {
    const lang = buildParser([]);
    const result = lang.Expr.parse(source);
    if (result.status) return result.value;
    throw new Error(`Parsing failed: ${P.formatError(source, result)}`);
} 