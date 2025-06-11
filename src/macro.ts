// src/macros.ts

import { MacroError, $$raw } from 'ts-macros';
import * as ts from 'typescript';
import { parseToSyntaxTree } from './parser-logic';
import { Term, Icit } from './types';

// The new `term` macro. It must be prefixed with `$` to be recognized by ts-macros.
// It will be used as a function call: `$term("...source...")`
// We use `$$raw` to get access to the compiler context and generate the AST.
export function $term(source: string): Term {
    return $$raw!<Term>(({ factory, ...ctx }, call) => {
        let sourceText: string;
        const arg = call.arguments[0];

        if (ts.isStringLiteral(arg)) {
            sourceText = arg.text;
        } else if (ts.isNoSubstitutionTemplateLiteral(arg)) {
            sourceText = arg.rawText ?? '';
        }
        else {
            throw new MacroError(arg, "Macro expects a single string literal or template literal argument.");
        }

        let parsedTerm: Term;
        try {
            parsedTerm = parseToSyntaxTree(sourceText);
        } catch (e: any) {
            throw new MacroError(call, `Failed to parse term: ${e.message}`);
        }

        // We cannot use ctx.addUtil in $$raw. We need to handle imports manually
        // by creating identifiers that will resolve to the imported names at the call site.
        const Var = factory.createIdentifier('Var');
        const Lam = factory.createIdentifier('Lam');
        const App = factory.createIdentifier('App');
        const Pi = factory.createIdentifier('Pi');
        const Type = factory.createIdentifier('Type');
        const IcitEnum = factory.createIdentifier('Icit');
        // The `replaceFreeVar` function is more complex as it's not a type/constructor.
        // For now, let's assume it's available in the scope where the macro is called.
        // A better solution might be needed if it's not.
        const replaceFreeVar = factory.createIdentifier('replaceFreeVar');


        const getIcitAST = (icit: Icit) => factory.createPropertyAccessExpression(
            IcitEnum,
            icit === Icit.Expl ? 'Expl' : 'Impl'
        );

        function termToAST(term: Term): ts.Expression {
            switch (term.tag) {
                case 'Var':
                    return factory.createCallExpression(Var, undefined, [
                        factory.createStringLiteral(term.name)
                    ]);
                case 'Type':
                    return factory.createCallExpression(Type, undefined, []);
                case 'App':
                    return factory.createCallExpression(App, undefined, [
                        termToAST(term.func),
                        termToAST(term.arg),
                        getIcitAST(term.icit)
                    ]);
                case 'Lam': {
                    const paramName = term.paramName;
                    // The HOAS representation needs careful reconstruction.
                    // The original macro used a helper function for substitution.
                    // In $$raw, we have to construct the AST for the higher-order function.
                    const hoasBody = factory.createArrowFunction(
                        undefined,
                        undefined,
                        [factory.createParameterDeclaration(undefined, undefined, "v")],
                        undefined,
                        factory.createToken(ts.SyntaxKind.EqualsGreaterThanToken),
                        // The body of the lambda is created by applying the HOAS function
                        // to a new variable `v`. The challenge is that `term.body` is a JS function.
                        // We must convert `term.body` into an AST that represents that function.
                        // This is a complex task. For now, we'll replicate the old logic's structure,
                        // assuming a `replaceFreeVar` is available.
                        termToAST(term.body({ tag: 'Var', name: paramName, isLambdaBound: true }))
                    );
                    
                    let args: ts.Expression[];
                    if (term.paramType) {
                        args = [
                            factory.createStringLiteral(paramName),
                            getIcitAST(term.icit),
                            termToAST(term.paramType),
                            hoasBody
                        ];
                    } else {
                        // The type is inferred if paramType is missing. The constructor handles this overload.
                        args = [
                            factory.createStringLiteral(paramName),
                            getIcitAST(term.icit),
                            hoasBody
                        ];
                    }
                    return factory.createCallExpression(Lam, undefined, args);
                }
                case 'Pi': {
                     const paramName = term.paramName;
                     const hoasBodyType = factory.createArrowFunction(
                        undefined,
                        undefined,
                        [factory.createParameterDeclaration(undefined, undefined, "v")],
                        undefined,
                        factory.createToken(ts.SyntaxKind.EqualsGreaterThanToken),
                        termToAST(term.bodyType({ tag: 'Var', name: paramName, isLambdaBound: true }))
                    );
                    
                    return factory.createCallExpression(Pi, undefined, [
                        factory.createStringLiteral(paramName),
                        getIcitAST(term.icit),
                        termToAST(term.paramType),
                        hoasBodyType
                    ]);
                }
                default:
                    // This is a compile-time error
                    ctx.error(call, `AST generation not implemented for term tag: ${(term as any).tag}`);
                    return factory.createNull();
            }
        }
        
        return termToAST(parsedTerm);
    });
}