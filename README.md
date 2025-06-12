# Emdash — A Dependently Typed Logical Framework for Computational Category Theory

For a comprehensive and detailed overview of the Emdash project, its architecture, core features, and testing, please refer to [README2.md](README2.md).

## Overview
`emdash` is a TypeScript-based core for a dependently typed language, built with a strong emphasis on integrating concepts from category theory as first-class citizens. It provides a robust and extensible type theory kernel, featuring dependent types, a sophisticated elaboration engine, a powerful unification algorithm, and a reduction system that supports equational reasoning. The system aims to provide a flexible foundation for computational type theory and functorial programming, drawing inspiration from systems like Agda and Lambdapi.

## Getting Started

To set up the project and run tests, follow these steps:

1.  **Install Dependencies**:
    ```bash
    npm install
    ```

2.  **Run Tests**:
    ```bash
    npm test
    ```

## Core Components (Brief)

*   **Type Theory Kernel**: Implements dependent functions (Pi-types), lambda abstractions, and a type universe.
*   **Elaboration Engine**: Performs bidirectional type checking, handles implicit arguments, and generates unification constraints.
*   **Unification**: Solves constraints, including higher-order pattern unification and occurs checks.
*   **Reduction & Equality**: Supports β-reduction, η-contraction, and user-defined rewrite rules for term convertibility.
*   **Pattern Matching**: Provides higher-order pattern matching with scope annotations.
*   **Category Theory Integration**: Natively supports categories, functors, and natural transformations with functorial elaboration.
*   **Extensibility**: Allows for user-defined global constants, rewrite rules, and unification rules.
*   **Proof Mode**: (Preliminary) Provides interactive proof assistance functionalities.
*   **Parser**: Converts human-readable syntax into the internal abstract syntax tree.

---
**For detailed documentation on the project structure, features, and testing, please see [README2.md](README2.md).** 