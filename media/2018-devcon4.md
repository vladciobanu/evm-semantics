---
title: 'K, KEVM [@hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf] and KLab Workshop'
author:
-   Denis Erfurt
-   Everett Hildenbrandt
-   Lev Livnev
-   Martin Lundfall
institute:
-   DappHub
-   Runtime Verification, Inc.
date: '\today'
theme: metropolis
fontsize: 10pt
header-includes:
-   \newcommand{\K}{\ensuremath{\mathbb{K}}}
-   \newcommand{\vect}[1]{\ensuremath{\overrightarrow{#1}}}
csl: ieee.csl
---

Overview
--------

1.  \K{} Framework
2.  KEVM: A formalization in \K{}
3.  KLab: Formal verification for KEVM

### Links

-   K Repository: <https://github.com/kframework/k>
-   KEVM Repository: <https://github.com/kframework/evm-semantics>
-   KLab Repository: <https://github.com/dapphub/klab>
-   DappHub: <https://dapp.coop> **TODO**: Check this link
-   Runtime Verification: <https://runtimeverification.com>

\K{} Framework
==============

The Vision: Language Independence
---------------------------------

Separate development of PL software into two tasks:

. . .

### The Programming Language

PL expert builds rigorous and formal spec of the language in a high-level human-readable semantic framework.

. . .

### The Tooling

Build each tool *once*, and apply it to every language, eg.:

-   Parser
-   Interpreter
-   Debugger
-   Compiler
-   Model Checker
-   Program Verifier

The Vision: Language Independence
---------------------------------

![K Tooling Overview](media/images/k-overview.png)

Current Semantics
-----------------

Many languages have full or partial \K{} semantics, this lists some notable ones (and their primary usage).

-   [C](https://github.com/kframework/c-semantics): detecting undefined behavior
-   [Java](https://github.com/kframework/java-semantics): detecting racy code
-   [EVM](https://github.com/kframework/evm-semantics): verifying smart contracts
-   [LLVM](https://github.com/kframework/llvm-semantics): compiler validation (to x86)
-   [JavaScript](https://github.com/kframework/javascript-semantics): finding disagreements between JS engines
-   [P4](https://github.com/kframework/p4-semantics): SDN data-layer verification
-   many others ...

\K{} Specifications: Syntax
---------------------------

Concrete syntax built using EBNF style:

```k
    syntax Exp ::= Int | Id | "(" Exp ")" [bracket]
                 | Exp "*" Exp
                 > Exp "+" Exp // looser binding

    syntax Stmt ::= Id ":=" Exp
                  | Stmt ";" Stmt
                  | "return" Exp
```

. . .

This would allow correctly parsing programs like:

```imp
    a := 3 * 2;
    b := 2 * a + 5;
    return b
```

\K{} Specifications: Configuration
----------------------------------

Tell \K{} about the structure of your execution state.
For example, a simple imperative language might have:

```k
    configuration <k>     $PGM:Program </k>
                  <env>   .Map         </env>
                  <store> .Map         </store>
```

. . .

-   `<k>` will contain the initial parsed program
-   `<env>` contains bindings of variable names to store locations
-   `<store>` contains bindings of store locations to integers

\K{} Specifications: Transition Rules
-------------------------------------

Using the above grammar and configuration:

. . .

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

. . .

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

Example Execution
-----------------

### Program

```imp
    a := 3 * 2;
    b := 2 * a + 5;
    return b
```

### Initial Configuration

```k
    <k>     a := 3 * 2 ; b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 0    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>     a := 6 ~> b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 0    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>               b := 2 * a + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>     a ~> b := 2 * [] + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>     6 ~> b := 2 * [] + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable lookup

```k
    rule <k> X:Id => V ... </k>
         <env>   ...  X |-> SX ... </env>
         <store> ... SX |-> V  ... </store>
```

### Next Configuration

```k
    <k>          b := 2 * 6 + 5 ; return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>     b := 17 ~> return b </k>
    <env>   a |-> 0    b |-> 1 </env>
    <store> 0 |-> 6    1 |-> 0 </store>
```

Example Execution (cont.)
-------------------------

### Variable assignment

```k
    rule <k> X := I:Int => . ... </k>
         <env>   ...  X |-> SX       ... </env>
         <store> ... SX |-> (V => I) ... </store>
```

### Next Configuration

```k
    <k>                return b </k>
    <env>   a |-> 0    b |-> 1  </env>
    <store> 0 |-> 6    1 |-> 17 </store>
```

KEVM: Status and Current Uses
=============================

Correctness and Performance [^outdated]
---------------------------------------

-   Pass the VMTests and GeneralStateTests of the [Ethereum Test Suite](https://github.com/ethereum/tests).

. . .

-   Roughly an order of magnitude slower than cpp-ethereum (reference implementation in C++).

    **Test Set** (no. tests)   **KEVM**  **cpp-ethereum**
    ------------------------- --------- -----------------
    VMAll (40683)                 99:41              4:42
    GSNormal (22705)              35:00              1:30

. . .

-   (Non-empty) lines of code comparison:

    KEVM: 2644

    cpp-ethereum: 4588

[^outdated]: These figures are from roughly July 2018.

Reachibility Logic Prover [@stefanescu-ciobaca-mereuta-moore-serbanuta-rosu-2014-rta]
-------------------------------------------------------------------------------------

-   Takes operational semantics as input (no axiomatic semantics).[^inthiscaseK]
-   Generalization of Hoare Logic:
    -   Hoare triple: $\{\textit{Pre}\} \textit{Code} \{\textit{Post}\}$
    -   Reachability claim: $\widehat{\textit{Code}} \land \widehat{\textit{Pre}} \Rightarrow \epsilon \land \widehat{\textit{Post}}$
    -   "Any instance of $\widehat{\textit{Code}}$ which satisfies $\widehat{Pre}$ either does not terminate or reaches an instance of $\epsilon$ (empty program) which satisfies $\widehat{Post}$".
    No need for end state in RL to be $\epsilon$ though.
-   See paper for example claims.

. . .

-   Reachability claims are fed to \K{} prover as normal \K{} rules.
-   Functional correctness directly specifiable as set reachability claims.
-   Correctness bugs often lead to security bugs.

[^inthiscaseK]: In this case, we use \K{} to specify the operational semantics.

Reachability Logic Inference System [@stefanescu-ciobaca-mereuta-moore-serbanuta-rosu-2014-rta]
-----------------------------------------------------------------------------------------------

![RL Inference System](media/images/proof-system.png)

In Practice for KEVM
--------------------

Specifications translated into English read like:

-   "Calling $f(\vect{x})$ of contract $A$ such that $C(x)$ holds results in $u$."
-   "Calling $f(\vect{x})$ of contract $A$ such that $\lnot C(x)$ holds results in `REVERT`."

. . .

Example:

```sol
pragma solidity ^0.4.21;
contract SafeAdd {
    function add(uint x, uint y) public pure returns (uint z) {
        require((z = x + y) >= x);
    }
}
```

-   "Calling $add(x, y)$ of contract $SafeAdd$ such that $x + y < 2^{256}$ holds results in `return (x + y)`."
-   "Calling $add(x, y)$ of contract $SafeAdd$ such that $x + y \ge 2^{256}$ holds results in `REVERT`."

KLab
====

\K{} Specification Example
--------------------------

\K{} specifications are hard to write:

. . .

**TODO**: Mini version of whole \K{} spec for `SafeAdd` here.

KLab to the rescue!
-------------------

-   Simpler input format in terms of "acts".
-   Compiles act to \K{} specification and runs \K{} prover asynchronously.
-   Interactive execution exploration tool for evaluating proof/failure.

. . .

**TODO**: Example act for `SafeAdd` here.

Workshop
--------

-   Install KEVM dependencies (no need for OCaml backend deps).
-   Clone KLab repository, build.
-   Run example proof at `examples/SafeAdd`, try breaking it.
-   Exercises!

KLab Setup
----------

Install and build:

```sh
sudo apt-get install                   \
    make gcc maven openjdk-8-jdk       \
    flex pkg-config libmpfr-dev        \
    autoconf libtool pandoc zlib1g-dev
git clone 'https://github.com/dapphub/klab'
cd klab
make deps
```

. . .

Environment setup (via `source env`):

```sh
export PATH=$PATH:$(pwd)/bin
export KLAB_EVMS_PATH=$(pwd)/evm-semantics
export TMPDIR=/tmp
```

Running `SafeAdd`
-----------------

Start `klab server`:

```sh
source env
klab server
```

. . .

Run `klab` on `SafeAdd`:

```sh
source env
cd examples/SafeAdd
klab build
klab run
```

Your Turn!
----------

-   Clone the tutorial repository.
-   Try out our challenges!

```sh
git clone 'https://github.com/dapphub/fv-tutorial'
```

. . .

Finished and feeling brave??

Try your own contract!
We'll help!
