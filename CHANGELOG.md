Changelog
=========

?? AUG 2022 **Version 1.8.0:**

* Abandoned Menhir in favour of new extensible parser.
* Abandoned useless “module … where” syntax.
* Deprecated useless (and inconsistent) `irrelevance` option.
* Rename `pre-eval` option to `normalize`.
* Several major optimisations.
* Built-in natural numbers ℕ.
* `typeof` & `domainof`.

27 MAY 2022 **Version 1.4.1:**

* Fix of major bug leading to inconstistency.
* `section` and `variables` (for example look in [experiments/test.anders](https://github.com/forked-from-1kasper/anders/blob/master/experiments/test.anders)).
* Dropped support for extracting into cubicaltt.
* Reorganized and cleaned up library.
* Coequalizer.

6 APR 2022 **Version 1.4.0 Microkernel Pipeline:**

* Repository in https://github.com/forked-from-1kasper/anders.
* Microkernel Architecture: kernel separated from frontend (including REPL) with open binary protocols.
* Universe polymorphism (like in [Agda](https://agda.readthedocs.io/en/latest/language/universe-levels.html)).
* Overhaul of DNF solver for a lot better performance (so `constcubes.anders` finally works).
* Bugfixes for Glue (including https://github.com/agda/agda/issues/5755).
* Abandoned syntax highlighting for MC.

27 JAN 2022 **Version 1.1.1 Univalence:**

* `Glue`, `glue` and `unglue` primitives.
* 𝟎, 𝟏, 𝟐, and W-types.
* Infinitesimal Shape Modality ℑ.
* `ZArith` for universe levels to avoid inconstistency (see https://github.com/agda/agda/issues/5706).
* Eliminate a lot of “Variable … was not found” bugs.

11 DEC 2021 **Version 0.12.1:**

*Technical release.*

11 DEC 2021 **Version 0.12.0:**

* Some of Huber’s rules (see https://simhu.github.io/misc/hcomp.pdf).
* Support for `PartialP` primitive.
* Improved reduction rules for hypercubes.
* `infer` is now able to handle cubical systems.
* Rewritten DNF solver.
* Accessors for Σ’s.
* Some optimisations.

15 JUL 2021 **Version 0.7.2 Kan Operations:**

* Cubical Subtypes (`Sub`, `inc`, `ouc`).
* Homogeneous Kan composition (`hcomp`).
* Eliminate neutral elements (they were derived from Mini-TT).
* Initial Base Library (OPAM share folder).
* New options: `silent` and `indices`.

6 JUL 2021 **Version 0.7.1 Binary Distribution:**

* `infer` is now able to handle lambdas.
* Partials, Cubical Systems (Partial, [φ ↦ u]).
* Strict Equality (`Id`, `ref`, `idJ`).
* Minor optimizations.
* OPAM package.
* ISC license.

5 JUL 2021 **Version 0.7 MLTT Internalization:**

* Universes hierarchy Uₙ.
* `PathP`, path lambdas (`<i> f`), path application `@`.
* CHM interval and de Morgan algebra over it (`∧`, `∨` and `-`).
* Pretypes hierarchy Vₙ.
* Generalized Transport (`transp`).
* `infer` allowing to write definition without type ascription.
* `girard` option.
* (Wide) UTF-8 support.
* Debug traces.
* REPL.

14 APR 2020 **Development starts here:**
* Type checker based on my (unpublished) port Mini-TT to F#.
* Parser & Lexer (Menhir + ocamllex).
* MLTT ΠΣ primitives.