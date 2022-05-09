Anders
======

```OCaml
type exp =
  | EPre of Z.t | EKan of Z.t                                                          (* cosmos *)
  | EVar of ident | EHole                                                           (* variables *)
  | EPi of exp * (ident * exp) | ELam of exp * (ident * exp) | EApp of exp * exp           (* pi *)
  | ESig of exp * (ident * exp) | EPair of tag * exp * exp                              (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                    (* simga elims/records *)
  | EId of exp | ERef of exp | EJ of exp                                      (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp       (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp * exp * exp * exp                     (* Kan operations *)
  | EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t      (* partial functions *)
  | ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp                (* cubical subtypes *)
  | EGlue of exp | EGlueElem of exp * exp * exp | EUnglue of exp * exp * exp          (* glueing *)
  | EEmpty | EIndEmpty of exp                                                               (* 𝟎 *)
  | EUnit | EStar | EIndUnit of exp                                                         (* 𝟏 *)
  | EBool | EFalse | ETrue | EIndBool of exp                                                (* 𝟐 *)
  | EW of exp * (ident * exp) | ESup of exp * exp | EIndW of exp * exp * exp                (* W *)
  | EIm of exp | EInf of exp | EIndIm of exp * exp | EJoin of exp      (* Infinitesimal Modality *)
```

Anders is a HoTT proof assistant based on [CCHM](https://arxiv.org/pdf/1611.02108.pdf)
in flavour of [Cubical Agda](https://agda.readthedocs.io/en/v2.6.2.1/language/cubical.html)
plus strict equality for 2LTT and ℑ modality for synthetic differential geometry.

Features
--------

* 𝟎, 𝟏, 𝟐, W.
* Pretypes & strict equality.
* Generalized Transport and Homogeneous Composition as primitive Kan operations.
* Cubical subtypes.
* Glue types.
* Coequalizer.
* ℑ modality.
* UTF-8 support including universe levels (i.e. `U₁₂₃`).
* Lean syntax for ΠΣW.
* Poor man’s records as Σ with named accessors to telescope variables.
* 1D syntax with top-level declarations.

Setup
-----

```shell
$ make
$ dune exec anders help
```

Samples
-------

You can find some examples in [`library/`](https://github.com/forked-from-1kasper/anders/tree/master/library).

```Lean
def inv′ (A : U) (a b : A) (p : Path A a b) : Path A b a :=
<i> hcomp A (∂ i) (λ (j : I), [(i = 0) → p @ j, (i = 1) → a]) a

def kan (A : U) (a b c d : A) (p : Path A a c) (q : Path A b d) (r : Path A a b) : Path A c d :=
<i> hcomp A (∂ i) (λ (j : I), [(i = 0) → p @ j, (i = 1) → q @ j]) (r @ i)

def comp (A : I → U) (r : I) (u : Π (i : I), Partial (A i) r) (u₀ : (A 0)[r ↦ u 0]) : A 1 :=
hcomp (A 1) r (λ (i : I), [(r = 1) → transp (<j> A (i ∨ j)) i (u i 1=1)]) (transp (<i> A i) 0 (ouc u₀))

def ghcomp (A : U) (r : I) (u : I → Partial A r) (u₀ : A[r ↦ u 0]) : A :=
hcomp A (∂ r) (λ (j : I), [(r = 1) → u j 1=1, (r = 0) → ouc u₀]) (ouc u₀)
```

```shell
$ anders check library/everything.anders
```

## Related publications

### MLTT

Type Checker is based on classical MLTT-80 with 0, 1, 2 and W-types.

* <a href="https://raw.githubusercontent.com/michaelt/martin-lof/master/pdfs/Bibliopolis-Book-retypeset-1984.pdf">Intuitionistic Type Theory</a> [Martin-Löf]

### CCHM

* <a href="http://www.cse.chalmers.se/~simonhu/papers/cubicaltt.pdf">CTT: a constructive interpretation of the univalence axiom</a> [Cohen, Coquand, Huber, Mörtberg]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalhits.pdf">On Higher Inductive Types in Cubical Type Theory</a> [Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1607.04156.pdf">Canonicity for Cubical Type Theory</a> [Huber]
* <a href="http://www.cse.chalmers.se/~simonhu/papers/can.pdf">Canonicity and homotopy canonicity for cubical type theory</a> [Coquand, Huber, Sattler]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf">Cubical Synthetic Homotopy Theory</a> [Mörtberg, Pujet]
* <a href="https://staff.math.su.se/anders.mortberg/papers/unifying.pdf">Unifying Cubical Models of Univalent Type Theory</a> [Cavallo, Mörtberg, Swan]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf">Cubical Agda: A Dependently Typed PL with Univalence and HITs</a> [Vezzosi, Mörtberg, Abel]
* <a href="https://simhu.github.io/misc/hcomp.pdf">A Cubical Type Theory for Higher Inductive Types</a> [Huber]
* <a href="http://www.cse.chalmers.se/~simonhu/papers/p.pdf">Gluing for type theory</a> [Kaposi, Huber, Sattler]
* <a href="https://doi.org/10.1017/S0960129521000311">Cubical Methods in HoTT/UF</a> [Mörtberg]

### HTS

* <a href="https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf">A simple type system with two identity types</a> [Voevodsky]
* <a href="https://arxiv.org/pdf/1705.03307.pdf">Two-level type theory and applications</a> [Annenkov, Capriotti, Kraus, Sattler]
* <a href="https://types21.liacs.nl/download/syntax-for-two-level-type-theory/">Syntax for two-level type theory</a> [Bonacina, Ahrens]

### Modalities

Infinitesimal Modality was added for direct support of Synthetic Differential Geometry.

* <a href="https://arxiv.org/pdf/1310.7930v1.pdf">Differential cohomology in a cohesive ∞-topos</a> [Schreiber]
* <a href="https://arxiv.org/pdf/1806.05966.pdf">Cartan Geometry in Modal Homotopy Type Theory</a> [Cherubini]
* <a href="https://hott-uf.github.io/2017/abstracts/cohesivett.pdf">Differential Cohesive Type Theory</a> [Gross, Licata, New, Paykin, Riley, Shulman, Cherubini]
* <a href="https://arxiv.org/abs/1509.07584">Brouwer's fixed-point theorem in real-cohesive homotopy type theory</a> [Shulman]

Acknowledgements
----------------

* Univalent People

Authors
-------

* <a href="https://twitter.com/siegment">@siegment</a>
* <a href="https://twitter.com/tonpaguru">@tonpaguru</a>
