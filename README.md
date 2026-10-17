# The Zygmund and Rey conjectures in Lean

## What this is

A Lean 4 formalization accompanying Henri Martikainen's [*The Zygmund conjecture and Rey's exponential integrability conjecture*](https://arxiv.org/abs/2609.23895), built on Mathlib.

The formalization covers the two conjectures and their underlying maximal estimate, together with related dyadic overlap and square-function estimates, projection identities and a sparse-family sharpness result. The paper is the primary mathematical exposition.

[Main theorems](MAIN-STATEMENTS.md) · [Supporting results](SUPPORTING-STATEMENTS.md) · [Independent specification](lean/ReyZygmund/MathlibOnly/README.md) · [Checking the formalization](VERIFYING.md)

## Main results

The paper proves the Zygmund conjecture in all parameters, in the following continuous form.

Let $`m\geq3`$, let $`d_1,\ldots,d_m\geq1`$, and set $`d=d_1+\cdots+d_m`$.
We work on $`\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}=\mathbb R^d`$
with Lebesgue measure. Let
$`\phi:(0,\infty)^{m-1}\to(0,\infty)`$ be coordinatewise nondecreasing.
Let $`\mathcal R_\phi`$ consist of all rectangles
$`R=R^1\times\cdots\times R^m`$ with axis-parallel cube factors
$`R^i\subset\mathbb R^{d_i}`$ and side-length tuple

```math
(s_1,\ldots,s_{m-1},\phi(s_1,\ldots,s_{m-1})),
\qquad s_1,\ldots,s_{m-1}>0.
```

For a family $`\mathcal E`$ of rectangles, define

```math
M_{\mathcal E}f(x)
=\sup_{\substack{I\in\mathcal E\\x\in I}}
  \frac1{|I|}\int_I |f(y)|\,dy.
```

**Theorem (Zygmund conjecture).** For every
$`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$ and every $`\lambda>0`$,

```math
|\{x:M_{\mathcal R_\phi}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
```

The constant depends only on $`m`$ and $`d`$, not on $`\phi`$.
No continuity or doubling assumption on $`\phi`$ is imposed.
This weak $`L(\log L)^{m-2}`$ estimate saves one logarithm compared with
the full $`m`$-parameter strong maximal function, whose logarithmic power is $`m-1`$.

The central analytic estimate is $`\|M_{\mathcal G}f\|_p\leq C_{m,d}(p')^{m-1}\|f\|_p`$, $`1<p\leq2`$, for weakly incomparable $`m`$-parameter dyadic rectangle families, $`m\geq2`$. Here $`p'=p/(p-1)`$. Weak incomparability means that no two rectangles are strictly nested in every coordinate factor. The estimate saves one factor of $`p'`$ compared with the unrestricted product maximal operator. Duality gives exponential integrability of the overlap function $`h_{\mathcal G}=\sum_{I\in\mathcal G}\mathbf 1_I`$, with power $`1/(m-1)`$, for sparse weakly incomparable families, and in particular proves Rey's conjecture.

The three central results are:

| Result | Mathematical role | Formal statement and proof |
| --- | --- | --- |
| [Continuous Zygmund endpoint estimate](MAIN-STATEMENTS.md#continuous-zygmund-endpoint-estimate) | Zygmund's conjecture in its continuous form | [Statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L66) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L59) |
| [Rey's conjecture for weakly incomparable families](MAIN-STATEMENTS.md#reys-conjecture-for-weakly-incomparable-families) | Rey's exponential integrability conjecture, with weak incomparability | [Statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L48) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L43) |
| [Weakly incomparable maximal estimate](MAIN-STATEMENTS.md#weakly-incomparable-maximal-estimate) | Central analytic estimate used to prove both conjectures | [Statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L34) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L31) |

The proof library contains the supporting results needed to establish these three theorems. Nineteen selected supporting and additional results are also included in the independent specification and collected in [Supporting results](SUPPORTING-STATEMENTS.md). Their statements and definitions can be inspected without reading the proof library, and their proofs receive the same Comparator, Lean, Nanoda and con-ron checks as the three main results.

## Independent specification, verification and correspondence with the paper

[Main theorems](MAIN-STATEMENTS.md) and [Supporting results](SUPPORTING-STATEMENTS.md) present the results in mathematical prose. Their precise formal meaning is given by an [independent specification rebuilt from Mathlib primitives](lean/ReyZygmund/MathlibOnly/README.md), without importing the proof library. To inspect a result, read its statement and the definitions listed for it. No software installation is needed to inspect these statements and definitions.

Mathematical review checked that the statements and their definitions express the intended results of the paper. This addresses the central question: does the Lean specification faithfully represent the mathematics we intend to prove? The formal checks then verify that the supplied proofs establish those statements.

The mathematical arguments are developed in the [proof library](lean/ReyZygmund/), using the specification’s shared definitions and further properties and constructions.

The public proofs, in [Solutions.lean](lean/ReyZygmund/MathlibOnly/Solutions.lean) and the [individual proof modules](lean/ReyZygmund/MathlibOnly/Proof/), derive the independently stated results from the library’s theorems. Where the proofs use other representations, identities proved in Lean connect them to the specification. The [definition guide](lean/ReyZygmund/MathlibOnly/DEFINITIONS.md) explains the mathematical objects and their Lean representations, with links to the relevant identifications.

Comparator checks that the Lean statement of each supplied theorem is identical to the separately compiled statement from our independent specification. It also checks that the definitions on which those statements depend agree. It does not assess correspondence with the paper; that is the role of mathematical review. All twenty-two comparisons passed. Lean’s default kernel and two additional proof checkers, Nanoda and con-ron, accepted the exported proofs and their exported dependencies. The checks also exclude omitted steps (`sorry`) and restrict axioms to `propext`, `Classical.choice` and `Quot.sound`. The [verification guide](VERIFYING.md#what-the-programs-do) explains these tools and records the checking scope and reproduction instructions.

A checked proof of a faithful specification establishes the intended mathematical results; whether it follows the paper’s argument is a separate question. This formalization was developed to follow the paper’s proof strategies closely. Separate mathematical reviews examined that correspondence and found agreement in the main lines of argument.

## Building

The development uses Lean 4.35.0-rc4 and a pinned Mathlib version. See the [verification guide](VERIFYING.md) for dependency setup, build options and checking commands.

For ordinary compilation after that setup:

```sh
cd lean
lake build
```

## Repository layout

| Location | Contents |
| --- | --- |
| [MAIN-STATEMENTS.md](MAIN-STATEMENTS.md) | The three main statements and source links |
| [SUPPORTING-STATEMENTS.md](SUPPORTING-STATEMENTS.md) | The nineteen supporting and additional statements and source links |
| `lean/ReyZygmund/` | The proof development |
| [MathlibOnly/README.md](lean/ReyZygmund/MathlibOnly/README.md) | Guide to the independent statements, their definitions and proofs |
| `lean/Verification/` | Supporting declaration checks and verification programs |
| `verification/comparator/` | Statement-comparison configurations and their adapters |
| [VERIFYING.md](VERIFYING.md) | Reproduction instructions and checking scope |
| `tools/` | Checking and site-generation programs |
| `docs/` | Static website; see [SITE.md](SITE.md) |

## How this was built

The formalization was developed with AI assistance, with separate reviews of its scope and faithfulness to the intended mathematics. The main Lean codebase was produced using GPT-6-Astra in a workflow with specialized subagents. Claude Fable 5.1 provided additional independent and blind reviews of the mathematical specifications and of the correspondence between the formal proofs and the paper’s main arguments.

## Authors and citation

Henri Martikainen, Washington University in St. Louis.

Please use the metadata in [CITATION.cff](CITATION.cff) when citing this development, and the linked paper for the mathematical results.

## Acknowledgements

This material is based upon work supported by the National Science Foundation under Grant No. 2247234. The work was also supported by the Simons Foundation through MP-TSM-00002361 (travel support for mathematicians).

Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

## License

The source code, checking scripts and accompanying documentation are available under [Apache-2.0](LICENSE). See [third-party notices](lean/THIRD_PARTY.md) for the Mathlib adaptation and the Carleson proof-pattern acknowledgment. The linked paper is not distributed under this software license.
