# The Zygmund and Rey conjectures in Lean

## What this is

A Lean 4 formalization accompanying Henri Martikainen's [*The Zygmund conjecture and Rey's exponential integrability conjecture*](https://arxiv.org/abs/2609.23895), built on Mathlib.

The formalization covers the two conjectures and their underlying maximal estimate, together with extensions to more general rectangle families and a sparse-family sharpness result. The paper is the primary mathematical exposition.

[Main theorems](MAIN-STATEMENTS.md) · [Definitions and consistency](CONSISTENCY.md) · [Checking the formalization](VERIFYING.md)

## Main results

The paper proves the Zygmund conjecture in all parameters, in the following continuous form.

Let $m\geq3$, let $d_1,\ldots,d_m\geq1$, and set $d=d_1+\cdots+d_m$.
We work on $\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}=\mathbb R^d$
with Lebesgue measure. Let
$\phi:(0,\infty)^{m-1}\to(0,\infty)$ be coordinatewise nondecreasing.
Let $\mathcal R_\phi$ consist of all rectangles
$R=R^1\times\cdots\times R^m$ with axis-parallel cube factors
$R^i\subset\mathbb R^{d_i}$ and side-length tuple

$$
(s_1,\ldots,s_{m-1},\phi(s_1,\ldots,s_{m-1})),
\qquad s_1,\ldots,s_{m-1}>0.
$$

For a family $\mathcal E$ of rectangles, define

$$
M_{\mathcal E}f(x)
=\sup_{\substack{I\in\mathcal E\\x\in I}}
  \frac1{|I|}\int_I |f(y)|\,dy.
$$

**Theorem (Zygmund conjecture).** For every
$f\in L^1_{\mathrm{loc}}(\mathbb R^d)$ and every $\lambda>0$,

$$
|\{x:M_{\mathcal R_\phi}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
$$

The constant depends only on $m$ and $d$, not on $\phi$.
No continuity or doubling assumption on $\phi$ is imposed.
This weak $L(\log L)^{m-2}$ estimate saves one logarithm compared with
the full $m$-parameter strong maximal function, whose logarithmic power is $m-1$.

The central analytic estimate is $\|M_{\mathcal G}f\|_p\leq C_{m,d}(p')^{m-1}\|f\|_p$, $1<p\leq2$, for incomparable $m$-parameter dyadic rectangle families, $m\geq2$. Here $p'=p/(p-1)$. It saves one factor of $p'$ compared with the unrestricted product maximal operator. Duality gives Rey's exponential integrability estimate for sparse incomparable families, with power $1/(m-1)$.

The continuous Zygmund theorem also uses an extension allowing certain containments: the slices arising after dyadic rounding need not be incomparable.

The three central results are:

| Result | Mathematical role | Lean source |
| --- | --- | --- |
| [Continuous Zygmund endpoint estimate](MAIN-STATEMENTS.md#continuous-zygmund-endpoint-estimate) | Zygmund's conjecture in its continuous form | [Continuous/Endpoint.lean](lean/ReyZygmund/Continuous/Endpoint.lean) |
| [Sparse incomparable overlap estimate](MAIN-STATEMENTS.md#sparse-incomparable-overlap-estimate) | Rey's exponential integrability conjecture | [Main/Overlap.lean](lean/ReyZygmund/Main/Overlap.lean) |
| [Incomparable maximal estimate](MAIN-STATEMENTS.md#incomparable-maximal-estimate) | Central analytic estimate used to prove both conjectures | [Main/Maximal.lean](lean/ReyZygmund/Main/Maximal.lean) |

We also formalize the following extensions, transfer steps and sharpness result:

| Result | Mathematical role | Lean source |
| --- | --- | --- |
| [Maximal and overlap estimates under weaker containment](MAIN-STATEMENTS.md#maximal-and-overlap-estimates-under-weaker-containment) | Applies to the slices used in the continuous reduction | [Main/Overlap.lean](lean/ReyZygmund/Main/Overlap.lean) |
| [Rounded dyadic endpoint estimate](MAIN-STATEMENTS.md#rounded-dyadic-endpoint-estimate) | Dyadic endpoint used to obtain the continuous theorem | [Main/Endpoints.lean](lean/ReyZygmund/Main/Endpoints.lean) |
| [Sparse Φ-Zygmund overlap estimate](MAIN-STATEMENTS.md#sparse-φ-zygmund-overlap-estimate) | Overlap estimate without incomparability | [Main/PhiSparse.lean](lean/ReyZygmund/Main/PhiSparse.lean) |
| [Sharpness for the classical dyadic Zygmund family](MAIN-STATEMENTS.md#sharpness-for-the-classical-dyadic-zygmund-family) | Sharpness even for incomparable families | [Main/Sharpness.lean](lean/ReyZygmund/Main/Sharpness.lean) |

## Scope and faithfulness

[Main theorems](MAIN-STATEMENTS.md) gives the seven self-contained mathematical statements, including the hypotheses and constants for each setting. The links beneath each result lead to its independent Lean statement, definitions and proofs. No software installation is needed to inspect them.

Separate mathematical reviews checked the correspondence between these formal statements and definitions and the paper. The [mathematical scope notes](VERIFYING.md#mathematical-scope) describe the coverage of the formalization relative to the paper.

## Consistency checks of the definitions

The [consistency guide](CONSISTENCY.md) explains how the mathematical objects are represented in Lean and how the independently written definitions are related to those used in the proofs. It links to the relevant definitions and identifications, distinguishing identities proved in Lean from comparisons checked mathematically.

## Verified against a Mathlib-only statement

Each of the seven results has an [independent Lean statement](lean/ReyZygmund/MathlibOnly/Statements.lean) using [definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) that depend only on Mathlib. Neither file imports the proof development. Identities proved in Lean relate these definitions to those used in the proofs, so the main theorems give the independently stated results.

On 26 September 2026, all seven results passed Comparator's comparison of the formal statements and their definitions. Their exported proofs, including the declarations on which they depend, were accepted by both Lean's default kernel and Nanoda.

The theorem proofs contain no omitted steps (`sorry`) and use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. See the [verification summary](VERIFYING.md#what-has-been-checked) for the recorded checks and their scope, and the [reproduction instructions](VERIFYING.md#4-comparator-with-nanoda-on-linux) to repeat the Comparator and two-kernel checks.

## Building

The development uses Lean 4.34.0 and a pinned Mathlib version. See the [verification guide](VERIFYING.md) for dependency setup, build options and checking commands.

For ordinary compilation after that setup:

```sh
cd lean
lake build
```

## Repository layout

| Location | Contents |
| --- | --- |
| [MAIN-STATEMENTS.md](MAIN-STATEMENTS.md) | The seven mathematical statements and source links |
| `lean/ReyZygmund/` | The proof development |
| [MathlibOnly/README.md](lean/ReyZygmund/MathlibOnly/README.md) | Independently written statements and their relation to the proofs |
| `lean/Verification/` | Reviewed formal statements and programs for checking them |
| `verification/comparator/` | The seven Mathlib-only comparison adapters and configurations |
| [CONSISTENCY.md](CONSISTENCY.md) | Mathematical definitions and the identities relating their descriptions |
| [VERIFYING.md](VERIFYING.md) | Reproduction instructions and checking scope |
| `tools/` | Checking and site-generation programs |
| `docs/` | Static website; see [SITE.md](SITE.md) |

## How this was built

The formalization was developed with AI assistance, with separate reviews of its scope and faithfulness to the intended mathematics. The main Lean codebase was produced using GPT-6-Astra at Max reasoning effort, in a workflow with specialized subagents. Claude Fable 5.1 provided additional independent and blind review of the mathematical specifications.

## Authors and citation

Henri Martikainen, Washington University in St. Louis.

Please use the metadata in [CITATION.cff](CITATION.cff) when citing this development, and the linked paper for the mathematical results.

## Acknowledgements

This material is based upon work supported by the National Science Foundation under Grant No. 2247234. The work was also supported by the Simons Foundation through MP-TSM-00002361 (travel support for mathematicians).

Any opinions, findings, and conclusions or recommendations expressed in this material are those of the author(s) and do not necessarily reflect the views of the National Science Foundation.

## License

The source code, checking scripts and accompanying documentation are available under [Apache-2.0](LICENSE). See [third-party notices](lean/THIRD_PARTY.md) for the Mathlib adaptation and the Carleson proof-pattern acknowledgment. The linked paper is not distributed under this software license.
