# Main theorems

<a id="shared-definitions"></a>

## Setting and notation

Let $`m\geq2`$, let $`d_1,\ldots,d_m\geq1`$, and set $`d=d_1+\cdots+d_m`$.
We work on $`\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}=\mathbb R^d`$.

### Rectangles and dyadic grids

A rectangle is a product $`I=I^1\times\cdots\times I^m`$ of axis-parallel
cubes, with $`I^i`$ in $`\mathbb R^{d_i}`$. Write $`\ell(Q)`$ for the side
length of a cube $`Q`$.

Let $`\mathcal D^i`$ be a dyadic grid of cubes in $`\mathbb R^{d_i}`$ and set
$`\mathcal D=\mathcal D^1\times\cdots\times\mathcal D^m`$.
The cubes in each grid are half-open, and those of side length $`2^k`$
partition the corresponding space for every $`k\in\mathbb Z`$.
Any two intersecting cubes in the same grid are nested.

### Conventions

We use $`\subset`$ for inclusion allowing equality.

Input functions are real-valued; maximal and overlap functions may take the
value $`+\infty`$. All measures and integrals are with respect
to Lebesgue measure, and $`\|g\|_p`$ denotes the $`L^p(\mathbb R^d)`$ norm.
We write $`p'=p/(p-1)`$ for $`1<p<\infty`$.

### Maximal operators and overlap functions

For a family $`\mathcal E`$ of rectangles and $`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$,
define the maximal operator

```math
M_{\mathcal E}f(x)
=\sup_{\substack{I\in\mathcal E\\x\in I}}
  \frac1{|I|}\int_I |f(y)|\,dy.
```

For $`\mathcal G\subset\mathcal D`$, define the overlap function and shadow by

```math
h_{\mathcal G}=\sum_{I\in\mathcal G}\mathbf1_I,
\qquad \mathrm{sh}(\mathcal G)=\bigcup_{I\in\mathcal G}I.
```

The family has finite shadow if $`|\mathrm{sh}(\mathcal G)|<\infty`$.

It is **incomparable** if no two distinct members contain one another.
It is **weakly incomparable** if there are no $`I,J\in\mathcal G`$ with
$`I^i\subsetneq J^i`$ for every $`i=1,\ldots,m`$.
Every incomparable family is weakly incomparable; weak incomparability
allows containment when at least one coordinate factor is unchanged.

For $`0<\eta\leq1`$, it is **$`\eta`$-sparse** if there are pairwise disjoint
measurable sets $`E_I\subset I`$, $`I\in\mathcal G`$, with $`|E_I|\geq\eta|I|`$.

<a id="incomparable-maximal-estimate"></a>

<a id="maximal-and-overlap-estimates-under-weaker-containment"></a>

## Weakly incomparable maximal estimate

Let $`\mathcal G\subset\mathcal D`$ be weakly incomparable. Then

```math
\|M_{\mathcal G}f\|_p
\leq C_{m,d}(p')^{m-1}\|f\|_p,
\qquad 1\lt p\leq2.
```

The constant depends only on $`m`$ and $`d`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L34) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#weakly-incomparable-maximal-estimate) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L31) · [Theorem in the main development](lean/ReyZygmund/Maximal/WeakerGlobal.lean#L139).

<a id="sparse-incomparable-overlap"></a>

<a id="sparse-incomparable-overlap-estimate"></a>

<a id="sparse-weakly-incomparable-overlap-estimate"></a>

## Rey's conjecture for weakly incomparable families

The maximal estimate gives the following overlap bounds by duality.
Rey states his conjecture for incomparable families.
The estimate below allows weak incomparability.

Let $`\mathcal G\subset\mathcal D`$ be weakly incomparable and $`\eta`$-sparse,
with finite shadow. Then

```math
\|h_{\mathcal G}\|_q
\leq C_{m,d}\eta^{-1}q^{m-1}
      |\mathrm{sh}(\mathcal G)|^{1/q},
\qquad q\geq2,
```

and

```math
\int_{\mathrm{sh}(\mathcal G)}
\exp\!\left(c_{m,d}(\eta h_{\mathcal G})^{1/(m-1)}\right)dx
\leq C_{m,d}|\mathrm{sh}(\mathcal G)|.
```

The positive constants depend only on $`m`$ and $`d`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L48) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#reys-conjecture-for-weakly-incomparable-families) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L43) · [Exponential estimate in the main development](lean/ReyZygmund/Overlap/Exponential.lean#L79).

## Continuous Zygmund endpoint estimate

This is the monotone side-length formulation of Zygmund's conjecture.

Let $`m\geq3`$ and let
$`\phi:(0,\infty)^{m-1}\to(0,\infty)`$ be coordinatewise nondecreasing.
Let $`\mathcal R_\phi`$ consist of all rectangles
$`R=R^1\times\cdots\times R^m`$ with axis-parallel cube factors
$`R^i\subset\mathbb R^{d_i}`$ and side-length tuple

```math
(s_1,\ldots,s_{m-1},\phi(s_1,\ldots,s_{m-1})),
\qquad s_1,\ldots,s_{m-1}>0.
```

For every $`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$ and every $`\lambda>0`$,

```math
|\{x:M_{\mathcal R_\phi}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
```

The constant depends only on $`m`$ and $`d`$, not on $`\phi`$.
No continuity or doubling assumption on $`\phi`$ is imposed.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L66) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#zygmunds-conjecture) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L59) · [Theorem in the main development](lean/ReyZygmund/Continuous/Endpoint.lean#L90).

The [supporting and additional results](SUPPORTING-STATEMENTS.md) include the
rounded endpoint, sparse Φ-Zygmund overlap, sharpness, square-function
estimates and projection identities.

## Notes on the formalization

The links under each result give its independent Lean statement and
definitions, a proof of that statement, and the theorem used from the main
development. The [definition guide](lean/ReyZygmund/MathlibOnly/DEFINITIONS.md)
explains the mathematical objects and their Lean representations;
the [verification guide](VERIFYING.md) describes the checking procedure and
how to run it.

The examples cited in the paper to establish sharpness of the incomparable
maximal power are not formalized.
