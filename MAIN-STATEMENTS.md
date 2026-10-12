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

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L33) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L19) · [Theorem in the main development](lean/ReyZygmund/Maximal/WeakerGlobal.lean#L140).

<a id="sparse-incomparable-overlap"></a>

<a id="sparse-incomparable-overlap-estimate"></a>

## Sparse weakly incomparable overlap estimate

The maximal estimate gives the following overlap bounds by duality.
Rey states his conjecture for incomparable, $`1/2`$-sparse families.
The estimate below allows weak incomparability and any sparsity
parameter $`\eta\in(0,1]`$.

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

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L47) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L31) · [Exponential estimate in the main development](lean/ReyZygmund/Overlap/Exponential.lean#L78).

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

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L64) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L49) · [Theorem in the main development](lean/ReyZygmund/Continuous/Endpoint.lean#L88).

<a id="endpoint-estimate-for-the-rounded-dyadic-families"></a>

## Rounded dyadic endpoint estimate

Let $`m\geq3`$ and let
$`\phi:(0,\infty)^{m-1}\to(0,\infty)`$ be coordinatewise nondecreasing.
For $`s>0`$, define $`\rho(s)=\lceil\log_2s\rceil+2`$, and put

```math
\Gamma_\phi=
\{(\rho(s_1),\ldots,\rho(s_{m-1}),\rho(\phi(s))):
                       s\in(0,\infty)^{m-1}\}.
```

In $`\Gamma_\phi`$, the first $`m-1`$ rounded scales need not determine the last.

For $`\tau=(\tau_1,\ldots,\tau_m)`$, with
$`\tau_i\in\{0,1/3,2/3\}^{d_i}`$, use the shifted grids

```math
\mathcal D^{i,\tau_i}
=\{2^k([0,1)^{d_i}+z+(-1)^k\tau_i):
                              k\in\mathbb Z,\ z\in\mathbb Z^{d_i}\},
```

and set

```math
\mathcal D_\tau=\prod_{i=1}^m\mathcal D^{i,\tau_i},
\qquad
\mathcal E_\phi^\tau
=\{I\in\mathcal D_\tau:
    (\log_2\ell(I^1),\ldots,\log_2\ell(I^m))\in\Gamma_\phi\}.
```

For every $`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$ and every $`\lambda>0`$,

```math
|\{x:M_{\mathcal E_\phi^\tau}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
```

The constant depends only on $`m`$ and $`d`$, not on $`\phi`$ or $`\tau`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L78) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L59) · [Theorem in the main development](lean/ReyZygmund/Main/Endpoints.lean#L19).

<a id="sparse-overlap-with-a-monotone-zygmund-scale-relation"></a>

## Sparse Φ-Zygmund overlap estimate

Let $`m\geq3`$ and let $`\Phi:\mathbb Z^{m-1}\to\mathbb Z`$ be
coordinatewise nondecreasing. Let $`\mathcal Z_\Phi\subset\mathcal D`$
be the family of rectangles with side-length tuple

```math
\bigl(2^{k_1},\ldots,2^{k_{m-1}},
                 2^{\Phi(k_1,\ldots,k_{m-1})}\bigr),
\qquad (k_1,\ldots,k_{m-1})\in\mathbb Z^{m-1}.
```

If $`\mathcal G\subset\mathcal Z_\Phi`$ is $`\eta`$-sparse with finite
shadow, where $`0<\eta\leq1`$, then

```math
\int_{\mathrm{sh}(\mathcal G)}
\exp\!\left(c h_{\mathcal G}^{1/(m-1)}\right)dx
\leq C|\mathrm{sh}(\mathcal G)|,
```

where $`c,C>0`$ depend only on $`m`$, $`d`$ and $`\eta`$, not on $`\Phi`$
or the dyadic grids.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L92) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L69) · [Theorem in the main development](lean/ReyZygmund/Main/PhiSparse.lean#L51).

<a id="sharpness-for-sparse-incomparable-zygmund-families"></a>

## Sharpness for the classical dyadic Zygmund family

The formalization proves the following sharpness result.

Let $`m\geq3`$, $`0<\eta<1`$, and set

```math
\Phi(k_1,\ldots,k_{m-1})=k_1+\cdots+k_{m-1}.
```

For every choice of the dyadic grids, there are finite incomparable
$`\eta`$-sparse families
$`\mathcal G_N\subset\mathcal Z_\Phi`$, $`N\geq2`$, with
$`|\mathrm{sh}(\mathcal G_N)|=1`$, such that

```math
\lim_{N\to\infty}
\int_{\mathrm{sh}(\mathcal G_N)}
\exp\!\left(c h_{\mathcal G_N}^{\beta}\right)dx
=\infty
\quad\text{for every }c>0,\quad\beta>\frac1{m-1}.
```

The same sequence works for every such $`c`$ and $`\beta`$.

Thus adding incomparability to sparseness and the $`\Phi`$-Zygmund scale
restriction need not improve the exponential power, even for the classical
relation above.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L109) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L88) · [Theorem in the main development](lean/ReyZygmund/Main/Sharpness.lean#L22).

## Notes on the formalization

The links under each result give its independent Lean statement and
definitions, a proof of that statement, and the theorem used from the main
development. The [consistency guide](CONSISTENCY.md) explains the relation
between the mathematical definitions and their formal representations;
the [verification guide](VERIFYING.md) describes the checks performed and
how to repeat them.

The formalization also gives the weakly incomparable maximal estimate for
$`2<p<\infty`$.

The shifted grids above use $`[0,1)`$, as in the paper; the underlying proof uses $`(0,1]`$.
The corresponding rounded-family maximal functions agree almost everywhere.
