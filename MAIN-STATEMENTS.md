# Main theorems

<a id="shared-definitions"></a>

## Setting and notation

Let $m\geq2$, let $d_1,\ldots,d_m\geq1$, and set $d=d_1+\cdots+d_m$.
We work on $\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_m}=\mathbb R^d$.

### Rectangles and dyadic grids

A rectangle is a product $I=I^1\times\cdots\times I^m$ of axis-parallel
cubes, with $I^i$ in $\mathbb R^{d_i}$. Write $\ell(Q)$ for the side
length of a cube $Q$.

Let $\mathcal D^i$ be a dyadic grid of cubes in $\mathbb R^{d_i}$ and set
$\mathcal D=\mathcal D^1\times\cdots\times\mathcal D^m$.
The cubes in each grid are half-open, and those of side length $2^k$
partition the corresponding space for every $k\in\mathbb Z$.
Any two intersecting cubes in the same grid are nested.

### Conventions

We use $\subset$ for inclusion allowing equality.

All functions are real-valued. All measures and integrals are with respect
to Lebesgue measure, and $\|g\|_p$ denotes the $L^p(\mathbb R^d)$ norm.
We write $p'=p/(p-1)$ for $1<p<\infty$.

### Maximal operators and overlap functions

For a family $\mathcal E$ of rectangles and $f\in L^1_{\mathrm{loc}}(\mathbb R^d)$,
define the maximal operator

$$
M_{\mathcal E}f(x)
=\sup_{\substack{I\in\mathcal E\\x\in I}}
  \frac1{|I|}\int_I |f(y)|\,dy.
$$

For $\mathcal G\subset\mathcal D$, define the overlap function and shadow by

$$
h_{\mathcal G}=\sum_{I\in\mathcal G}\mathbf1_I,
\qquad \operatorname{sh}(\mathcal G)=\bigcup_{I\in\mathcal G}I.
$$

The family has finite shadow if $|\operatorname{sh}(\mathcal G)|<\infty$.

It is **incomparable** if no two distinct members contain one another.
For $0<\eta\leq1$, it is **$\eta$-sparse** if there are pairwise disjoint
measurable sets $E_I\subset I$, $I\in\mathcal G$, with $|E_I|\geq\eta|I|$.

## Incomparable maximal estimate

Let $\mathcal G\subset\mathcal D$ be incomparable. Then

$$
\|M_{\mathcal G}f\|_p
\leq C_{m,d}(p')^{m-1}\|f\|_p,
\qquad 1<p\leq2.
$$

The constant depends only on $m$ and $d$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L25) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionMaximal.lean#L10) · [Theorem in the main development](lean/ReyZygmund/Main/Maximal.lean#L70).

<a id="sparse-incomparable-overlap"></a>

## Sparse incomparable overlap estimate

Let $\mathcal G\subset\mathcal D$ be incomparable and $\eta$-sparse,
with finite shadow. Then

$$
\|h_{\mathcal G}\|_q
\leq C_{m,d}\eta^{-1}q^{m-1}
      |\operatorname{sh}(\mathcal G)|^{1/q},
\qquad q\geq2,
$$

and

$$
\int_{\operatorname{sh}(\mathcal G)}
\left[\exp\!\left(c_{m,d}(\eta h_{\mathcal G})^{1/(m-1)}\right)-1\right]dx
\leq C_{m,d}|\operatorname{sh}(\mathcal G)|.
$$

The positive constants depend only on $m$ and $d$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L39) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionOverlap.lean#L8) · [Theorem in the main development](lean/ReyZygmund/Main/Overlap.lean#L100).

## Maximal and overlap estimates under weaker containment

Suppose $\mathcal G\subset\mathcal D$ satisfies

$$
I,J\in\mathcal G,\quad I\subset J
\quad\Longrightarrow\quad I^i=J^i
\text{ for some }i\in\{1,\ldots,m\}.
$$

Then

$$
\|M_{\mathcal G}f\|_p
\leq C_{m,d}(p')^{m-1}\|f\|_p,
\qquad 1<p\leq2.
$$

The constant depends only on $m$ and $d$.
If $\mathcal G$ is also $\eta$-sparse and has finite shadow, the
[moment and exponential estimates above](#sparse-incomparable-overlap-estimate)
hold as well.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L57) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionWeaker.lean#L8) · [Theorem in the main development](lean/ReyZygmund/Main/Overlap.lean#L60).

## Continuous Zygmund endpoint estimate

Let $m\geq3$ and let
$\phi:(0,\infty)^{m-1}\to(0,\infty)$ be coordinatewise nondecreasing.
Let $\mathcal R_\phi$ consist of all rectangles
$R=R^1\times\cdots\times R^m$ with axis-parallel cube factors
$R^i\subset\mathbb R^{d_i}$ and side-length tuple

$$
(s_1,\ldots,s_{m-1},\phi(s_1,\ldots,s_{m-1})),
\qquad s_1,\ldots,s_{m-1}>0.
$$

For every $f\in L^1_{\mathrm{loc}}(\mathbb R^d)$ and every $\lambda>0$,

$$
|\{x:M_{\mathcal R_\phi}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
$$

The constant depends only on $m$ and $d$, not on $\phi$.
No continuity or doubling assumption on $\phi$ is imposed.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L81) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionContinuous.lean#L10) · [Theorem in the main development](lean/ReyZygmund/Continuous/Endpoint.lean#L88).

<a id="endpoint-estimate-for-the-rounded-dyadic-families"></a>

## Rounded dyadic endpoint estimate

Let $m\geq3$ and let
$\phi:(0,\infty)^{m-1}\to(0,\infty)$ be coordinatewise nondecreasing.
For $s>0$, define $\rho(s)=\lceil\log_2s\rceil+2$, and put

$$
\Gamma_\phi=
\{(\rho(s_1),\ldots,\rho(s_{m-1}),\rho(\phi(s))):
                       s\in(0,\infty)^{m-1}\}.
$$

In $\Gamma_\phi$, the first $m-1$ rounded scales need not determine the last.

For $\tau=(\tau_1,\ldots,\tau_m)$, with
$\tau_i\in\{0,1/3,2/3\}^{d_i}$, use the shifted grids

$$
\mathcal D^{i,\tau_i}
=\{2^k([0,1)^{d_i}+z+(-1)^k\tau_i):
                              k\in\mathbb Z,\ z\in\mathbb Z^{d_i}\},
$$

and set

$$
\mathcal D_\tau=\prod_{i=1}^m\mathcal D^{i,\tau_i},
\qquad
\mathcal E_\phi^\tau
=\{I\in\mathcal D_\tau:
    (\log_2\ell(I^1),\ldots,\log_2\ell(I^m))\in\Gamma_\phi\}.
$$

For every $f\in L^1_{\mathrm{loc}}(\mathbb R^d)$ and every $\lambda>0$,

$$
|\{x:M_{\mathcal E_\phi^\tau}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
$$

The constant depends only on $m$ and $d$, not on $\phi$ or $\tau$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L94) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionRounded.lean#L10) · [Theorem in the main development](lean/ReyZygmund/Main/Endpoints.lean#L19).

<a id="sparse-overlap-with-a-monotone-zygmund-scale-relation"></a>

## Sparse Φ-Zygmund overlap estimate

Let $m\geq3$ and let $\Phi:\mathbb Z^{m-1}\to\mathbb Z$ be
coordinatewise nondecreasing. Let $\mathcal Z_\Phi\subset\mathcal D$
be the family of rectangles with side-length tuple

$$
\bigl(2^{k_1},\ldots,2^{k_{m-1}},
                 2^{\Phi(k_1,\ldots,k_{m-1})}\bigr),
\qquad (k_1,\ldots,k_{m-1})\in\mathbb Z^{m-1}.
$$

If $\mathcal G\subset\mathcal Z_\Phi$ is $\eta$-sparse with finite
shadow, where $0<\eta\leq1$, then

$$
\int_{\operatorname{sh}(\mathcal G)}
\left[\exp\!\left(c h_{\mathcal G}^{1/(m-1)}\right)-1\right]dx
\leq C|\operatorname{sh}(\mathcal G)|,
$$

where $c,C>0$ depend only on $m$, $d$ and $\eta$, not on $\Phi$
or the dyadic grids.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L108) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionPhiSparse.lean#L8) · [Theorem in the main development](lean/ReyZygmund/Main/PhiSparse.lean#L51).

<a id="sharpness-for-sparse-incomparable-zygmund-families"></a>

## Sharpness for the classical dyadic Zygmund family

Let $m\geq3$, $0<\eta<1$, and set

$$
\Phi(k_1,\ldots,k_{m-1})=k_1+\cdots+k_{m-1}.
$$

There are finite incomparable $\eta$-sparse families
$\mathcal G_N\subset\mathcal Z_\Phi$, $N\geq2$, with
$|\operatorname{sh}(\mathcal G_N)|=1$, such that

$$
\lim_{N\to\infty}
\int_{\operatorname{sh}(\mathcal G_N)}
\left[\exp\!\left(c h_{\mathcal G_N}^{\beta}\right)-1\right]dx
=\infty
\quad\text{for every }c>0,\quad\beta>\frac1{m-1}.
$$

Thus adding incomparability to sparseness and the $\Phi$-Zygmund scale
restriction need not improve the exponential power, even for the classical
relation above.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/Statements.lean#L123) · [Definitions](lean/ReyZygmund/MathlibOnly/Definitions.lean) · [Proof](lean/ReyZygmund/MathlibOnly/SolutionSharpness.lean#L8) · [Theorem in the main development](lean/ReyZygmund/Main/Sharpness.lean#L22).

## Notes on the formalization

The links under each result give its independent Lean statement and
definitions, a proof of that statement, and the theorem used from the main
development. The [consistency guide](CONSISTENCY.md) explains the relation
between the mathematical definitions and their formal representations;
the [verification guide](VERIFYING.md) describes the checks performed and
how to repeat them.

The formalization also gives the incomparable maximal estimate for
$2<p<\infty$.

The shifted grids above use $[0,1)$, as in the paper; Lean uses $(0,1]$.
The corresponding rounded-family maximal functions agree almost everywhere.
