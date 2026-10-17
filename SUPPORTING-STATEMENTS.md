# Supporting and additional results

These results complement the three [main theorems](MAIN-STATEMENTS.md).
Each result links to its independent Lean statement, the definitions it uses
and a proof.

We use the [setting and notation](MAIN-STATEMENTS.md#setting-and-notation)
of the main theorems. The weighted estimates and projection identities use the finite
setting defined below.

## Square-function estimates

### Averages and martingale differences

For a cube $`Q`$, let $`\mathrm{ch}(Q)`$ be its dyadic children,
obtained by halving each side. Define

```math
\langle u\rangle_Q=\frac1{|Q|}\int_Q u,
\qquad E_Q u=\mathbf1_Q\langle u\rangle_Q,
\qquad \Delta_Q u=\sum_{J\in\mathrm{ch}(Q)}E_Ju-E_Qu.
```

On the product space, the operators act in the indicated coordinate.
For $`I=I^1\times\cdots\times I^m`$, put
$`E_I=\prod_iE_{I^i}`$ and $`\Delta_I=\prod_i\Delta_{I^i}`$,
where products of operators mean composition.

### Maximal–square-function estimate

Let $`m\geq1`$. Define

```math
\mathcal M_{\mathcal D}g(x)
 =\sup_{\substack{I\in\mathcal D\\x\in I}}|\langle g\rangle_I|,
\qquad
S_{\mathcal D}g(x)
 =\left(\sum_{I\in\mathcal D}|\Delta_Ig(x)|^2\right)^{1/2}.
```

Here the absolute value in $`\mathcal M_{\mathcal D}`$ is taken after the
average. Suppose that $`g=\sum_{I\in\mathcal H}\Delta_Ig`$ for a finite
$`\mathcal H\subset\mathcal D`$. Then

```math
\|\mathcal M_{\mathcal D}g\|_p
 \leq 2^{6d+10}\|S_{\mathcal D}g\|_p,
 \qquad 1\leq p\leq\frac32.
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L34) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#maximal-square-function-estimate) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/MaximalSquareSolution.lean#L47) · [Library theorem](lean/ReyZygmund/Maximal/GlobalSquare.lean#L43).

### Scalar estimate

For $`a\in\mathbb R`$ and $`b>0`$, set $`\Psi_p(a,b)=a^2/b^{2-p}`$.
Let $`1<p\leq2`$, $`a,h,\eta\in\mathbb R`$, and $`b>0`$ with
$`b+\eta>0`$. Then

```math
\Psi_p(a+h,b+\eta)-\Psi_p(a,b)
 -\frac{2ah}{b^{2-p}}+\frac{(2-p)a^2\eta}{b^{3-p}}
 \geq\frac{p-1}{3-p}\frac{h^2}{\max\{b,b+\eta\}^{2-p}}.
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L47) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#scalar-estimate) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/SquareSolutions.lean#L20) · [Library theorem](lean/ReyZygmund/Weighted/Scalar.lean#L166).

### Finite dyadic setting

Let $`m\geq2`$. Fix $`I_0\in\mathcal D`$ and $`k\in\mathbb Z`$ with
$`2^{-k}\leq\ell(I_0^i)`$ for every $`i`$. Set

```math
\mathcal D_0^i
 =\{Q\in\mathcal D^i:Q\subset I_0^i,\ \ell(Q)\geq2^{-k}\},
\qquad
(\mathcal D_0^i)^\circ
 =\{Q\in\mathcal D_0^i:\ell(Q)>2^{-k}\}.
```

The smallest cubes have side length $`2^{-k}`$. For a coordinate set $`A`$,
write $`\mathcal D_0^A=\prod_{i\in A}\mathcal D_0^i`$ and
$`(\mathcal D_0^A)^\circ=\prod_{i\in A}(\mathcal D_0^i)^\circ`$,
omitting $`A`$ when it contains all coordinates. Put
$`E_{K^A}=\prod_{i\in A}E_{K^i}`$ and
$`\Delta_{K^A}=\prod_{i\in A}\Delta_{K^i}`$.
These operators leave the other coordinates unchanged. For $`A=\varnothing`$,
both products are the identity operator.

### One-coordinate weighted square-function estimate

Fix $`i`$; the estimate uses only this coordinate grid. Let $`u,v`$ be
functions on $`I_0^i`$, with $`v>0`$, both
constant on every $`Q\in\mathcal D_0^i`$ with $`\ell(Q)=2^{-k}`$. Then

```math
\sum_{Q\in(\mathcal D_0^i)^\circ}\int_Q
 \frac{|\Delta_Q u|^2}{\langle v\rangle_Q^{2-p}}
 \leq 2^{d_i(2-p)}\frac{3-p}{p-1}
       \int_{I_0^i}\frac{|u|^2}{v^{2-p}},
 \qquad 1<p\leq2.
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L55) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#one-coordinate-weighted-square-function-estimate) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/SquareSolutions.lean#L25) · [Library theorem](lean/ReyZygmund/Weighted/OneCoordinate.lean#L295).

### Product weighted square-function estimate

Let $`f`$ be supported on $`I_0`$, strictly positive there, and constant on
every product of smallest cubes, one of side length $`2^{-k}`$ in each
coordinate. For every nonempty coordinate set $`A`$,

```math
\sum_{K^A\in(\mathcal D_0^A)^\circ}\int_{K^A\times I_0^{A^c}}
 \frac{|\Delta_{K^A}f|^2}{(E_{K^A}f)^{2-p}}
 \leq 2^{(2-p)\sum_{i\in A}d_i}
       \left(\frac{3-p}{p-1}\right)^{|A|}\|f\|_p^p,
 \qquad 1<p\leq2.
```

Here $`A^c`$ is the complement of $`A`$ among the coordinate factors.
The region $`K^A\times I_0^{A^c}`$ uses the factor $`K^i`$ for $`i\in A`$
and $`I_0^i`$ otherwise.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L72) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#product-weighted-square-function-estimate) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProductSquareSolution.lean#L22) · [Library theorem](lean/ReyZygmund/Weighted/Product.lean#L191).

## Projection identities and estimates

### The projection

In the [finite dyadic setting](#finite-dyadic-setting), let $`f`$ be supported
on $`I_0`$, strictly positive there, and constant on every product of smallest
cubes. Let $`\mathcal G\subset\mathcal D_0`$ be arbitrary. Define

```math
F_{\mathcal G}
 =f-\sum_{\substack{L\in\mathcal D_0^\circ\\
                   L\subset I\text{ for some }I\in\mathcal G}}\Delta_Lf.
```

The following projection identities and estimates use this setting.

### Preserved averages

If $`\mathcal G`$ is weakly incomparable, then

```math
E_Rf=E_RF_{\mathcal G},\qquad R\in\mathcal G.
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L94) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#preserved-averages) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProjectionAverageSolutions.lean#L21).

### Averages in fewer coordinates

For every $`\mathcal G\subset\mathcal D_0`$, $`R\in\mathcal G`$ and $`x\in R`$,

```math
E_RF_{\mathcal G}(x)
 =\sum_{B\subsetneq\{1,\ldots,m\}}
       (-1)^{m+1+|B|}\left(\prod_{i\in B}E_{R^i}\right)F_{\mathcal G}(x).
```

No incomparability assumption is needed.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L109) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#averages-in-fewer-coordinates) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProjectionAverageSolutions.lean#L57).

### Cross-coordinate averages

For $`j\in\{1,\ldots,m\}`$, put $`A_j=\{1,\ldots,m\}\setminus\{j\}`$.
For $`K^{A_j}\in\mathcal D_0^{A_j}`$, set

```math
\mathcal A_{K^{A_j}}
 =\{I^j:I\in\mathcal G,\ K^{A_j}\subset I^{A_j}\}
   \cup\{Q^j\in\mathcal D_0^j:\ell(Q^j)=2^{-k}\}.
```

Let $`\mathcal P_{K^{A_j}}`$ consist of the maximal cubes of
$`\mathcal A_{K^{A_j}}`$. These cubes partition $`I_0^j`$. Define

```math
X_{K^{A_j}}g=\sum_{P^j\in\mathcal P_{K^{A_j}}}E_{P^j}g,
```

acting in coordinate $`j`$.

### Differences of the projected function

For every $`j\in\{1,\ldots,m\}`$ and $`K^{A_j}\in\mathcal D_0^{A_j}`$,

```math
\Delta_{K^{A_j}}F_{\mathcal G}
 =X_{K^{A_j}}\Delta_{K^{A_j}}f.
```

This is a pointwise identity of functions, with no incomparability assumption.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L126) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#differences-of-the-projected-function) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProjectionDifferencesSolution.lean#L22).

### Averaging rectangles

In the [finite setting](#finite-dyadic-setting), with the cross partitions
defined above, put

```math
\mathcal B
 =\bigcup_{j=1}^m
   \{K^{A_j}\times P^j:K^{A_j}\in\mathcal D_0^{A_j},
                         P^j\in\mathcal P_{K^{A_j}}\},
\qquad
\widehat{\mathcal G}=\mathcal G\cup\mathcal B.
```

The rectangles in $`\mathcal B`$ cover $`I_0`$.

### Unchanged projection and weak incomparability

For every $`\mathcal G\subset\mathcal D_0`$,

```math
F_{\widehat{\mathcal G}}=F_{\mathcal G}.
```

If $`\mathcal G`$ is weakly incomparable, then so is
$`\widehat{\mathcal G}`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L143) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#unchanged-projection-and-weak-incomparability) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/AveragingFamilySolutions.lean#L21).

### Representation of the averages

Suppose $`\mathcal G`$ is weakly incomparable. For every
$`R\in\widehat{\mathcal G}`$ and $`x\in R`$,

```math
E_Rf(x)
 =\sum_{B\subsetneq\{1,\ldots,m\}}
   (-1)^{m+1+|B|}\left(\prod_{i\in B}E_{R^i}\right)F_{\mathcal G}(x).
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L160) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#representation-of-the-averages) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/AveragingFamilySolutions.lean#L64).

### Square functions of the projection

Write $`F=F_{\mathcal G}`$. For $`j=1,\ldots,m`$, define

```math
S_{A_j}F
 =\left(\sum_{K^{A_j}\in(\mathcal D_0^{A_j})^\circ}
                   |\Delta_{K^{A_j}}F|^2\right)^{1/2},
\qquad
WF=\left(\sum_{j=1}^m(S_{A_j}F)^2\right)^{1/2}.
```

### Reduction to square functions

If $`\mathcal G`$ is weakly incomparable, then

```math
\|M_{\widehat{\mathcal G}}f\|_p
 \leq C_{m,d}(p')^{m-2}\|f\|_p+C_{m,d}\|WF\|_p,
 \qquad 1<p\leq\frac32.
```

The constant depends only on $`m`$ and $`d`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L179) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#reduction-to-square-functions) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProjectedSquareSolutions.lean#L28).

### Square-function estimate for the projected function

For every $`\mathcal G\subset\mathcal D_0`$,

```math
\int_{I_0}\frac{(WF)^2}{(M_{\mathcal B}f)^{2-p}}
 \leq C_{m,d}(p')^{m-1}\|f\|_p^p,
 \qquad 1<p\leq2.
```

The constant depends only on $`m`$ and $`d`$. No incomparability assumption
is needed.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L200) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#square-function-estimate-for-the-projected-function) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/ProjectedSquareSolutions.lean#L135).

## Covering, selection and slicing

### Prescribed-scale covering

For $`s>0`$, set $`\rho(s)=\lceil\log_2s\rceil+2`$. In each
coordinate factor, use the $`3^{d_i}`$ dyadic grids

```math
\mathcal D^{i,a}
 =\{2^k([0,1)^{d_i}+z+(-1)^ka):k\in\mathbb Z,\ z\in\mathbb Z^{d_i}\},
\qquad a\in\{0,1/3,2/3\}^{d_i}.
```

Every closed axis-parallel cube $`Q\subset\mathbb R^{d_i}`$ of side length
$`s`$ is contained in a cube $`P`$ from one of these grids with
$`\ell(P)=2^{\rho(s)}`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L224) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#prescribed-scale-covering) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/CoveringSolution.lean#L15) · [Library theorem](lean/ReyZygmund/Geometry/PrescribedCover.lean#L77).

### Córdoba–Fefferman selection

Let $`\mathcal F`$ be a finite family in a product of $`m\geq1`$
dyadic cube grids. There is a $`\mathcal G\subset\mathcal F`$ such that

```math
|\mathrm{sh}(\mathcal F)|\leq C_m|\mathrm{sh}(\mathcal G)|,
\qquad
|I\cap\mathrm{sh}(\mathcal G\setminus\{I\})|\leq\tfrac12|I|
\quad(I\in\mathcal G).
```

The constant depends only on the number $`m`$ of factors.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L238) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#córdoba-fefferman-selection) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/SelectionSolution.lean#L19) · [Library theorem](lean/ReyZygmund/Selection/Shadow.lean#L126).

### Rounded families and slices

Let $`m\geq3`$ and let
$`\phi:(0,\infty)^{m-1}\to(0,\infty)`$ be coordinatewise nondecreasing.
With the rounding rule and shifted grids above, put

```math
\Gamma_\phi=
\{(\rho(s_1),\ldots,\rho(s_{m-1}),\rho(\phi(s))):
                       s\in(0,\infty)^{m-1}\}.
```

For $`\tau=(\tau_1,\ldots,\tau_m)`$, with
$`\tau_i\in\{0,1/3,2/3\}^{d_i}`$, set

```math
\mathcal D_\tau=\prod_{i=1}^m\mathcal D^{i,\tau_i},
\qquad
\mathcal E_\phi^\tau
=\{I\in\mathcal D_\tau:
    (\log_2\ell(I^1),\ldots,\log_2\ell(I^m))\in\Gamma_\phi\}.
```

For a rectangle family $`\mathcal G`$ and $`t\in\mathbb R^{d_m}`$,
its slice is

```math
\mathcal G_t=\{I^1\times\cdots\times I^{m-1}:
                   I\in\mathcal G,\ t\in I^m\}.
```

### Weak incomparability of slices

Fix $`\tau`$, and let $`\mathcal G\subset\mathcal E_\phi^\tau`$
be incomparable. For every $`t\in\mathbb R^{d_m}`$, the family
$`\mathcal G_t`$ is weakly incomparable. Each member of $`\mathcal G_t`$
is the projection of exactly one $`I\in\mathcal G`$ with $`t\in I^m`$,
and

```math
h_{\mathcal G}(x,t)=h_{\mathcal G_t}(x),
\qquad x\in\mathbb R^{d_1}\times\cdots\times\mathbb R^{d_{m-1}}.
```

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L251) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#weak-incomparability-of-slices) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/SliceSolutions.lean#L20) · [Library proofs](lean/ReyZygmund/Geometry/RoundedSlicesIco.lean).

### Half-sparsity of slices

Let $`m\geq2`$ and let $`\mathcal G\subset\mathcal D`$ be finite.
Suppose that

```math
|I\cap\mathrm{sh}(\mathcal G\setminus\{I\})|\leq\tfrac12|I|,
\qquad I\in\mathcal G.
```

Then $`\mathcal G_t`$ is $`1/2`$-sparse for every
$`t\in\mathbb R^{d_m}`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L267) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#half-sparsity-of-slices) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/SliceSolutions.lean#L37) · [Library theorem](lean/ReyZygmund/Selection/SliceSparsity.lean#L94).

## Endpoint, overlap and sharpness results

These results use the [global setting](MAIN-STATEMENTS.md#setting-and-notation)
of the main theorems.

<a id="endpoint-estimate-for-the-rounded-dyadic-families"></a>

### Rounded dyadic endpoint estimate

For the [rounded family](#rounded-families-and-slices) $`\mathcal E_\phi^\tau`$,
for every $`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$ and every $`\lambda>0`$,

```math
|\{x:M_{\mathcal E_\phi^\tau}f(x)>\lambda\}|
\leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
\left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
```

The constant depends only on $`m`$ and $`d`$, not on $`\phi`$ or $`\tau`$.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L281) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#rounded-dyadic-endpoint) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L68) · [Theorem in the main development](lean/ReyZygmund/Main/Endpoints.lean#L19).

### Dyadic Zygmund conjecture

Let $`m\geq3`$ and let $`\Phi:\mathbb Z^{m-1}\to\mathbb Z`$ be
coordinatewise nondecreasing. Let $`\mathcal Z_\Phi\subset\mathcal D`$
be the family of rectangles with side-length tuple

```math
\bigl(2^{k_1},\ldots,2^{k_{m-1}},
                 2^{\Phi(k_1,\ldots,k_{m-1})}\bigr),
\qquad (k_1,\ldots,k_{m-1})\in\mathbb Z^{m-1}.
```

For every $`f\in L^1_{\mathrm{loc}}(\mathbb R^d)`$ and $`\lambda>0`$,

```math
|\{x:M_{\mathcal Z_\Phi}f(x)>\lambda\}|
 \leq C_{m,d}\int_{\mathbb R^d}\frac{|f(x)|}{\lambda}
 \left[\log\!\left(e+\frac{|f(x)|}{\lambda}\right)\right]^{m-2}dx.
```

The constant depends only on $`m`$ and $`d`$, not on $`\Phi`$ or the grids.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L296) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#dyadic-zygmund-conjecture) · [Proof](lean/ReyZygmund/MathlibOnly/Proof/DyadicEndpointSolution.lean#L18) · [Library theorem](lean/ReyZygmund/Continuous/DyadicEndpoint.lean#L21).

<a id="sparse-overlap-with-a-monotone-zygmund-scale-relation"></a>

### Sparse Φ-Zygmund overlap estimate

If $`\mathcal G\subset\mathcal Z_\Phi`$ is $`\eta`$-sparse with finite
shadow, where $`0<\eta\leq1`$, then

```math
\int_{\mathrm{sh}(\mathcal G)}
\exp\!\left(c h_{\mathcal G}^{1/(m-1)}\right)dx
\leq C|\mathrm{sh}(\mathcal G)|,
```

where $`c,C>0`$ depend only on $`m`$, $`d`$ and $`\eta`$, not on $`\Phi`$
or the dyadic grids.

The implication from the Zygmund estimate to this overlap bound is due to Rey.

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L308) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#sparse-φ-zygmund-overlap) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L77) · [Theorem in the main development](lean/ReyZygmund/Main/PhiSparse.lean#L21).

<a id="sharpness-for-sparse-incomparable-zygmund-families"></a>

### Sharpness for the classical dyadic Zygmund family

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

Lean: [Independent statement](lean/ReyZygmund/MathlibOnly/SupportingStatements.lean#L324) · [Definitions](lean/ReyZygmund/MathlibOnly/README.md#sharpness-for-the-classical-dyadic-zygmund-family) · [Proof](lean/ReyZygmund/MathlibOnly/Solutions.lean#L94) · [Theorem in the main development](lean/ReyZygmund/Main/Sharpness.lean#L24).
