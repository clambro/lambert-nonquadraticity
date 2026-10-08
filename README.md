# Nonquadraticity of Lambert Series Values

**[Read the paper (PDF)](Nonquadraticity_of_Lambert_Series_Values.pdf)** · **[LaTeX source](Nonquadraticity_of_Lambert_Series_Values.tex)** · **[Lean proofs and verification notes](formalization/README.md)**

## AI disclosure

Generative AI performed nearly all of the mathematical work: it developed the determinant construction and the algebraic-degree arguments, conducted the literature search, wrote the manuscript, and produced the Lean formalization. I directed and supervised the investigation.

## Main result

For every integer $q\geq2$, the Lambert value

$$
F(q)=\sum_{n=1}^{\infty}\frac1{q^n-1}
$$

is **neither rational nor quadratic irrational**: the numbers $1,F(q),F(q)^2$ are linearly independent over $\mathbb Q$. This includes the **Erdős–Borwein constant $F(2)$**. Erdős proved irrationality at integer bases in 1948; the result here excludes quadratic relations as well.

For rational bases $q=a/b>1$, the same theorem improves the known bounds for [Erdős Problem 1049](https://www.erdosproblems.com/1049), enlarging the irrationality region from $\log b/\log a<0.405683\ldots$ to **$\log b/\log a<0.5728$**.

The underlying theorem applies to every real algebraic base $q>1$. Write $K=\mathbb Q(q)$, let $M(q)$ be the Mahler measure of its primitive irreducible integer polynomial, and set

$$
C=42963+\frac{428220}{\pi^2},\qquad S=202140,\qquad
\lambda=\frac CS=0.4271829289\ldots.
$$

**Degree-exclusion theorem.** For an integer $e\geq0$, if

$$
e\lambda\log M(q)<\log q,
$$

then no nonzero polynomial over $K$ of degree at most $e$ vanishes at $F(q)$.

For integer bases, $M(q)=q$ and $2\lambda<1$, giving the headline result. The same criterion has three further consequences:

- **Pisot and Salem bases:** nonquadraticity holds over $\mathbb Q(q)$, since these bases also satisfy $M(q)=q$.
- **Rational bases:** for integers $a>b>0$, relations over $\mathbb Q$ of degree at most $e$ are excluded when $\log b/\log a<1-e\lambda$. Taking $e=1$ gives the irrationality region above; $e=2$ gives nonquadraticity in the smaller region $\log b/\log a<1-2\lambda$.
- **Radical bases:** if $q^n=m$ for positive integers $n,m$, put $g=[\mathbb Q(q):\mathbb Q]$. Every conjugate has modulus $q$, so the criterion becomes $eg\lambda<1$. In particular, $F(\sqrt m)\notin\mathbb Q(\sqrt m)$ for every integer $m\geq2$.

## Proof outline

### Positive determinants and decay

For an indeterminate base $U$, define a linear functional by

$$
\mu_X(t^r)=\frac1{U^{r+1}-1},\qquad
\mu_X\!\left(\frac1{U^j-t}\right)
=X-\sum_{v=1}^{j}\frac1{U^v-1}.
$$

Partial fractions extend it to the rational functions used below. Take $h=60N$, $k=3N$, and form

$$
\Delta_{h,k}(U,X)=\det_{0\leq i,j<h}
\mu_X\!\left(\frac{t^{k+i+j}}{\prod_{v=k}^{k+h-1}(U^v-t)}\right).
$$

At $(U,X)=(q,F(q))$, the functional is integration against the positive measure $\sum_{v\geq1}q^{-v}\delta_{q^{-v}}$. The determinant is therefore a Gram determinant for $1,t,\ldots,t^{h-1}$ with strictly positive weight and infinite support. This proves strict positivity, which will prevent the eventual algebraic norm from vanishing.

Normalize by $Q_N(U,X)=U^{-G_N}\Delta_{h,k}(U,X)$, where $G_N=5940N^3-90N^2$. Comparison with a geometric Cauchy determinant gives

$$
\log Q_N(q,F(q))=-S N^3\log q+o(N^3).
$$

The normalization also makes every coefficient bounded at infinity. On each fixed circle $|u|=\rho>1$, the determinant grows only as $\exp(O(N\log N))$, uniformly for $X$ in a bounded disk.

### Clearing denominators without losing the decay

The coefficients of $Q_N$ have poles only at zero and roots of unity. At zero, a finite-part expansion converts the determinant into sums over evaluation and derivative columns. Their valuations reduce to an explicit minimization over node indices, giving the clearing exponent $15963N^3-10N$.

At a primitive $n$th root of unity, Taylor coefficients lie in nested spaces of dimension at most $2n(\ell+1)$ at order $\ell$. A determinant cannot have too many columns in these small spaces without vanishing. This forces cancellation of cyclotomic poles; a separate bound on the rank of the residue matrix improves the estimate further.

Combining these bounds gives a monic clearing polynomial $J_N(U)$ such that

$$
\mathcal P_N(U,X)=J_N(U)Q_N(U,X)\in\mathbb Z[U,X],
\qquad
\deg_U\mathcal P_N\leq(C+o(1))N^3,\quad
\deg_X\mathcal P_N\leq60N.
$$

The constant $C$ comes from summing the cyclotomic exponents with weights $\varphi(n)$, using the summatory totient asymptotic. Monic division ensures integer coefficients. At the distinguished real base,

$$
\mathcal P_N(q,F(q))>0,\qquad
\log\mathcal P_N(q,F(q))=(C-S)N^3\log q+o(N^3).
$$

Thus denominator clearing preserves cubic decay. The circle bounds and maximum modulus control the cleared polynomial at every other complex embedding, including those sending $q$ inside the unit disk.

### The product-formula contradiction

Suppose $\alpha=F(q)$ is algebraic over $K$, and let $E=K(\alpha)$ have relative degree $r$. The nonzero number $x_N=\mathcal P_N(q,\alpha)$ is exponentially small at the distinguished real embedding. At every other complex embedding $\sigma$,

$$
\log|\sigma(x_N)|\leq C N^3\log\max(1,|\sigma(q)|)+o(N^3).
$$

At finite places, integrality of the polynomial coefficients bounds the contribution from $q$ by its height times the degree in $U$. The contribution from $\alpha$ is only $O(N)$, because the degree in $X$ is at most $60N$.

Summing over all places and applying the product formula forces

$$
S\log q\leq C H_E(q)=rC\log M(q),
$$

where $H_E$ is the unnormalized logarithmic height and the equality is the height–Mahler identity. If $r\leq e$, this contradicts the theorem's strict inequality.

The Lean development also includes a refinement using six presentations of the determinant that raises the rational irrationality threshold to $0.573290$; the paper records it in a closing remark.

## Lean verification

The entire proof is formalized using Mathlib, including the totient asymptotic and height–Mahler identity. There are no additional mathematical hypotheses, admitted proofs, or project axioms. All project sources are included, and the Lean and dependency versions are pinned.

With Lean installed through `elan`, run:

```bash
cd formalization
lake exe cache get
bash verification/check.sh
```

The check builds the development and audits its axioms. The [formalization guide](formalization/README.md) maps the theorems to their declarations and gives commands for kernel replay and certificate reproduction.
