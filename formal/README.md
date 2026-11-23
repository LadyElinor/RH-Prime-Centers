# Lean proofs for the ordinary-prime tent

A low point between two sampled positions matters when the inequality must hold at every real position. This module proves the step used by the [finite spectral checker](../notes/certify_core3_spectrum.py) to cover those gaps.

For a twice differentiable real function, suppose its values at both ends of a cell of width $h$ are at least $A$ and its second derivative is bounded above by $K\ge0$. Then the value throughout the cell is at least $A-Kh^2/8$. Subtracting $Kx^2/2$ gives a concave function. The chord inequality and $t(1-t)\le1/4$ give the constant. The quadratic $f(x)=(x^2-x)/2$ on $[0,1]$ attains the loss $1/8$ at the midpoint.

In the prime-window application the variable is $v=\log(y/Y)$, the start parameter is $s=\log Y$, and the finite spectrum is

$$q(v)=2\Re\sum_j c_j\exp(i g_j(s+v)).$$

Here $c_j=H(1/2+ig_j)$ for the positive ordinates below the cutoff. Lean proves the complex-to-real identity, the derivative bound $q''(v)\le\sum_j2|c_j|g_j^2$, and the interpolation estimate on every cell. The theorem applies to any finite coefficient family.

## What was checked

* **Lean** proves that a lower bound $A$ at all 257 nodes and an upper bound $M$ for the curvature sum suffice for a claimed floor $L$ throughout $0\le v\le\log 2$, if $L\le A-M(0.6931471808/256)^2/8$. Mathlib proves the upper bound on $\log 2$. The second declaration checks this rational arithmetic for each of the three rows below.
* **FLINT** isolates and counts the finite zeta zeros. It encloses the complex coefficients and all node values with ball arithmetic and rounds the two inputs outwards. The checker can print the exact rationals passed to the Lean arithmetic. Their numerators are in the table.
* **Replay** reads the compiled module, checks that the two named theorems are present, and resubmits the local declarations to Lean’s kernel against the pinned imported environment. It rejects local axioms, unsafe or partial declarations, and direct uses of a placeholder. The axiom reports for both theorems list only `propext`, `Classical.choice`, and `Quot.sound`. The replay checked 10 local declarations. Imported Mathlib artifacts were used as dependencies.

| $Y$ | Positive ordinates | $10^9 A$ | $10^9 M$ | Lower bound for $q$ everywhere |
|---:|---:|---:|---:|---:|
| 32 | 4 | −129507246 | 49223601912 | −0.129553 |
| 64 | 14 | −75190770 | 155325919655 | −0.075334 |
| 128 | 42 | −86210961 | 427664801569 | −0.086603 |

For a negative control we raised the first claimed floor by one millionth, keeping its inputs fixed. Lean rejected the resulting arithmetic obligation. A stronger certificate would need tighter inputs or a sharper estimate for this particular spectrum.

## Uniform error and the signed zero sum

Each position $y$ in a doubling uses the two intervals $[y,2y]$ and $[2y,4y]$. As $y$ ranges from $Y$ to $2Y$, their union lies in $[Y,8Y]$. The [tent transfer module](TentTransfer.lean) keeps one truncation height $T=Y$ for that whole input interval. Write

$$A f(y)=y\int_y^{2y}\frac{f(t)}{t^2}\,dt,\qquad Lf(y)=2\big(Af(y)-Af(2y)\big).$$

If $\lVert e(u)\rVert\le M$ on $[Y,8Y]$ then $\lVert Le(y)\rVert\le2M$ at every real $y\in[Y,2Y]$. Each average has positive kernel mass $1/2$. To attain the factor 2 at any chosen $y>0$, take a real error equal to $+1$ up to $2y$ and $-1$ thereafter. Its averages at $y$ and $2y$ are $+1/2$ and $-1/2$, giving $Le(y)=2$.

For a finite family of complex numbers $\rho\ne0,1$, give each occurrence its own index, including repeated values. The module integrates each signed term $-u^\rho/\rho$ exactly. Its contribution to $L$ is $H(\rho)y^\rho$, where

$$H(\rho)=\frac{(2^\rho-1)(2^\rho-2)}{\rho(\rho-1)}.$$

Let $f$ be the input to $L$, with integrable weighted inputs on the dyadic intervals. Suppose the error between $f(u)$ and the finite sum of $-u^\rho/\rho$ is at most $C\big(u\log^2(uY)/Y+\log u+S\big)$ for $Y\le u\le8Y$, with $Y\ge2$ and $C\ge0$. Then

$$\left|Lf(y)-\sum_\rho H(\rho)y^\rho\right|
\le 2C\big(8\log^2(8Y^2)+\log(8Y)+S\big)
\qquad(Y\le y\le2Y).$$

For fixed $C,S$ and this bound at every $Y\ge2$, the difference divided by $\sqrt y$ tends to zero uniformly across the doubling. The finite family can change with $Y$. Lean checks this statement with the quantifiers in that order in `finite_formula_vanishing`.

The intended arithmetic input is $f(u)=\psi(u)-u$. Pi’s upstream Core 3 theorem supplies a pointwise bound with multiplicities as analytic orders and a strict height cutoff. Connecting that exact declaration to this module still requires a conductor-one adapter. The contribution of the omitted prime powers, including the positive prime-square term, enters separately when passing to ordinary primes. The signed lower bound for arbitrarily late doublings remains open by this route. [Pi’s staged Core 3 theorem in Levent Alpöge’s project](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Derivation, contributors and sources](../notes/core3-window-roadmap.md) · [Remaining signed estimate](../notes/critical-line-budget.md)

The transfer replay accepted 43 local declarations. The six theorems selected for axiom reporting used only `propext`, `Classical.choice`, and `Quot.sound`. Lean rejected two deliberately altered proofs. One reduced the bound from $2M$ to $M$. The other reversed the sign of the spectral coefficient. Mathlib provides the complex-power antiderivative and the logarithmic limit. [Pinned integral theorem](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean#L111-L126) · [Pinned growth estimate](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L330-L341)

## Reproduce

With Elan available, run the following from this directory. The toolchain file selects Lean 4.24.0. Lake pins Mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. These standalone modules can be checked without building an RH library.

```sh
lake exe cache get Mathlib.Analysis.Convex.Deriv Mathlib.Analysis.SpecialFunctions.Complex.Arg Mathlib.Analysis.Complex.ExponentialBounds Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp
lake exe cache get Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
mkdir -p .lake/build
lake env lean -o .lake/build/WindowCertificate.olean WindowCertificate.lean
lake env lean --run Replay.lean .lake/build/WindowCertificate.olean
lake env lean -o .lake/build/TentTransfer.olean TentTransfer.lean
lake env lean --run Replay.lean tent .lake/build/TentTransfer.olean
```

To reproduce the external numerical premises, use Python with `python-flint==0.9.0` and run `python ../notes/certify_core3_spectrum.py --lean-inputs`. The FLINT and Lean checks were both run for this release. We used local source directories for the pinned dependencies and Mathlib's compiled cache when running the Lake commands.
