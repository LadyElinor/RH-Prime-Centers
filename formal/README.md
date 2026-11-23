# A Lean certificate for the interval between samples

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

## Reproduce

With Elan available, run the following from this directory. The toolchain file selects Lean 4.24.0. Lake pins Mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. This standalone module can be checked without building an RH library.

```sh
lake exe cache get Mathlib.Analysis.Convex.Deriv Mathlib.Analysis.SpecialFunctions.Complex.Arg Mathlib.Analysis.Complex.ExponentialBounds Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp
mkdir -p .lake/build
lake env lean -o .lake/build/WindowCertificate.olean WindowCertificate.lean
lake env lean --run Replay.lean .lake/build/WindowCertificate.olean
```

To reproduce the external numerical premises, use Python with `python-flint==0.9.0` and run `python ../notes/certify_core3_spectrum.py --lean-inputs`. The FLINT and Lean checks were both run for this release. We used local source directories for the pinned dependencies and Mathlib's compiled cache when running the Lake commands.

The output concerns a truncated sum over known zeros on three specified doublings. The signed estimate for arbitrarily late doublings, the prime-square asymptotic, and the passage from Core 3 to the uniform smoothed remainder remain separate mathematical statements. [Current analytic bounds and source credits](../notes/critical-line-budget.md) · [Pinned Mathlib concavity theorem](https://github.com/leanprover-community/mathlib4/blob/f897ebcf72cd16f89ab4577d0c826cd14afaafc7/Mathlib/Analysis/Convex/Deriv.lean#L246-L258) · [FLINT zero isolation](https://flintlib.org/doc/acb_dirichlet/index.html)
