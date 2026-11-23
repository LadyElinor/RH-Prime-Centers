# From Pi’s explicit formula to the ordinary-prime tent

The two tent theorems in [PinnedFormula.lean](PinnedFormula.lean) apply Pi’s `AlpogeRHCore3.explicitFormula` directly. The arithmetic function in the conclusion is Mathlib’s Chebyshev function $\psi(x)=\sum_{1\le n\le x}\Lambda(n)$, which counts each prime power $p^k$ with weight $\log p$.

Write $Lf(y)=2(Af(y)-Af(2y))$ for the signed tent operator, where $Af(y)=y\int_y^{2y} f(u)u^{-2}\,du$. Let $Z_Y$ be the distinct zeta zeros in the open critical strip with $|\Im\rho|<Y$, and $m_\rho$ the analytic order of the zero. Set

$$
S_Y(y)=\sum_{\rho\in Z_Y}m_\rho\,
\frac{(2^\rho-1)(2^\rho-2)}{\rho(\rho-1)}\,y^\rho.
$$

**Result.** For every $\varepsilon>0$ there is a starting scale beyond which every $Y$ and every real $y\in[Y,2Y]$ satisfy

$$
\big|L(\psi-\mathrm{id})(y)-S_Y(y)\big|<\varepsilon\sqrt y.
$$

The same height $Y$ is used throughout that doubling. There is also one constant $C>0$ such that the absolute error is at most $2C(8\log^2(8Y^2)+\log(8Y)+S)$ for every $Y\ge2$, where $S=\sum_{\rho\in Z_1}m_\rho/|\rho|$. The final theorem exposes $C$ existentially, as the upstream statement does. RH is absent from its hypotheses. [Bound and uniform limit](PinnedFormula.lean) · [Definition of the operator and its coefficient](../TentTransfer.lean)

## How the arithmetic enters

1. The upstream module and the adapter pick different Lean decision procedures for the test “is this the trivial character?” The proof checks the two cases explicitly, so both formulas choose the same main term. The trivial character modulo one is primitive and takes the value one at every integer. Its L-function equals the Riemann zeta function, including equality as functions when taking analytic orders.
2. The arithmetic sum uses the positive integers up to and including the floor of $u$. The adapter identifies this sum with Mathlib’s $\psi$ at every real input. Monotonicity of the real sum and continuity of the kernel away from zero give the needed integrability.
3. For $Y\ge2$, Core 3 gives finiteness of $Z_Y$. For each zero the adapter makes one index for every integer $0\le j<m_\rho$. Summing over those indices exactly recovers the analytic-order-weighted sum. Both signs of the ordinate are included. The height-one correction is a finite, nonnegative sum. Finiteness follows by inclusion in the set at height two, where the upstream theorem applies.
4. At height $T=Y$ the upstream formula supplies the pointwise error bound throughout $[Y,8Y]$. The tent transfer then applies simultaneously for all $y\in[Y,2Y]$. [Conductor-one adapter](../Core3Adapter.lean)

## The discrete ordinary-prime formula

For $y>0$, let $P(y)$ be the sum of $\log p$ over ordinary primes with weight $2(1-y/p)$ for $y<p\le2y$ and $4y/p-1$ for $2y<p\le4y$. The weight is zero at both outer endpoints and equals one at $2y$. Define $D(y)=2y\log 2-P(y)$. Define $Q_2(y)$ and $Q_{\ge3}(y)$ by the same weights at $p^2$ and $p^k$ with $k\ge3$, respectively, each with coefficient $\log p$.

Applying Abel summation separately on the two halves gives an exact identity at every positive real scale,

$$
D(y)=L(\psi-\mathrm{id})(y)+Q_2(y)+Q_{\ge3}(y).
$$

The two integration boundary terms at $2y$ cancel. Dropping a prime power increases the deficit by its weighted contribution. At $y=2$, the square $4$ carries weight one and the cube $8$ carries weight zero. The difference between the two deficits is exactly $\log 2$. [Discrete identity, positivity and exponent classification](DiscreteTent.lean)

The cumulative weight of prime squares up to $x$ is exactly $\vartheta(\sqrt x)$. For $x\ge1$, the Costa Pereira upper bound on $\psi(x)-\vartheta(x)$ gives a main term $\psi(\sqrt x)$ and two smaller terms at $x^{1/3}$ and $x^{1/5}$. After subtracting $\vartheta(\sqrt x)$, the remaining difference at $\sqrt x$ is $O(x^{1/4})$ by the Chebyshev bound. The cumulative mass from exponents at least three is therefore $O(x^{1/3})$. The tent has weights between zero and one, so its higher powers also contribute $O(y^{1/3})$. [Prime-square bijection and higher-power bounds](HigherPowers.lean)

Consequently, for each $\varepsilon>0$, every sufficiently large $Y$ satisfies

$$
\left|D(y)-S_Y(y)-Q_2(y)\right| < \varepsilon\sqrt y
\qquad (Y\le y\le 2Y).
$$

Here $Q_2(y)$ is the **actual finite prime-square sum** at the sliding scale $y$. The finite-height envelope above carries over exactly when both $Q_2$ and $Q_{\ge3}$ are retained. With only $Q_2$ retained, the higher-power error is absorbed in the uniform limit. [Ordinary-prime residual, finite bound and uniform limits](OrdinaryFormula.lean)

## Reproduce the check

From this directory, with Elan, Git, Python 3, and network access, run

```sh
lake update
lake exe cache get
lake env python3 verify.py
```

The [verifier](verify.py) fetches Pi’s source at commit `25bc57f3919f3578d396b71f8bc2cf9b3675ac63` and checks SHA-256 `28fab02c68c3a5a4d596e72f68caa532d14ddf8c70a5a2abfe5c4e821bf76e68`. An existing download can be supplied with `--source /path/to/Solution.lean`. It compiles that source unchanged together with the downstream modules on Lean 4.34.1 with Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Running from this directory selects that toolchain. The parent project also checks the adapter as an implication on Lean 4.24.0.

The verifier checks the axiom reports for Pi’s theorem and the selected downstream theorems, then replays the seven modules separately against their imported dependencies with Lean’s native `leanchecker`. The reports list `propext`, `Classical.choice`, and `Quot.sound`. The check uses Mathlib’s prebuilt dependencies. Two changes to a temporary copy of the adapter test the correspondence. Lean rejected including zeros exactly at the cutoff and assigning each zero a single copy regardless of analytic order.

Run `python3 check_discrete.py` for an independent arithmetic check. It integrates the step function exactly on each piece and compares rational coefficients of each $\log p$ against the direct tent sum, at the 257 scales $y=i/4$ for $1\le i\le257$. [Finite check](check_discrete.py)

## The next mathematical question

The next formal step is to replace $Q_2(y)$ by $(6\sqrt2-8)\sqrt y+o(\sqrt y)$ using the prime number theorem. The written square-bias derivation is linked below. The separate sign question asks for a lower bound on the retained zero sum across arbitrarily late whole intervals. [Ordinary-prime derivation](../../notes/core3-window-roadmap.md) · [The remaining sign estimate](../../notes/critical-line-budget.md)

Pi authored the standalone Core 3 proof. Osgood001 staged the cited source in the project based on Levent Alpöge’s formalization. LadyElinor directed this investigation, with OpenAI Codex and ChatGPT assisting on the downstream work. The earlier dyadic setup is due to bramble_trace and the three-scale criterion to Lee Crossley. Lean and Mathlib supply the kernel and mathematical library. Mathlib credits Alastair Irving, Terry Tao and Ruben Van de Velde for the Chebyshev module. [Pi’s source](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Staging and verification history](https://github.com/Osgood001/riemann-hypothesis/pull/4) · [Mathlib’s Chebyshev functions](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Chebyshev.lean#L73-L85) · [Project credits](../../CREDITS.md)

Xavier Roblot authored Mathlib’s Abel summation module. Bhavik Mehta authored the von Mangoldt module. The higher-power proof uses the Costa Pereira inequalities and Chebyshev bounds formalized in the Chebyshev module cited above. [Abel summation](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/AbelSummation.lean#L129-L136) · [von Mangoldt weights](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean#L73-L99) · [Costa Pereira inequalities](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Chebyshev.lean#L584-L604)
