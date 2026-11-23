# From Pi’s explicit formula to the prime-power tent

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

## Reproduce the check

From this directory, with Elan, Git, Python 3, and network access, run

```sh
lake update
lake exe cache get
lake env python3 verify.py
```

The [verifier](verify.py) fetches Pi’s source at commit `25bc57f3919f3578d396b71f8bc2cf9b3675ac63` and checks SHA-256 `28fab02c68c3a5a4d596e72f68caa532d14ddf8c70a5a2abfe5c4e821bf76e68`. An existing download can be supplied with `--source /path/to/Solution.lean`. It compiles that source unchanged, the tent module, the adapter and the two resulting theorems together on Lean 4.34.1 with Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Running from this directory selects that toolchain. The parent project also checks the adapter as an implication on Lean 4.24.0.

The verifier checks the axiom reports for Pi’s theorem and both resulting theorems, then replays the four modules separately against their imported dependencies with Lean’s native `leanchecker`. The reports list `propext`, `Classical.choice`, and `Quot.sound`. The check uses Mathlib’s prebuilt dependencies. Two changes to a temporary copy of the adapter test the correspondence. Lean rejected including zeros exactly at the cutoff and assigning each zero a single copy regardless of analytic order.

## The next mathematical question

The prime-power formula now controls the truncation error on every sufficiently late doubling. To obtain the corresponding ordinary-prime formula in Lean, the next step is to identify the signed integral with the weighted prime-power sum and then account for the powers omitted from the ordinary-prime sum. Prime squares supply a positive term of order $\sqrt y$. Even after that step, a direct proof of recurring positivity requires a signed estimate for the retained zeros across an unbounded sequence of whole intervals. [Ordinary-prime derivation](../../notes/core3-window-roadmap.md) · [The remaining sign estimate](../../notes/critical-line-budget.md)

Pi authored the standalone Core 3 proof. Osgood001 staged the cited source in the project based on Levent Alpöge’s formalization. LadyElinor directed this investigation, with OpenAI Codex and ChatGPT assisting on the downstream work. The earlier dyadic setup is due to bramble_trace and the three-scale criterion to Lee Crossley. Lean and Mathlib supply the kernel and mathematical library. Mathlib credits Alastair Irving, Terry Tao and Ruben Van de Velde for the Chebyshev module. [Pi’s source](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Staging and verification history](https://github.com/Osgood001/riemann-hypothesis/pull/4) · [Mathlib’s Chebyshev functions](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Chebyshev.lean#L73-L85) · [Project credits](../../CREDITS.md)
