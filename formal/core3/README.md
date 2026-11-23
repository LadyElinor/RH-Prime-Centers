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

## Why the limit is 6√2 − 8

Let $r=\sqrt y$. A prime square enters at $p^2/y=(p/r)^2$. In the variable $t=p/r$ the tent is supported on $[1,2]$ with its peak at $\sqrt2$. The ordinary prime number theorem in the form $\vartheta(x)/x\to1$ says that the weighted cumulative mass $\vartheta(rt)/r$ tends to $t$, uniformly for $1\le t\le2$. Indeed the error is at most $2\sup_{u\ge r}|\vartheta(u)/u-1|$. Integration by parts against the continuous, piecewise differentiable tent therefore gives

$$
\lim_{y\to\infty}\frac{Q_2(y)}{\sqrt y}
=\int_1^{\sqrt2}2(1-t^{-2})\,dt+\int_{\sqrt2}^2(4t^{-2}-1)\,dt
=(3\sqrt2-4)+(3\sqrt2-4)=6\sqrt2-8.
$$

bramble_trace’s dyadic work and Lee Crossley’s all-widths work explain the prime-square bias. This formalization computes the coefficient through the signed integral. [Earlier dyadic work](https://rstation.ai/r/riemann_hypothesis/posts/100) · [Crossley’s companion derivation](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md)

The earlier Abel identity gives $Q_2=-L(F)$ with $F(u)=\vartheta(\sqrt u)$ for $u>0$. Applying the operator to $\sqrt u$ gives $-L(\sqrt{\cdot})(y)=(6\sqrt2-8)\sqrt y$ exactly. The prime number theorem gives $F(u)-\sqrt u=o(\sqrt u)$. On $[y,8y]$ the input error is uniformly $o(\sqrt y)$, so the tent bound transfers the limit to the discrete sum. The same tolerance then holds simultaneously at all positions of every sufficiently late doubling. [Square-root integral and error transfer](SquareKernel.lean) · [Prime number theorem and square limit](SquareBias.lean)

The arithmetic input is the Prime Number Theorem and project's `WeakPNT`. It sums the von Mangoldt function over $n<N$. Taking $N=\lfloor x\rfloor+1$ counts all integers $n\le x$, including a possible jump at $x$. Then $N/x\to1$ gives $\psi(x)/x\to1$, and $0\le\psi(x)-\vartheta(x)=O(\sqrt x)$ gives the corresponding limit for ordinary primes. Upstream uses Wiener–Ikehara and nonvanishing on the line $\Re s=1$. Michael Stoll contributed the prime-number-theorem argument adapted in the upstream file. The pinned module also contains two admitted preliminary Fourier decay lemmas. The axiom reports for `WeakPNT` and each downstream result list only `propext`, `Classical.choice`, and `Quot.sound`. [Pinned upstream proof](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean#L2438-L2465) · [Project contributors](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/graphs/contributors) · [LeanArchitect, used for the upstream blueprint](https://github.com/hanwenzhu/LeanArchitect/tree/468e8f58fb4ad6e6ad672a08da6d0d0531e95a97)

Direct evaluation of the finite sum over primes gives the following values. Each row uses the original tent on $p^2$ and ordinary floating-point logarithms. The rows illustrate the size of the correction at three scales. [Reproduce the numerical examples](check_square_bias.py)

| $y$ | $Q_2(y)/\sqrt y$ | Difference from $6\sqrt2-8$ |
|---:|---:|---:|
| $10^4$ | 0.435660036 | −0.049621338 |
| $10^8$ | 0.482805749 | −0.002475625 |
| $10^{12}$ | 0.485072593 | −0.000208782 |

## The sign question after normalization

Write $c=6\sqrt2-8\approx0.485281374$. The combined Lean theorem gives

$$
\frac{D(y)}{\sqrt y} = c+\frac{\Re S_Y(y)}{\sqrt y}+o(1)
\qquad(Y\le y\le 2Y),
$$

with a uniform error and a fixed cutoff $Y$ on the doubling. Thus, for any fixed $\eta>0$, a lower bound $\Re S_Y(y)/\sqrt y\ge -c+\eta$ at every position of a sufficiently late doubling implies $D(y)/\sqrt y>\eta/2$ throughout it.

For longer windows one can also specialize the estimate at $Y=y$. The cutoff then moves with the position. For fixed $\delta,\eta>0$, suppose arbitrarily large $X$ satisfy $\Re S_y(y)/\sqrt y\ge -c+\eta$ at every $y=x/4$ with $X\le x\le X^{1+\delta}$. Lean proves that arbitrarily late such intervals have $D(x/4)>0$ throughout. This is a sufficient condition for the sign hypothesis in Lee Crossley’s ordinary-prime criterion. Establishing the recurring spectral bound independently of RH is the open step in this argument. [Constant-bias formula, real-part bounds and power-window implication](BiasFormula.lean) · [Crossley’s stated criterion](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/PrimeWindow.lean#L194-L198)

The same moving sum gives a test at squares. Put $y=k^2/4$. The prime-power deficit at $x=k^2$ differs from $\Re S_y(y)$ by $O(\log^2 k)$. Crossley’s square-block criterion therefore makes RH equivalent to the existence of one $C>0$ such that $\Re S_y(y)\ge -Ck$ for every integer $K\le k\le K^2$ on arbitrarily late blocks. [The Crossley Criteria, Theorem 4.1](https://doi.org/10.5281/zenodo.24466908).

## Reproduce the check

From this directory, with Elan, Git, Python 3, and network access, run

```sh
lake update
lake exe cache get
lake env python3 verify.py --square-bias
```

The [verifier](verify.py) fetches Pi’s source at commit `25bc57f3919f3578d396b71f8bc2cf9b3675ac63` and checks SHA-256 `28fab02c68c3a5a4d596e72f68caa532d14ddf8c70a5a2abfe5c4e821bf76e68`. An existing download can be supplied with `--source /path/to/Solution.lean`. It compiles that source unchanged together with the downstream modules on Lean 4.34.1 with Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Running from this directory selects that toolchain. The parent project also checks the adapter as an implication on Lean 4.24.0.

With `--square-bias` the verifier downloads 15 pinned PNT and LeanArchitect source modules, checks each SHA-256, compiles 25 modules, checks 24 named axiom reports and replays all compiled modules with Lean’s native `leanchecker`. Imported Mathlib dependencies come from its build cache. The original seven-module check remains available as `lake env python3 verify.py`. For an offline source check, supply Pi’s file with `--source` and a directory containing the two upstream module trees with `--square-sources`. [Source revisions, build order and hashes](square-sources.json) Two changes to a temporary copy of the adapter test the correspondence. Lean rejected including zeros exactly at the cutoff and assigning each zero a single copy regardless of analytic order.

Run `python3 check_discrete.py` for an independent arithmetic check. It integrates the step function exactly on each piece and compares rational coefficients of each $\log p$ against the direct tent sum, at the 257 scales $y=i/4$ for $1\le i\le257$. [Finite check](check_discrete.py)

## The next mathematical question

The square-bias limit is now checked. Obtaining the lower bound on the signed zero sum across arbitrarily late intervals remains the next analytic target. [Ordinary-prime derivation](../../notes/core3-window-roadmap.md) · [The remaining sign estimate](../../notes/critical-line-budget.md)

Pi authored the standalone Core 3 proof. Osgood001 staged the cited source in the project based on Levent Alpöge’s formalization. LadyElinor directed this investigation, with OpenAI Codex and ChatGPT assisting on the downstream work. The earlier dyadic setup is due to bramble_trace and the three-scale criterion to Lee Crossley. Lean and Mathlib supply the kernel and mathematical library. Mathlib credits Alastair Irving, Terry Tao and Ruben Van de Velde for the Chebyshev module. [Pi’s source](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Staging and verification history](https://github.com/Osgood001/riemann-hypothesis/pull/4) · [Mathlib’s Chebyshev functions](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Chebyshev.lean#L73-L85) · [Project credits](../../CREDITS.md)

Xavier Roblot authored Mathlib’s Abel summation module. Bhavik Mehta authored the von Mangoldt module. The higher-power proof uses the Costa Pereira inequalities and Chebyshev bounds formalized in the Chebyshev module cited above. [Abel summation](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/AbelSummation.lean#L129-L136) · [von Mangoldt weights](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean#L73-L99) · [Costa Pereira inequalities](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/NumberTheory/Chebyshev.lean#L584-L604)
