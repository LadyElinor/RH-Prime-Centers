# From Core 3 to a full prime-window doubling

**Research checkpoint, 22 November 2026.** For the ordinary-prime tent deficit
$D(y)=2y\log 2-P(y)$, the target is an arbitrarily large $Y$ with $D(y)\ge0$ for every real $y\in[Y,2Y]$, by an argument independent of RH. The existing written proof reaches $[Y,Y+Y^\alpha]$ for every fixed $0<\alpha<1$. This note derives a sufficient spectral inequality for the next step and runs two finite tests. It makes no priority claim. [Existing proof and tent definition](https://four-primes.owonm.chatgpt.site/successive-scales)

## 1. The upstream explicit formula

Pi’s staged submission 97759 ends with the theorem `AlpogeRHCore3.explicitFormula` and supplies the witness $C=10102292$. For primitive Dirichlet characters of conductor $N$ and $2\le T\le u$, it bounds the difference between a prime-power sum, its main term, and a sum over zeros counted with multiplicity. It explicitly includes a low-zero term and uses the strict cutoff $|\Im\rho|<T$. The project reports Lean and Comparator verification of the standalone submission. The draft reports 21,025 normalized tokens against 129,270 and lists a separate port and rebuild as pending. The [conductor-one verification](../formal/core3/README.md) recompiles the staged proof and replays it with the downstream tent application. [Pi’s pinned declaration, staged by Osgood001](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Draft PR and verification report](https://github.com/Osgood001/riemann-hypothesis/pull/4)

## 2. Carry the error through one doubling

Specialize to the trivial character of conductor one. Write $\psi(u)=\sum_{n\le u}\Lambda(n)$. For $Y\ge2$, fix **one cutoff** $T=Y$ for the entire interval. Throughout $Y\le u\le8Y$, the theorem gives

$$\psi(u)-u=-\sum_{|\Im\rho|<Y}\frac{u^\rho}{\rho}+O(\log^2(2Y)).$$

The conductor-one low-zero term is a fixed finite constant. In the main error term $u/T\le8$, and $\log(uT)\le\log(8Y^2)$. All zero sums here include both signs and multiplicity.

Define $G_f(y)=y\int_y^{2y}(f(t)-t)t^{-2}\,dt$. For $f=\psi$, twice the difference $G_f(y)-G_f(2y)$ is the deficit with all prime powers included. This follows by integrating each point mass over the same tent as in the ordinary-prime identity. If the error in $f(t)-t$ is bounded by $M$, the error in each $G_f$ is at most $M/2$ and the error in twice their difference is at most $2M$. The range up to $8Y$ covers every needed argument when $Y\le y\le2Y$.

The [Lean transfer theorem and replay](../formal/README.md#uniform-error-and-the-signed-zero-sum) now verify the sharp factor 2, the signed coefficient for finite families with repeated zeros, and the uniform limit for changing cutoffs. The [conductor-one application](../formal/core3/PinnedFormula.lean) supplies the pointwise arithmetic bound from Pi’s theorem.

Integrating a term $-t^\rho/\rho$ gives $-y^\rho(2^{\rho-1}-1)/(\rho(\rho-1))$ in $G_f(y)$. Subtract the value at $2y$ and double. The coefficient in the deficit is

$$H(\rho)=\frac{(2^\rho-1)(2^\rho-2)}{\rho(\rho-1)}.$$

Returning to ordinary primes **adds** the missing prime powers. Prime squares contribute $(c+o(1))\sqrt y$ with $c=6\sqrt2-8$ by the prime number theorem applied to the tent. Powers with exponent at least three contribute $O(y^{1/3}\log^2(2y))$ by counting bases and exponents. These estimates are uniform for $y\in[Y,2Y]$ as $Y\to\infty$. Hence

$$\frac{D(y)}{\sqrt y}=c+\sum_{|\Im\rho|<Y} H(\rho)y^{\rho-1/2}+o(1)$$

uniformly over the doubling. Conjugation makes the sum real. The normalized truncation error is $O(\log^2(2Y)/\sqrt Y)$; the other errors include the prime-square asymptotic. [bramble_trace’s dyadic work](https://rstation.ai/r/riemann_hypothesis/posts/100) · [Prime-square derivation](https://four-primes.owonm.chatgpt.site/short-intervals#margin) · [Lee Crossley’s related zero-sum and square-bias method](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md)

## 3. Isolate the zeros that could exhaust the margin — completed analytically

On the critical line $|y^{\rho-1/2}|=1$ and $|\rho(\rho-1)|=|\rho|^2$. The Hadamard sum over **all** nontrivial zeros is $2\sum_\rho\Re(1/\rho)=2+\gamma_E-\log(4\pi)$. Every summand is positive and for critical-line zeros $2\Re(1/\rho)=1/|\rho|^2$. The absolute contribution of any subset of critical-line zeros is consequently at most

$$B=(1+\sqrt2)(2+\sqrt2)(2+\gamma_E-\log(4\pi))\approx0.380739261.$$

This subset bound needs no assumption about the location of the other zeros. [Noam Elkies, completed zeta product and zero sum](https://people.math.harvard.edu/~elkies/M229.09/zeta2.pdf)

Zeros strictly to the left of the line contribute $o(1)$ uniformly after normalization. Indeed, $\sum_\rho |H(\rho)|<\infty$ by $H(\rho)=O((1+|\Im\rho|)^{-2})$ and the classical zero count $N(t)=O(t\log(2t))$. For each left-hand zero, $\sup_{Y\le y\le2Y}|y^{\rho-1/2}|=Y^{\Re\rho-1/2}\to0$. Dominated convergence also permits the moving cutoff. [Andreas Strömbergsson, analytic number theory lecture notes, chapters on zeta zeros and the explicit formula](https://www2.math.uu.se/~ast10761/analtalt08/www_notes.pdf)

Let $R_Y(y)$ denote the same normalized sum restricted to $\Re\rho>1/2$, $|\Im\rho|<Y$. The result is a **sufficient condition**: for some fixed $\epsilon>0$ and arbitrarily large $Y$, show

$$\inf_{Y\le y\le2Y} R_Y(y)\ \ge\ -(c-B)+\epsilon,\qquad c-B\approx0.104542113.$$

Then $D(y)>0$ throughout all sufficiently large such intervals. This loses information by taking absolute values on the critical line. Assuming RH makes $R_Y$ empty and recovers eventual positivity; that route does not prove recurrence independently of RH. The theorem used for compression bounds the truncation error, while this remaining condition concerns the signed zero sum itself.

## 4. Finite checks — executed

Run `python notes/check_core3_window.py` from the repository root with Python 3 and mpmath 1.3.0. A direct prime sum and a finite zero sum are evaluated on 65 equally spaced logarithmic positions per doubling. The residual subtracts **all** prime powers of exponent at least two from the ordinary deficit before comparing it with the spectrum. The code independently integrates the tent for its first three Mellin coefficients.

| Starting scale | Positive zero ordinates used | Smallest sampled ordinary deficit / √y | Largest sampled absolute residual / √y | Certified lower bound for raw D on the entire doubling |
|---:|---:|---:|---:|---:|
| 32 | 4 | 0.453815136 | 0.025811851 (rounded up) | 2.613 |
| 64 | 14 | 0.571106459 | 0.015295101 (rounded up) | 5.880 |
| 128 | 42 | 0.550133624 | 0.004264574 (rounded up) | 6.574 |

The last column uses a different calculation. For $x=4y$ the deficit is affine between $x=p,2p,4p$. The checker evaluates both endpoints and every corner with exact rational weights and outward bounds around correctly rounded decimal logarithms. The three runs used 45, 81 and 143 distinct positions. Thus their bounds cover every real position. The zero calculations use floating point and mpmath’s enumerated zeros. They test normalization and sign; the three residuals give no asymptotic rate. The repository's earlier broad-range certificate already covers much larger scales. [Finite certificate](../extension/certificate.csv)

## 5. Next milestones and decision rules

**Follow-up completed.** The [critical-line budget and interval certificate](critical-line-budget.md) certifies the finite spectra, improves the available margin to at least 0.211697, and derives the fixed-ratio conclusions when a rightmost real part is attained.

The [Lean certificate and replay](../formal/README.md) now check the curvature-based grid-to-interval step for the three finite spectra, conditional on the numerical inputs certified by FLINT. The new transfer proof accepts the pointwise explicit formula and proves the smoothed formula on the entire doubling. The conductor-one specialization now supplies the pointwise hypothesis for the prime-power sum.

1. **Continuum test for a proposed spectral bound.** The script implements a grid-to-interval estimate for the finite normalized spectrum. In $v=\log(y/Y)$, the derivative has absolute value at most the sum of $|H(\rho)(\rho-1/2)|\max(Y^{\Re\rho-1/2},(2Y)^{\Re\rho-1/2})$. Subtract this times half the grid spacing from the sampled minimum. A certified *spectral* computation would additionally need verified zero enclosures, completeness up to the cutoff, and outward arithmetic. The raw-deficit certificates above bypass those dependencies.
2. **Analytic bottleneck.** Seek a uniform lower bound for $R_Y$ along an unbounded sequence without importing RH. A result about its value at a single starting point or its average over the interval is insufficient. An alternative is to exploit cancellation jointly with the critical-line part and improve the sufficient condition. The numerical diagnostics do not settle either route.
3. **Formalization order.** The finite tent integral and uniform truncation remainder are checked. The conductor-one character, strict cutoff, analytic-order multiplicities and Chebyshev sum are connected in Lean. The [discrete identity](../formal/core3/DiscreteTent.lean), [cube-root higher-power bound](../formal/core3/HigherPowers.lean) and [ordinary-prime formula retaining exact squares](../formal/core3/OrdinaryFormula.lean) are now checked. The [prime-square limit](../formal/core3/SquareBias.lean) now supplies the coefficient from the ordinary prime number theorem. The [signed formula and power-window implication](../formal/core3/BiasFormula.lean) identify the remaining sufficient lower bound when the cutoff moves with the scale. The critical-line budget remains a written bound with checked numerical inputs.
4. **Power windows.** A full doubling is an intermediate target. Crossley’s RH implication requires a fixed $\delta>0$ and arbitrarily late $[X,X^{1+\delta}]$, spanning $\delta\log_2 X$ doublings. Passing the one-doubling test alone cannot supply the extra quantifiers. [Crossley’s Lean theorem](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/PrimeWindow.lean#L194-L198)

LadyElinor directed the prime-window investigation. OpenAI assisted with this roadmap, derivation and diagnostic. Credit for the standalone Core 3 submission belongs to Pi; the underlying RH library is Levent Alpöge’s. [Project contributors](../CREDITS.md)
