# A sharper zero budget and the length of a positive window

For the ordinary-prime tent, let $D(y)=2y\log 2-P(y)$. We seek a proof from the primes that $D(y)\ge0$ throughout $[Y,2Y]$ for arbitrarily large $Y$. The [Core 3 derivation](core3-window-roadmap.md) reduced that question to a signed sum over zeta zeros. Here we tighten its numerical threshold, certify three finite spectra and examine what the rightmost zeros could do. The analytic arguments are written proofs. The computations use FLINT ball arithmetic.

## An unconditional margin of at least 0.211697

Recall the square bias $c=6\sqrt2-8$ and the tent coefficient

$$H(s)=\frac{(2^s-1)(2^s-2)}{s(s-1)}.$$

Write $K=2+\gamma_E-\log(4\pi)=2\sum_\rho\Re(1/\rho)$, summing both signs with multiplicity. The identity follows from the completed zeta product. Every term on the right is positive. For a critical-line zero $\rho=1/2+ig$, its term $2\Re(1/\rho)$ equals $1/|\rho|^2$. Also $|H(\rho)|\le A/|\rho|^2$ there, for $A=(1+\sqrt2)(2+\sqrt2)$. [Elkies, product formula for zeta](https://people.math.harvard.edu/~elkies/M229.09/zeta2.pdf)

Let $S$ contain both members of each of the first $n$ certified conjugate pairs, all simple and on the line. Pay their actual absolute contributions. The remaining critical-line zeros can use at most the unused part of $K$. Thus their **combined** bound, including $S$, is

$$B_S=\sum_{\rho\in S}|H(\rho)|+A\left(K-\sum_{\rho\in S}\frac{1}{|\rho|^2}\right).$$

This bounds the absolute sum for all critical-line zeros and therefore for any height cutoff. It continues to hold if some zeros outside $S$ lie off the line. Crossley’s companion proof studies the absolute zero mass for this family of weights under RH; the calculation here bounds the critical-line subset while allowing the remaining zeros to have unknown real parts. [Crossley, zero mass for the all-widths tent](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md#L12-L52)

| Positive ordinates evaluated | Upper bound for critical-line contribution | Lower bound for remaining margin |
|---:|---:|---:|
| 0 | 0.380740 | 0.104542 |
| 42 | 0.300083 | 0.185198 |
| 512 | 0.273584 | 0.211697 |

As in the roadmap, $R_Y(y)$ sums $H(\rho)y^{\rho-1/2}$ over $\Re\rho>1/2$ and $|\Im\rho|<Y$. Left-of-line terms are uniformly $o(1)$ after normalization. An actionable sufficient estimate now is

$$R_Y(y)\ge-0.21\quad\text{for every }y\in[Y,2Y],\quad\text{for arbitrarily large }Y.$$

Indeed, the certified remaining margin exceeds 0.21 by at least 0.001697, enough to absorb the uniform $o(1)$. This estimate on $R_Y$ is the outstanding hypothesis.

## Certified finite spectra over continuous intervals

For the three cutoffs below, the enumerated zeros exhaust the truncated sum. The checker obtains rigorously isolated, consecutive critical-line ordinates from FLINT. It checks a total zero count and brackets each cutoff between consecutive ordinates. It then bounds the **minimum** of the finite, normalized zero sum on the entire log interval. These numbers exclude the square bias and the truncation remainder. [FLINT, rigorous zero isolation and indexing](https://flintlib.org/doc/acb_dirichlet/index.html) · [Python interface](https://python-flint.readthedocs.io/en/stable/acb.html)

| $Y=T$ | Positive ordinates below $T$ | Enclosure for the spectral minimum on $[Y,2Y]$ |
|---:|---:|---:|
| 32 | 4 | [−0.129553, −0.129507] |
| 64 | 14 | [−0.075334, −0.075190] |
| 128 | 42 | [−0.086603, −0.086210] |

For $v=\log(y/Y)$ the function is $q(v)=2\Re\sum_{g>0}H(1/2+ig)e^{ig(\log Y+v)}$. On 256 equal cells of width $h=(\log2)/256$, the linear interpolation error is bounded by $h^2\sup|q''|/8$, with $\sup|q''|\le2\sum g^2|H(1/2+ig)|$. The lowest nodal value therefore bounds the true minimum above, and subtracting the interpolation error bounds it below. All node values, derivatives and constants used in the enclosure have outward rounding.

To reproduce, install the pinned binary package and run the [spectral checker](certify_core3_spectrum.py). The default precision is 144 bits. The printed bounds also reproduce at 224 bits.

```sh
python -m pip install python-flint==0.9.0
python notes/certify_core3_spectrum.py
```

The earlier [independent prime-side checker](check_core3_window.py) bounds the raw deficit itself on the same intervals.

## What if the rightmost real part is attained?

The following analysis is hypothetical. It makes no assertion that an off-line zero exists. Let $\beta>1/2$ be the largest real part of a nontrivial zero **and suppose it is attained**. Write

$$F(u)=\sum_{\Re\rho=\beta} H(\rho)e^{i(\Im\rho)u}.$$

Count multiplicity. This is a real uniformly convergent series because $\sum_\rho|H(\rho)|<\infty$; the latter follows from quadratic decay in height and the classical zero count. The roadmap’s uniform formula gives

$$D(y)/y^\beta=F(\log y)+o(1)\quad(y\to\infty).$$

To check the passage to this formula, take the roadmap cutoff $Y=y$. The square bias and its normalized error vanish after scaling by $y^\beta$. Each zero with real part below $\beta$ contributes a factor $y^{\Re\rho-\beta}\to0$, bounded by 1. Absolute summability gives dominated convergence, even if zeros approach the rightmost line arbitrarily closely. The omitted tail of the rightmost-line series tends uniformly to zero. The resulting one-variable asymptotic holds throughout any sufficiently late interval.

**Consequence 1. Some fixed positive relative length recurs under the attainment hypothesis.** The mean of $F$ over $[0,U]$ tends to zero because every frequency is nonzero. Pick one frequency with combined coefficient $a$. Its coefficient is nonzero because the tent transform has no zeros in the open strip and multiplicities add. Averaging $F(u)e^{-i g u}$ recovers $a$ by uniform convergence. Cauchy–Schwarz then gives a limiting lower bound $|a|^2$ for the mean of $|F|^2$. If $M=\sum_{\Re\rho=\beta}|H(\rho)|$, the inequality $|F|^2\le M|F|$ and the zero mean imply that the mean of $\max(F,0)$ has liminf at least $|a|^2/(2M)$. Thus some fixed positive height is exceeded arbitrarily far out. Uniform continuity gives a fixed $h>0$ on which each such peak stays positive with a uniform margin (reduce the height by half). Transfer through the preceding asymptotic with $Y=e^u$. There are arbitrarily large $Y$ with $D>0$ throughout $[Y,e^hY]$. The proof gives no guarantee that $h\ge\log2$. If the supremum exceeds one half and is never attained, this argument supplies no leading series $F$.

**Consequence 2. A single rightmost conjugate pair has a sharp interval-length threshold.** Suppose the only distinct zeros on $\Re\rho=\beta$ are $\beta\pm ig$, each of multiplicity $m$. Then

$$F(u)=2m|H(\beta+ig)|\cos(gu+\arg H(\beta+ig)).$$

For every fixed $0<L<\pi/g$, infinitely many log intervals of length $L$ fit strictly inside positive cosine arcs with a fixed margin. For every $L>\pi/g$, every such interval contains a cosine value bounded below zero by a fixed amount: the largest possible minimum over starting phases is strictly negative by continuity and compactness. The $o(1)$ error preserves these strict conclusions for late intervals. In ordinary coordinates the multiplier threshold is $e^{\pi/g}$. No endpoint conclusion follows from this comparison when $L=\pi/g$.

The certified first positive ordinate exceeds 14, so $\pi/g<\log2$ for any hypothetical off-line pair. In this particular rightmost-zero configuration **every sufficiently late doubling contains a point with negative deficit**. This explains why a general recurrence proof cannot simply let a single largest oscillation supply the starting margin. Configurations with multiple rightmost pairs, or with an unattained supremum, require separate analysis for a full doubling.

## Research decision

Finite spectral certification is complete for these three windows. Increasing the prefix can improve the numerical margin, but the sign of $R_Y$ throughout an arbitrarily late doubling remains the decisive estimate. A direct argument must either rule out the single-rightmost-pair configuration from independent information about primes or derive recurrence in a way that itself excludes it. The weaker fixed-ratio result under attainment identifies one intermediate conclusion available from the present method.

LadyElinor directed this project; OpenAI assisted with the derivation, implementation and interval checks. Sources for the explicit formula (Pi’s Core 3 submission), earlier dyadic work (bramble_trace), the prime-window criterion (Lee Crossley), and the prime-square asymptotic are given in the [roadmap](core3-window-roadmap.md).
