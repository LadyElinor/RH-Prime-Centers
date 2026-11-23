# Signed slope changes between fourth powers

For the ordinary-prime tent write $F(x)=(x/2)\log 2-P(x/4)$. This is the room below the ceiling at position $x$. At position $x$, the weight of a prime $p$ is $w_p(x)=\max(0,\min(x/p-1,2-x/(2p)))$. Write $L_{A,H}$ for the straight line through the values of $F$ at $A$ and $A+H$.

**Interpolation theorem (unconditional, written proof).** Fix $B\ge0$. As $A\to\infty$,

$$
\sup_{0<H\le A^{3/4}(\log A)^B}\ \sup_{A\le x\le A+H}
\frac{|F(x)-L_{A,H}(x)|}{\sqrt A}\longrightarrow 0.
$$

In particular, on every sufficiently late cell $[k^4,(k+1)^4]$ the worst departure is $o(k^2)$, including at doubled primes. Each cell uses its own actual endpoint values. Therefore errors from different cells do not add when bounding the minimum on their union.

## Proof

The contribution of $-w_p(x)\log p$ to the slope of $F$ changes at $dp$, for $d=1,2,4$, by $c_d\log(p)/p$, where $(c_1,c_2,c_4)=(-1,3/2,-1/2)$. This follows by differentiating the two affine pieces. If events coincide, add their changes. Use right derivatives so the jump at $A$ is excluded.

Put $V=A^{3/4}(\log A)^B$. For each of the three dilations, uniformly in $0\le u\le V$ and for any fixed $m>0$, we have

$$
E_d(u)=\sum_{A<dp\le A+u}\log p-u/d
=O_{B,m}(V/(\log A)^m).
$$

For $u<A^{2/3}$, counting integers bounds the error by $O((1+A^{2/3})\log A)$, which suffices. For larger $u$, apply Guth and Maynard's Corollary 1.3 at $z=A/d$ with length $h=u/d$. For large $A$ these lengths lie between $z^{17/30+1/20}$ and $z^{0.99}$. Their error in the prime count is $O(h\exp(- (\log z)^{1/4}))$. Weighting by $\log z$ gives the main term $h$. Replacing $\log z$ by $\log p$ costs $O((h+1)h/z)$ since $p\in(z,z+h]$. Both errors are $O_{B,m}(V/(\log A)^m)$. [Larry Guth and James Maynard, *New large value estimates for Dirichlet polynomials*, Corollary 1.3](https://arxiv.org/html/2405.20552v2) · [Published paper](https://doi.org/10.4007/annals.2026.203.2.6)

Partial summation with the weight $d/(A+v)$ now gives

$$
\sum_{A<dp\le A+u}\frac{\log p}{p}
=\log(1+u/A)+O_{B,m}\!\left(\frac{V}{A(\log A)^m}\right).
$$

Indeed the error is $dE_d(u)/(A+u)+d\int_0^u E_d(v)/(A+v)^2\,dv$. The main term is identical at all three dilations. It cancels because $-1+3/2-1/2=0$. Thus $F'_+(A+u)-F'_+(A)$ is uniformly $O_{B,m}(V/(A(\log A)^m))$.

On a cell of length $H\le V$ the chord slope is the mean slope. The difference between any slope and that mean is at most twice the preceding bound. Integrating gives $|F-L_{A,H}|\ll_{B,m} V^2/(A(\log A)^m)=\sqrt A\,(\log A)^{2B-m}$ up to a constant. Take $m>2B$. For consecutive fourth powers, $H\sim4A^{3/4}$, so $B=1$ suffices.

## What remains at the sample points

If some fixed $\eta>0$ satisfies $F(k^4)\ge\eta k^2$ for every $K\le k\le K^2$ on arbitrarily late integer blocks, the interpolation theorem gives $F(x)>0$ for every real $x\in[K^4,K^8]$ on those blocks once $K$ is large. The endpoints of each cell then both have margin at least $\eta k^2$. In the notation of Crossley's ordinary-prime criterion this is $X=K^4$ and $\delta=1$. [Lee Crossley, Theorems 3.2 and 3.4](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/main/paper/crossley-criteria-riemann-hypothesis.md#3-prime-windows)

Even the weaker sample condition $F(k^4)\ge-Ck^2$ on arbitrarily late such blocks, with one fixed $C\ge0$, implies RH via Crossley's **prime-power** square-block criterion. Interpolation gives $F(x)\ge-C'\sqrt x$ throughout the corresponding real blocks since $(k+1)^2/k^2\to1$. Adding prime powers to the tent sum costs at most $\psi(x)-\vartheta(x)=O(\sqrt x)$: the squares cost $O(\sqrt x)$ by Chebyshev, and higher powers cost $O(x^{1/3}\log x)$. Crossley's prime-power deficit therefore obeys the same type of lower bound, in particular at $x=j^2$ for $K^2\le j\le K^4$. His Theorem 4.1 applies with block parameter $K^2$. Conversely his Remark 3.3 gives eventual positivity of the ordinary-prime deficit under RH, which implies the weak sample condition with $C=0$. This use of fourth powers samples the ordinary-prime tent directly. Crossley's Theorem 6.1 studies weighted shortfalls of a different arithmetic sum. [Square-block criterion](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/main/paper/crossley-criteria-riemann-hypothesis.md#4-square-blocks) · [Crossley's fourth-power criterion](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/main/paper/crossley-criteria-riemann-hypothesis.md#6-fourth-powers)

The interpolation theorem controls changes in slope. An affine function added on a cell changes its two endpoint values and leaves its departure from the chord identical. The bound alone therefore gives no one-sided estimate for the anchors. A direct arithmetic proof of the recurring sample bound remains open in this approach.

## Finite check

On $[6^4,6^8]=[1296,1679616]$, outward bounds give $F(k^4)\ge0.2174 k^2$ at all 31 anchors and $|F(x)-L(x)|\le0.1016 k^2$ on all 30 cells. Hence $F(x)\ge0.1158k^2$ everywhere in its cell. Run `python notes/check_quartic_chords.py` to reproduce the check. The standard-library script encloses each prime's logarithm, rounds its slope coefficient to an integer on a common scale, sweeps all 228,620 distinct vertices and anchors, and allows for rounding at both the vertex and its chord. Piecewise linearity covers every real point between vertices. This is one finite block. [Certificate script](check_quartic_chords.py)

LadyElinor directed the investigation, with OpenAI Codex and ChatGPT assisting on the derivation. Lee Crossley's doubled-prime checkpoint question motivated this calculation. His paper credits bramble_trace for earlier prime-centre and square-sampling observations. Guth and Maynard supply the short-interval estimate. The interpolation argument here is a written derivation without a Lean formalization.
