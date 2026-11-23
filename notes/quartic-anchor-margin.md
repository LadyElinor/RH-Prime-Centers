# A uniform margin at fourth powers

For the ordinary-prime deficit $F(x)=(x/2)\log 2-P(x/4)$, one can take **$\eta=1/10$ at every integer fourth power**. This derivation uses RH through Lee Crossley's bound for the signed contribution of the zeta zeros. The Lean FRO and Mathlib Initiative reported independent verification of Levent Alpöge's proof of RH. We use their reported theorem here. We have not replayed that archive or formalized this deduction. A direct proof of the anchor inequality from the arithmetic of primes remains open in our approach. [Verification statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Andrew Sutherland's verification record](https://math.mit.edu/~drew/grh/)

## An unconditional estimate for the squares

Let $y=k^4/4$, $u=\sqrt y=k^2/2$ and $Q_2(y)=\sum_p\log(p)W(p^2/y)$. We prove

$$Q_2(k^4/4)>0.2338\,k^2\qquad(k\ge23).$$

At $k\ge3000$, the prime bases run from $u$ to $2u$, with $u\ge4{,}500{,}000$. The tent as a function of the prime base rises from zero to one and returns to zero, so its total variation is two. Integrating against $d\vartheta(t)$ and then replacing it by $dt$ costs at most $2\sup_{u\le t\le 2u}|\vartheta(t)-t|$ by integration by parts. Dusart's unconditional estimate $|\vartheta(t)-t|<0.2t/\log^2t$ applies above $3{,}594{,}641$. The replacement therefore costs at most $0.4k^2/\log^2 u$. The integral against $dt$ is $(6\sqrt2-8)u$, as follows by integrating $2(1-v^{-2})$ on $[1,\sqrt2]$ and $4v^{-2}-1$ on $[\sqrt2,2]$, with $v=t/u$. Hence $Q_2/k^2\ge3\sqrt2-4-0.4/\log^2 u>0.2409$. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442#page=4) · [Prime-square integral](../formal/core3/SquareKernel.lean)

For $23\le k<3000$ the minimum certified lower enclosure for $Q_2/k^2$ exceeds $0.233865$ (at $k=23$). A separate direct calculation for $1\le k\le22$ gives $F(k^4)/k^2>0.217468$ throughout that finite range. The standard-library script encloses each correctly rounded logarithm between its adjacent decimal values, then sweeps sieve primes with two integer prefix sums. For $n=p$ or $p^2$ it rounds $10^{25}\log(p)/(2n)$ down to an integer tick. On the two branches the tick multipliers are $4n-x$ and $2x-2n$, both nonnegative and at most $2n$. Thus the sum rounded downward is a lower bound, and adding $2x^2$ ticks bounds the total rounding loss. [Run the arithmetic certificate](check_quartic_anchors.py)

## Where RH enters

Crossley's explicit formula at width two gives the lower bound $F(4y)\ge Q_2(y)-L_2\sqrt y$ for $y>1$ under RH. Indeed the ordinary-prime deficit equals the sum of the higher-prime-power corrections, the signed nontrivial-zero sum, and a nonnegative trivial-zero correction. The first group contains the square sum and all its other terms are nonnegative. On RH the second group has absolute value at most $L_2\sqrt y$. For the sum of the absolute tent coefficients over the nontrivial zeros, Crossley's width-two identity gives

$$L_2=\sqrt2\,(3\log3-2\log2-\gamma-\log\pi)=0.2653021567\ldots <0.266.$$

Here $\gamma$ is Euler's constant. The coarse upper bound also follows from $\sqrt2<1.415$, $\log3<1.09862$, $\log2>0.69314$, $\gamma>0.5772$ and $\log\pi>1.14469$. Crossley's own paper gives a positive all-scale result and a quantitative large-scale bound. We specialize his estimate to quartic anchors and certify the small and intermediate anchors separately. [Crossley's explicit formula and zero-mass identity](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md#the-zero-mass) · [Crossley's Remark 3.3](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/main/paper/crossley-criteria-riemann-hypothesis.md#3-prime-windows)

Since $\sqrt y=k^2/2$, for $k\ge23$ we get $F(k^4)/k^2>0.2338-0.266/2=0.1008$. The direct finite check handles $1\le k\le22$. Consequently $F(k^4)>k^2/10$ for every integer $k\ge1$. The earlier interpolation theorem carries this margin across every cell of every sufficiently late block $[K^4,K^8]$. The logical direction here is from the external RH theorem to the anchor bound. [Interpolation proof](quartic-chords.md)

## Why the local prime-count estimates alone leave a gap

As a test of the direct proof, keep the actual prime positions and change only their weights beyond a fixed threshold $T$. Multiply $\log p$ by $1+a(p)\cos(\log p)$, where $a(t)=\exp(- (\log t)^{1/3})$. These positive weights agree with any prescribed finite list by taking $T$ sufficiently large. They preserve the uniform short-interval estimates used in the fourth-power interpolation proof: on the ranges $A<dp\le A+V$ there, the change to any prefix sum is $O((V+1)\log A\sup_{A/4\le t\le 2A}a(t))$, smaller than $V/(\log A)^m$ for every fixed $m$. They also preserve the limiting square bias because the relative change on its support tends uniformly to zero.

Yet the modified deficit takes negative values at anchors in every sufficiently late block. For the true weights the classical prime number theorem with exponential error and tent integration by parts give $F(x)=O(x\exp(-c\sqrt{\log x}))=o(xa(x))$ for some $c>0$. On a fixed-width band of phases around $\log x=2\pi j+(\log4)/2$, all $p\in[x/4,x]$ satisfy $\cos(\log p)>1/2$. The added tent sum is then at least $a(x)P(x/4)/2\gg xa(x)$, so the modified deficit is negative there. The log positions $4\log k$ have spacing tending to zero and span $4\log K$ as $k$ goes from $K$ to $K^2$. Every sufficiently late block therefore hits one of these bands. Shifting the phase by $\pi$ gives positive bands as well. [Classical prime number theorem with error term](https://www.math.leidenuniv.nl/~evertsejh/ant18-1.pdf)

This comparison isolates the information lost in the local estimates. The modified weights do not satisfy the exact prime-power identity $\sum_{p^m\mid n}\log p=\log n$ (sum over $m\ge1$). An independent arithmetic proof would have to exploit additional information, for example that identity together with a sufficiently sharp estimate for the resulting signed sum. The modified measure is only a test of the proposed inference.

LadyElinor directed the project. OpenAI Codex and ChatGPT assisted with the anchor calculation and certificate. The underlying prime-window criterion and width-two zero-mass identity are due to Lee Crossley, with earlier prime-centre and prime-square work credited to bramble_trace. The zero-free input and its verification, and Dusart's independent prime-counting input, are credited above.
