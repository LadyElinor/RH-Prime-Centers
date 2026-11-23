# RH Prime Centers

How close does a weighted sum of ordinary primes come to its main term? This repository contains the finite certificates, reproduction code, and research notes for the [Four Primes prime-window study](https://four-primes.owonm.chatgpt.site/prime-windows).

For every real scale in the certified range, the prime sum stays below its main term by at least a square-root-sized margin:

$$
D(y)=2y\log 2-P(y)>0.37468738\sqrt y
\qquad (64\le y\le114{,}791{,}256).
$$

The unique minimum of $D(y)/\sqrt y$ on this interval occurs at $y=159{,}693.5$ and is approximately $0.37468738359$. The certificate uses $x=4y$, so its full-range row runs from 256 through 459,165,024 and locates this minimum at $x=638{,}774$. The result is unconditional throughout that finite interval.

## Contributors and sources

LadyElinor directed the study. OpenAI Codex and ChatGPT assisted with the code, calculations and writing. In revision 24, bramble_trace gave the every-prime criterion, the concavity reduction and an earlier finite certificate. Lee Crossley suggested the three-scale filter and formalized the real-window implication. Our finite certificate gives the unique minimum of the normalized deficit on the interval above. [bramble_trace, revision 24](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) · [Crossley, v1.1.1](https://doi.org/10.5281/zenodo.24421600) · [Contributors and sources](CREDITS.md) · [Cite this software](CITATION.cff)

## What the verifier measures

For $y<p<4y$, the sum $P(y)$ weights each ordinary prime by its natural logarithm times $W(p/y)$. The weight rises to one at $p=2y$ and returns to zero at $p=4y$.

$$
W(t)=\begin{cases}
2(1-1/t) & 1<t\le 2,\\
4/t-1 & 2<t<4,\\
0 & \text{otherwise}.
\end{cases}
$$

The raw deficit $D(x/4)$ is concave between consecutive prime centers $x=2p$. Its minimum on a closed interval occurs among the centers and endpoints. Dividing by $\sqrt{x/4}$ can introduce an interior minimum. The extended verifier checks that possibility on every affine piece. Across the full range it checked 12,620,803 centers and endpoints and 43,494,876 pieces. The complete interval includes the gaps between the individual windows.

## Reproduce the certificates

Run these commands from the repository root. The full certificate requires 64-bit Linux, Python 3.10 or later, a C++17-capable g++ with 128-bit integer support, and GMP development headers and libraries.

```sh
python3 extension/run.py --check extension/certificate.csv
```

The command builds the verifier in a temporary directory, exercises a case with a known interior minimum, and checks the complete regenerated CSV against the recorded file. The CSV stores integer bounds. The [implementation notes](extension/README.md) explain the denominators and the independent floating-point scan used to find candidate minima.

The initial four-window check uses only the Python standard library. It recomputes the raw minima by two methods and compares the result with the recorded JSON.

```sh
python3 initial/verify.py --check initial/certificate.json
```

| Material | Contents |
| --- | --- |
| [Where to check a prime window (PDF)](notes/Prime_Window_Note.pdf) | The prime-center argument, the proof that ties are impossible at prime centers, and the initial windows. |
| [How close does the prime sum get? (PDF)](notes/Prime_Window_Extension.pdf) | The continuous finite bound, the raw and scaled minima, and how the extension was checked. |
| [Full certificate (CSV)](extension/certificate.csv) | Exact bounds and minimizers for the full interval and five subintervals. |
| [Initial certificate (JSON)](initial/certificate.json) | Enclosures from two independent calculations on the smaller windows. |

## One full doubling

The [Core 3 roadmap and derivation](notes/core3-window-roadmap.md) applies the truncated explicit formula to a full doubling, bounds the contribution of critical-line zeros, and identifies the remaining signed estimate. The [reproducible diagnostic](notes/check_core3_window.py) compares finite zero sums with direct prime counts and certifies three finite windows.

The [critical-line budget and certified spectra](notes/critical-line-budget.md) sharpen the available margin to at least 0.211697 and explain the limiting interval length in a hypothetical single-rightmost-pair case.

The [Lean interval certificate](formal/README.md) proves how the finite grid checks extend to every real position on each of the three spectral test windows. It includes a kernel replay and the exact rational inputs from FLINT.

The [Lean proof of uniform smoothing](formal/README.md#uniform-error-and-the-signed-zero-sum) integrates each signed zero term and proves that a Core 3 pointwise truncation error contributes $o(\sqrt y)$ uniformly for every $y\in[Y,2Y]$. The [conductor-one proof](formal/core3/README.md) supplies that hypothesis from Pi’s truncated explicit formula and obtains the uniform result for Mathlib’s Chebyshev prime-power sum. The [discrete formula](formal/core3/OrdinaryFormula.lean) gives the ordinary-prime deficit uniformly to error $o(\sqrt y)$ after retaining the zero sum and the actual prime squares. Higher powers contribute $O(y^{1/3})$. Lean also checks the [prime-square coefficient and signed zero-sum bound](formal/core3/README.md#the-sign-question-after-normalization). Removing the squares contributes $(6\sqrt2-8)\sqrt y+o(\sqrt y)$. A direct proof still has to control the signed zero sum throughout arbitrarily late windows.

## Relation to the Riemann hypothesis

The upstream Lean theorem says that RH follows if, for one fixed $\delta>0$, arbitrarily large $X$ satisfy $D(x/4)\ge0$ for every real $x$ in $[X,X^{1+\delta}]$. The first note gives a written deduction showing how a hypothesis at prime centers on arbitrarily late windows suffices. A direct proof of recurrence from these prime sums would give another route to RH. Our computations establish finite instances. The [Lean and Mathlib statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) covers the separate proof by Levent Alpöge. [Formal theorem in Lee Crossley’s repository](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/PrimeWindow.lean#L194-L198) · [Upstream pole-preservation proof](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/DelayedPole.lean#L113-L174) · [Companion all-scales argument](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md)
