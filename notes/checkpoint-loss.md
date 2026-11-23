# How much of the prime-window margin do the downward steps consume?

On the window from $54^4$ to $54^5$, the ordinary-prime margin starts at **766.36653**. Its deepest fall below its starting value is **134.64037**, reached at $x=9{,}372{,}758$. Adding every downward step between checkpoints gives **8,041.49478**. A bound that charges every fall to the initial margin therefore runs out well before the window ends. Five blocks suffice if we evaluate the margin again at four intermediate checkpoints. All three decimal values are rounded from certified enclosures.

## What is measured

Write $F(x)=(x/2)\log 2-P(x/4)$ for the deficit of the ordinary-prime tent sum. Use the two ends of a closed integer block $[a,b]$ and its interior points $2p$ for primes $p$, in increasing order $t_0,\dots,t_n$. At those points set $F_i=F(t_i)$ and $d_i=F_{i-1}-F_i$. Two different amounts of starting margin enter the calculation.

$$
L=\max_{0\le j\le n}\sum_{i=1}^{j} d_i=F_0-\min_j F_j,
\qquad
V=\sum_{i=1}^{n}\max(0,d_i).
$$

The first quantity counts recoveries along the way. The second charges every downward step in full and gives no credit for a rise. Always $L\le V$. Strict positivity on the whole window is equivalent to $L<F_0$ because the deficit is concave between consecutive checkpoints. The stronger inequality $V<F_0$ also suffices. Here $V$ measures movement from one checkpoint to the next. The deficit can move inside each gap, so variation along the entire continuous path can be larger. [Crossley, Theorem 3.4](https://github.com/leecrossley/crossley-criteria-riemann-hypothesis/blob/5fdcf17aef81eed22eded82acc29519ae4ff92c7/paper/crossley-criteria-riemann-hypothesis.md#L183-L191) · [Earlier concavity argument by bramble_trace](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

## A common starting point

All six rows start at $a=8{,}503{,}056$. The starting margin is 766.36653 and the maximum loss $L$ is 134.64037 in every row. The same early minimum remains the lowest even as the block grows. Units in the table are raw deficit units.

| Right endpoint | Checkpoints | Sum of downward steps $V$ | Fewest blocks with fresh margins |
| --- | ---: | ---: | ---: |
| $2a$ | 271,628 | 531.90725 | 1 |
| $4a$ | 791,998 | 1,377.06731 | 2 |
| $8a$ | 1,790,407 | 1,951.94943 | 3 |
| $16a$ | 3,709,000 | 4,079.02200 | 4 |
| $32a$ | 7,401,640 | 5,614.06862 | 4 |
| $54a$ | 12,321,146 | 8,041.49478 | 5 |

At $x=20{,}779{,}214$ the accumulated downward steps first exceed the starting margin. This lies between $2a$ and $4a$. The local margins for the five-block certificate start at $a$, then at $20{,}779{,}102$, $52{,}157{,}662$, $112{,}146{,}478$ and $308{,}391{,}574$. The first split is one checkpoint before the first excess.

Across the larger continuous range $[256,459{,}165{,}024]$, the starting margin is 6.60534 and the deepest loss from that start is 0.72492. The downward steps sum to 9,227.35881. Fourteen blocks suffice under the same rule. The certificate includes all six previously published intervals and the five additional nested comparisons. [Integer bounds, first excesses and split locations](../extension/checkpoint-loss.csv) · [Original minimum certificate](../extension/certificate.csv)

## Why the block count is minimal for this rule

Let $V(i,j)=\sum_{i<k\le j}\max(0,d_k)$. Accept a block with endpoint indices $i,j$ when $V(i,j)<F_i$. The greedy construction starts at $i$ and extends as far as that inequality permits. When the next step would exhaust the margin, the last passing checkpoint becomes the next start.

If a block from $i$ to $j$ passes, every suffix from $k$ to $j$ passes as well. Indeed, $F_k\ge F_i-V(i,k)$, and therefore

$$
F_k-V(k,j)\ge F_i-V(i,j)>0.
$$

Since $V(k,j)$ is nondecreasing in $j$, every prefix of a passing block also passes. Given any valid partition, one can extend the first block to its greedy endpoint, discard the boundaries it crosses, and retain a passing suffix of the block containing that endpoint. This never increases the count. Repeating gives the greedy partition. The reported block counts are minimal among partitions with boundaries on this checkpoint grid and this strict block rule.

## Reproduce the certificate

From the repository root run

```sh
python3 extension/run.py --loss --check extension/checkpoint-loss.csv
```

The verifier integrates the outward-rounded slopes of $2F$ between consecutive events $p,2p,4p$. For each whole checkpoint step it encloses the increment before taking its negative part and adding to the downward total. At each checkpoint it also evaluates an affine enclosure for $F$ directly to locate the minimum, certify its uniqueness and compare the accumulated drops with the relevant starting value. Every recorded split and first excess is separated by strict rational inequalities. Each pair of integer bounds in the CSV has denominator $2^{81}$. A zero in `first_excess_x` records that the total stayed strictly below the starting margin through the last checkpoint.

An independent integer calculation using prime prefix sums reproduces the three smallest windows, including their first excesses and split locations. Its enclosures lie within the reported certificate. Run `python3 extension/recount_loss.py extension/checkpoint-loss.csv` from the repository root. A separate floating-point scan using cumulative sums of $\log p$ and $(\log p)/p$ reproduced all eleven checkpoint counts, minimum locations and partitions. [Arithmetic used by the verifier](../extension/README.md)

These finite results explain precisely where an estimate based on downward steps alone runs out of room in this example. To use the block argument on arbitrarily late power windows, an analytic proof would have to supply sufficient margins at the new starts and bound the downward variation to the next start, or directly bound the signed losses. The observed five-block count supplies no uniform bound as the starting scale increases.

LadyElinor directed the study. OpenAI Codex assisted with the interval arithmetic and comparison. The tent criterion and checkpoint reduction draw on Lee Crossley's and bramble_trace's work. [Project contributors and sources](../CREDITS.md)
