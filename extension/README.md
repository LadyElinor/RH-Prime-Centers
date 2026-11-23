# Prime-window extension

This bundle certifies the dyadic ordinary-prime deficit over every real scale in the closed interval 256 ≤ x ≤ 459,165,024. The research note defines the observable and gives the results. The code is scoped to the fixed windows and numeric range printed in the certificate.

## Replay

On a 64-bit Linux system with Python 3.10+, g++ with 128-bit integer support, and GMP development headers/libraries, run:

```sh
python3 run.py --check certificate.csv
```

The driver produces a certified table of log anchors, compiles the verifier and the interior-minimum regression check, runs both and compares the regenerated CSV exactly. It uses roughly half a gigabyte of memory. Python's correctly rounded Decimal logarithm is used only for 4,097 small anchor entries. All subsequent certificate decisions use integers. A square-root approximation in the fast screen seeds an integer ceiling that is validated by squaring.

To repeat the separate floating-point discovery scan, run:

```sh
g++ -O3 -std=c++17 scan.cpp -o scan
./scan
```

The exploratory values can vary slightly with the platform. The candidate locations in the verifier are hints. An incorrect hint fails the inequalities required for certification.

## Read the certificate

Use F(x)=D(x/4) and R(x)=2F(x)/sqrt(x). Each row covers both closed endpoints and all real x between them. The raw minimum is unique at raw_x. Its rational enclosure is [raw_lo,raw_hi]/2^81. The normalized minimum is unique at norm_x; its enclosure is [norm_vlo,norm_vhi]/(2^80 sqrt(norm_x)). The centers_and_endpoints column counts distinct interior prime centers plus the two endpoints. affine_pieces counts intervals after splitting at every event q, 2q, 4q and at the study's window boundaries. Some cuts come from overlapping windows. exact_fallbacks counts nonadjacent pieces that required an exact squared comparison with the candidate; the two pieces touching the candidate undergo derivative-sign checks.

## Arithmetic

For a prime q write e=floor(log2(q)), h=floor(4096q/2^e), d=h 2^e, n=4096q−d. Then log q=e log 2+log(h/4096)+log(1+n/d). Here 0 ≤ n/d < 1/4096. The third and fourth partial sums for log(1+t) bracket the last term. An integer interval of width 256 at scale 2^57 is checked for every prime, then divided outward to enclose (log q)/q at scale 2^80. The certified pass uses a segmented sieve and cumulative prime sums. The discovery pass uses an odd-only sieve, floating-point logarithms, and integration of slope changes.

The fixed x limit is below 2^29. Logs are below 21, and all 128-bit scaled accumulation and multiplication in the prefix calculation fit comfortably: the total slope sums are bounded by 21 times the harmonic sum through xmax, and total log sums by 21*xmax. Candidate squared comparisons use GMP integers. The compressed fast test rounds its lower value down and its square-root denominator up before comparing.

On each affine piece, the lower bound for 2F is a line mx+b. If both endpoints beat the normalized candidate's upper bound even using the larger denominator sqrt(v), the whole piece passes. Otherwise the verifier compares both endpoints exactly and checks the interior point b/m whenever m>0 and b/m is strictly inside. Its normalized value there is 2 sqrt(mb) in scaled units. At the two adjacent pieces the derivative has the sign of mx−b. These checks prove the winning location is unique even among noninteger scales. The synthetic regression uses (x+4)/sqrt(x) on [1,9]; a threshold of 4.1 passes both endpoints and fails at x=4.

For raw minima, concavity between prime centers reduces the candidate set to the centers and closed endpoints. The verifier checks the winner's upper bound is below every other candidate's lower bound, and checks the value again by summing the original tent weights.

## Sources

bramble_trace’s earlier dyadic argument and certificate use concavity between prime centers. Our extension certifies the minimum after square-root normalization over the stated continuous interval. [Earlier certificate](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) · [Full contributors and sources](https://github.com/LadyElinor/RH-Prime-Centers/blob/main/CREDITS.md)

- [Lean real-window implication](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/PrimeWindow.lean#L194-L198)
- [Companion proof and its earlier finite-range use of concavity](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md)
- [Python Decimal.ln rounding specification](https://docs.python.org/3/library/decimal.html#decimal.Decimal.ln)

## Loss at doubled-prime checkpoints

The [checkpoint loss note](../notes/checkpoint-loss.md) compares the maximum loss from the starting margin with the sum of all downward steps. Run `python3 extension/run.py --loss --check extension/checkpoint-loss.csv` from the repository root to reproduce the eleven rows, first excesses and minimum block counts.
