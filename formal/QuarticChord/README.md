# Quartic chords for the ordinary-prime deficit

The [public Lean statements](../QuarticChord.lean) formalize the [quartic-chord argument](../../notes/quartic-chords.md) for the actual ordinary-prime tent. Given the prime count below, `quartic_chord_limit` proves that for each real $B\ge 0$,

$$
\lim_{A\to\infty}\ \sup_{0<H\le A^{3/4}(\log A)^B, A\le x\le A+H}
\frac{|F(x)-L_{A,H}(x)|}{\sqrt A}=0.
$$

Here $F$ is $(x/2)\log 2$ minus the sum of $\max(0,\min(x/p-1,2-x/(2p)))\log p$ over ordinary primes $p\le x$. Each chord uses the two values of $F$ at its own endpoints. The supremum ranges over a single set of admissible length–position pairs. Lean proves that this set of normalized errors is nonempty and bounded for all sufficiently large $A$.

## Mathematical inputs

1. **Prime counts.** `GuthMaynardPrimeCount` is the $\epsilon=1/20$ instance of Guth and Maynard's Corollary 1.3. It is an explicit argument to the public theorems. There exists a constant $C\ge0$ such that, for every sufficiently large real $z$ and every $z^{17/30+1/20}\le h\le z^{99/100}$,
   $$
   |\pi(z+h)-\pi(z)-h/\log z|\le Ch\exp(-(\log z)^{1/4}).
   $$
   Lean uses Mathlib's `Nat.primeCounting` at the floored real endpoints. The finite interval count equals that difference exactly. The published prime-count proof remains external. [Paper, Corollary 1.3](https://arxiv.org/html/2405.20552v2) · [Lean hypothesis and reduction](GuthMaynard.lean)
2. **Positive anchor recurrence.** To deduce arbitrarily late positive windows, one fixed $\eta>0$ must give $F(k^4)\ge\eta k^2$ at every integer $K\le k\le K^2$ for arbitrarily large integers $K$. This recurrence remains open in the direct unconditional approach.
3. **Weak anchor recurrence.** The alternative weak transfer assumes one fixed $C\ge0$ and arbitrarily late blocks with $F(k^4)\ge-Ck^2$ at every anchor. It gives $F(x)\ge-(4C+1)\sqrt{x}$ on the associated real windows. This recurrence also remains open. The positive and weak hypotheses are used in separate theorems. [Window statements](Windows.lean)

## Proof map

| Source | What Lean derives |
|---|---|
| [Elementary](Elementary.lean) | Right derivatives within $\varepsilon$ of a fixed slope give chord error at most $2\varepsilon H$. A common main term cancels with coefficients $-1,3/2,-1/2$. |
| [PrimeTent](PrimeTent.lean) | A fixed finite sum of hinges equals the max/min tent on the whole cell. Its right slope changes by the signed sum of events in $(A,A+u]$, including coincident events. |
| [CountWeight](CountWeight.lean), [GuthMaynard](GuthMaynard.lean), [Scale](Scale.lean) | For $z=A/d$, $h=u/d$, count integers when $h\le z^{2/3}$ and apply Corollary 1.3 above this cutoff. Replacing $\log z$ by $\log p$ costs at most $h/z$ per prime. One eventual bound covers all offsets and $d=1,2,4$. |
| [PartialSummation](PartialSummation.lean) | Mathlib's Abel summation theorem gives the common term $\log(1+u/A)$ for the three reciprocal-weighted sums. Uniform unweighted error $M$ gives weighted error at most $dM/A$. |
| [Asymptotic](Asymptotic.lean), [Supremum](Supremum.lean) | The per-cell error is at most $24MH/A$. With $V=A^{3/4}(\log A)^B$, a bound $M\le CV/(\log A)^m$ and $H\le V$ give normalized error at most $24C(\log A)^{2B-m}$. Any $m>2B$ suffices. |
| [Windows](Windows.lean) | The $B=1$ estimate controls every late fourth-power cell by $o(k^2)$. Every real point of $[K^4,K^8]$, including its right endpoint, belongs to a cell with both anchors in the integer block. |

The transfer uses each cell's own endpoints. A qualifying block bounds the minimum throughout that same block without adding errors across cells. The conclusion here ends at the continuous-window estimates. The reference to Crossley's RH criteria in the written note is downstream.

## Reproduce

From `formal/` with Elan available, the repository selects Lean 4.24.0 and the manifest pins Mathlib to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

```sh
lake exe cache get Mathlib.Analysis.Calculus.MeanValue Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics Mathlib.NumberTheory.AbelSummation Mathlib.NumberTheory.PrimeCounting Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
./check_quartic_chords.sh
```

The script builds the public module and replays every local declaration in each of the ten compiled quartic modules against its pinned imports. Each replay requires a named theorem in that module and rejects local axioms, unsafe or partial declarations, and direct placeholders. The public module also prints the transitive axiom lists for the supremum limit, fourth-power cell limit, the two same-block transfers, and their recurrence corollaries. Each list contains only `propext`, `Classical.choice`, and `Quot.sound`. The prime-count estimate and the respective anchor margins appear as premises in the theorem types.

The separate [finite-block certificate](../../notes/check_quartic_chords.py) checks the block $K=6$ with outward rounding. A single certified block supplies no recurrence theorem.

## Verification record

The pinned x86-64 Linux build passed. Kernel replay accepted 155 local declarations across the ten quartic modules and 79 across the three existing standalone certificates. The $K=6$ numerical checker reproduced 30 cells, 228,620 vertices, a lower anchor margin of $0.2174k^2$, and an upper chord departure of $0.1016k^2$.

The separate Lean 4.34.1 Core 3 build and its FLINT spectral computation were not rerun. Neither is a dependency of the quartic target. The Mathlib dependencies used their pinned compiled cache.
