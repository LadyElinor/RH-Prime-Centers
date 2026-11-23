# Contributors and sources

Four Primes and RH Prime Centers · November 22, 2026

## Project contributors

**LadyElinor.** Directed the investigation, selected the research questions, reported the quartet overlap counts, requested independent checks and maintains the public repository. [Project account](https://github.com/LadyElinor) · [Research repository](https://github.com/LadyElinor/RH-Prime-Centers)

**OpenAI Codex and ChatGPT.** Provided AI assistance with derivations, verifier implementations, certificate replays, writing and site preparation. The project generated its prime lists and result tables from the published rules. [Prime-window code and records](https://github.com/LadyElinor/RH-Prime-Centers) · [Four Primes code and records](https://four-primes.owonm.chatgpt.site/#methods)

## Ordinary-prime windows

**bramble_trace.** Published the dyadic ordinary-prime criterion at every prime center, the concavity argument and a fixed-point prefix-sum certificate checking 78,498 centers through r = 1,000,000. Revision 35 reports positive deficit at every real center through 10³⁵. In our notation r = 2y = x/2 and D(y) = 3 Dₚ(2y). [Original post](https://rstation.ai/r/riemann_hypothesis/posts/100) · [Revision 24 with certificate](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) · [Revision 35 and its bounds](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=35)

**Lee Crossley.** Suggested the three-scale filter for the disappearing-zero example. In Window criteria for the Riemann hypothesis, v1.1.1, he formalized pole preservation and the implication from recurring real windows to RH in Lean. Ordinary-prime windows, v1.1.0, gives the forward argument and the all-widths treatment. Both releases specify CC BY 4.0. [Original suggestion](https://x.com/lee_crossley/status/2124465481268461882) · [Criterion release](https://doi.org/10.5281/zenodo.24421600) · [Pole transfer](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/DelayedPole.lean#L113-L174) · [Lean theorem](https://github.com/leecrossley/prime-window-rh-criterion/blob/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/PrimeWindow.lean#L194-L198) · [Companion release](https://doi.org/10.5281/zenodo.24416358) · [Companion proof](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md#L55-L65)

**Pi and Osgood001.** Pi authored the standalone truncated explicit formula for primitive Dirichlet characters. Osgood001 staged the source in the project based on Levent Alpöge’s formalization. Our conductor-one application uses the primitive character modulo one and the Mathlib Chebyshev module by Alastair Irving, Terry Tao and Ruben Van de Velde. [Pi’s pinned proof](https://github.com/Osgood001/riemann-hypothesis/blob/25bc57f3919f3578d396b71f8bc2cf9b3675ac63/community/core3-attempt-97759/Solution.lean) · [Project application and reproduction](formal/core3/README.md)

**LadyElinor project.** The certificate reported here locates the unique minimum of D(y)/√y at y = 159,693.5 for 64 ≤ y ≤ 114,791,256. It checks possible minima inside every affine piece. The accompanying written note also gives a short endpoint argument for sparse power windows. [Study and downloads](https://four-primes.owonm.chatgpt.site/prime-windows) · [Exact certificate](https://github.com/LadyElinor/RH-Prime-Centers/blob/main/extension/certificate.csv)

**Joseph Bertrand and Pafnuty Chebyshev.** Bertrand proposed the prime-between-n-and-2n statement and Chebyshev proved it. The endpoint deduction uses this result. Eric W. Weisstein gives the historical attribution. [Bertrand’s Postulate, MathWorld](https://mathworld.wolfram.com/BertrandsPostulate.html)

**Earlier and related literature.** Loïc Grenié and Giuseppe Molteni studied a related centered kernel. Tianyu Zhao studied oscillation of integrated prime errors. Robert Polak gives a related fourth-power sampling criterion. Further references and acknowledgments for the all-widths argument are in Crossley’s companion paper. [Grenié and Molteni, Theorem 3.5](https://arxiv.org/abs/1607.02430) · [Zhao](https://arxiv.org/abs/2411.18903v2) · [Polak’s paper and acknowledgments](https://github.com/robopol/Riemann-hypothesis/blob/fc1ed5fe13cb1f93d68ebde25e763c5ff1ec88a4/papers/ordinary_prime_tent_windows.tex#L60-L81) · [Crossley’s bibliography](https://github.com/leecrossley/prime-window-all-widths/blob/5f5be229a1c42d6200fafeab4698480068e9055a/PROOF.md)

**David Platt and Tim Trudgian.** Their finite-height verification of zeta zeros is an input to bramble_trace’s larger analytic positivity range. The revision records the other estimates used there. [The Riemann hypothesis is true up to 3·10¹²](https://doi.org/10.1112/blms.12460) · [Revision 35](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=35)

## Four Primes and Artin densities

**Pieter Moree and Peter Stevenhagen.** Computing higher rank primitive root densities, Theorem 2.5. The project uses their radical Galois description to account for dependence between local power tests. [Paper](https://arxiv.org/abs/1203.4313v2)

**Olli Järviniemi and Antonella Perucca.** Unified treatment of Artin-type problems, Theorem 4.1. The passage from the calculated Galois probability to a limiting density uses Dedekind-GRH for the relevant fields. [Paper](https://arxiv.org/abs/2202.11329v2)

**Olli Järviniemi, Antonella Perucca and Pietro Sgobba.** Unified treatment of Artin-type problems II develops the related theory of index maps. [Companion paper](https://arxiv.org/abs/2211.15614)

**Francesco Pappalardi.** On Minimal Sets of Generators for Primitive Roots is an earlier study of multi-generator primitive-root questions. [Publisher’s article](https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/on-minimal-sets-of-generators-for-primitive-roots/C222563D11CB0DBA8F0B23601F385B98)

**Peter Gustav Lejeune Dirichlet and Andrew V. Sutherland.** After the Chinese remainder theorem combines the local conditions, Dirichlet’s theorem gives infinitely many covering primes. Sutherland’s MIT lecture 18, Theorem 18.1, supplies the statement used here. [Primes in arithmetic progressions](https://math.mit.edu/classes/18.785/2019fa/LectureNotes18.pdf)

## Origin and verification of the RH proof

**Levent Alpöge and Anthropic’s Claude.** Alpöge describes his work with Claude on the proof that supplied the smoothed-ramp and power-window setting. His announcement and the released formalization document this upstream work. [Alpöge’s announcement](https://alpo.ge/remark.pdf) · [Formalization release](https://github.com/CocoSgt/riemann-hypothesis-lean/releases/tag/v2026-11-20)

**Andrew V. Sutherland, the Lean and Mathlib communities, and independent checker contributors.** Sutherland documents his verification work with Claude Code, the individual checks and their authors. The community statement is endorsed by the Lean FRO and the Mathlib Initiative. The verified statements cover ordinary RH and Dirichlet L-functions. The quartet density uses a further Dedekind-GRH hypothesis. [Verification files and credits](https://math.mit.edu/~drew/grh/) · [Joint community statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

**Mathlib arithmetic modules.** Xavier Roblot authored the Abel summation formalization, Bhavik Mehta the von Mangoldt module, and Alastair Irving, Terry Tao and Ruben Van de Velde the Chebyshev module, including the Costa Pereira bounds used for the higher powers. [Pinned sources and downstream proof](formal/core3/README.md#the-discrete-ordinary-prime-formula)

## Software and publication

**Arithmetic and formal verification.** Python Software Foundation and Python contributors maintain Python and its decimal logarithm. GCC contributors maintain g++. Torbjörn Granlund and the GMP development team provide the multiprecision arithmetic. The upstream formal proofs use Lean and Mathlib. [Python decimal](https://docs.python.org/3/library/decimal.html#decimal.Decimal.ln) · [GCC](https://gcc.gnu.org/) · [GMP](https://gmplib.org/) · [Lean](https://lean-lang.org/) · [Mathlib](https://leanprover-community.github.io/mathlib4_docs/)

**Scientific computing and graphics.** The quartet search uses NumPy (Charles R. Harris and coauthors). Separate numerical spot checks used mpmath (Fredrik Johansson and contributors) and SymPy (Aaron Meurer and coauthors). John D. Hunter and the Matplotlib contributors developed the plotting software. [NumPy](https://doi.org/10.1038/s41586-020-2649-2) · [mpmath](https://mpmath.org/) · [SymPy](https://doi.org/10.7717/peerj-cs.103) · [Matplotlib](https://doi.org/10.1109/MCSE.2007.55)

**Typesetting and fonts.** The prime-window PDFs use ReportLab and DejaVu fonts. The website uses Inter by Rasmus Andersson and the Inter Project Authors under the SIL Open Font License 1.1. [ReportLab](https://www.reportlab.com/) · [DejaVu](https://dejavu-fonts.github.io/) · [Inter](https://rsms.me/inter/) · [Bundled font license](https://four-primes.owonm.chatgpt.site/assets/inter-license.txt)
