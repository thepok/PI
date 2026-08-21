# The decimal digits of π: state of knowledge of an autonomous research campaign

**Date:** 2026-07-23 (v2, revised after external review; see revision note below).
**Root question:** does every finite string of decimal digits occur somewhere in the decimal expansion of π?

## Abstract

This document surveys everything an autonomous theorem-proving research system has established, over seven successive research programs, about the question whether π is *disjunctive* in base 10 — whether every finite decimal word occurs contiguously in its expansion. The question remains open, as does every strictly weaker rung of a target ladder the system built beneath it (positive lower block density, quantitative block hitting, positive factor entropy, superlinear factor complexity). What the campaign produced instead is: (i) a machine-checked lattice of the problem's variants and of the implications among all rungs of the ladder; (ii) a small body of unconditional π-specific results, essentially the consequences of irrationality and of published irrationality-measure bounds; (iii) about a dozen bounded, source-pinned literature audits, none of which found a published theorem reaching any rung for π itself — a scoped negative claim: the exact first unmet hypothesis is recorded per audited candidate, but a finite set of audits cannot establish exhaustive absence from the literature; (iv) a family of conditional bridges reducing the whole problem to a handful of precisely stated open collision, correlation, and exponential-sum hypotheses about the orbit $\{10^j\pi\}$; and (v) a machine-checked portrait of what failure would have to look like — a pincer of simultaneous pathologies (spectral resonance, entropy deficit, Lebesgue singularity, dimension defect) forced by the negation of the density target. Every mathematical claim below is traceable to an accepted, adversarially reviewed artifact; theorems marked kernel-checked were verified by the Lean 4 kernel against mathlib. A closing section states the labeling conventions and lists questions on which expert input would be most valuable.

**Revision note (v2).** This revision responds to an external review of v1. Two prose-level errors are corrected: the v1 summary of [pi-digits T18] overstated a subsequence statement as a bound holding at every prefix (§3), and v1 misclassified the existential form of the PowerTenDiophantine hypothesis as fully open when it is dischargeable, non-effectively, from the pinned irrationality-measure bound (§5 item 9, §9 Q5). In addition, the literature-audit claims are now scoped to the sources and search paths actually audited, the ladder's partial order is stated precisely (§2), a tone pass removed rhetorical emphasis, and Appendix A adds the material needed for independent audit. The underlying formal corpus required no correction: on both technical objections the kernel-checked Lean statements were already correct as stated, and the errors were confined to this document's prose summaries.

**Reading conventions.** Bracketed tags like [pi-digits T29] name accepted artifacts in the corresponding program's record. Program short names map to repository slugs as follows: *pi-digits* (`pi-digits`, the human-authored root), *factor-complexity* (`pi-decimal-factor-complexity`), *block-hitting* (`pi-quantitative-block-hitting`), *block-density* (`pi-positive-lower-block-density`), *lacunary* (`pi-lacunary-near-return-sparsity`), *factor-entropy* (`pi-positive-decimal-factor-entropy`), *collision-decay* (`pi-long-lag-block-collision-decay`). Verification labels are used exactly as the system assigned them: **kernel-checked** (compiled by the Lean 4 kernel, no `sorry`, axioms restricted to `propext`, `Classical.choice`, `Quot.sound`, against a pinned mathlib commit), **replayed experiment** (finite computation, independently re-run bit-for-bit; heuristic evidence only, never proof), **pinned audit** (literature claims tied to SHA-256-hashed retrieved sources with exact locators), **sketch note** (a rigorous written proof, adversarially reviewed but not machine-checked), **conditional** (a proved implication whose π-specific premise is open), **necessary-only** (a proved consequence of the *failure* of a target, with no converse), **heuristic-only**, and **OPEN**.

---

## 1. The problem, its normalization, and the variant lattice

Throughout, write $\pi = 3.d_1 d_2 d_3\ldots$ for the unique nonterminating decimal expansion, $d_i \in D = \{0,\ldots,9\}$. The original question ("does any integer sequence occur at some point in the expansion of π?") was normalized on 2026-07-21 into an immutable root statement with three recorded readings, since the phrase "any integer sequence" is genuinely ambiguous:

- **V1 (canonical):** every *finite* digit string occurs contiguously somewhere in $(d_i)$; leading zeros permitted, so this covers digit strings rather than integer representations (the stronger and more natural normalization). Equivalently: π is disjunctive (rich) in base 10. **OPEN.** Implied by, and weaker than, base-10 normality of π, which is open in every base.
- **V2:** every *infinite* digit sequence occurs contiguously. **FALSE**, provably: a contiguous infinite occurrence is a tail of the expansion; there are only countably many tails but uncountably many infinite digit sequences. The system holds a complete machine-checked disproof via an explicit diagonal sequence avoiding all tails of π — kernel-checked as the module's main theorem [pi-digits T8].
- **V3:** every infinite digit sequence occurs as a *scattered* (not necessarily contiguous) subsequence. Kernel-checked to be equivalent to: every digit $0,\ldots,9$ occurs infinitely often in the expansion [pi-digits T9]. **OPEN** — it is not even proven that every single digit occurs infinitely often in π.

The relations among the variants are themselves kernel-checked: V1 implies recurrent occurrence of every word (every word occurs beyond every threshold), hence V1 ⇒ V3; and the converse fails for decimal streams in general — the stream $n \bmod 10$ satisfies V3 while omitting the word $00$ [pi-digits T21]. The formalization defines the digit stream of π directly from `Real.pi` by floor-based digit extraction, with the three variant statements matched line-by-line against the immutable problem file [pi-digits T7].

A further kernel-checked reformulation underpins nearly everything below: **V1 holds if and only if the base-10 orbit $(\,\{10^k\pi\}\,)_{k\ge 0}$ of fractional parts is dense in $[0,1)$** [pi-digits T20]. This turns a combinatorial question about digit strings into a dynamical question about the orbit of a single point under $x \mapsto 10x \bmod 1$, and it is the interface through which all Fourier-analytic and measure-theoretic work enters.

## 2. The ladder of targets and the proved relations among them

The system organized its attack as a ladder of target statements — more precisely, a ladder with a side branch, since one rung is incomparable to another at the stated rates (see below). All notation is as follows. For $n \ge 1$ let $F_\pi(n) = \{(d_i,\ldots,d_{i+n-1}) : i \ge 1\}$ be the set of length-$n$ *factors* (contiguous blocks) and $p_\pi(n) = |F_\pi(n)|$ the factor-complexity function. For a word $w = (w_0,\ldots,w_{k-1}) \in D^k$ and $N \ge 1$ let

$$A_\pi(w,N) \;=\; \#\{\,n : 0 \le n < N,\ d_{n+j+1} = w_j \text{ for } 0 \le j < k\,\}$$

count occurrences of $w$ starting in the first $N$ positions. The ladder:

1. **Irrationality baseline.** $p_\pi(n) \ge n+1$ for all $n \ge 1$ (Morse–Hedlund, from irrationality). Kernel-checked for the formal π stream [pi-digits T11], [factor-complexity T1].
2. **Superlinear factor complexity (SFC):** $\lim_n p_\pi(n)/n = \infty$. The canonical target of *factor-complexity*. **OPEN.**
3. **Positive factor entropy (PFE):** $\exists\, \eta > 0,\ N \ge 1$ with $p_\pi(n) \ge 10^{\eta n}$ for all $n \ge N$; equivalently the entropy $h_{10}(\pi) = \lim_n \log_{10} p_\pi(n)/n$ (the limit exists by submultiplicativity) is strictly positive. The canonical target of *factor-entropy*. **OPEN.**
4. **V1 (disjunctivity):** every word occurs. Kernel-checked to be equivalent to full entropy $h_{10}(\pi) = 1$ [factor-entropy T1]. **OPEN.**
5. **C1 — positive lower block density**, the canonical target of *block-density*: for every $k \ge 1$ and every $w \in D^k$,
   $$\liminf_{N\to\infty} \frac{A_\pi(w,N)}{N} \;>\; 0 .$$
   **OPEN.** Strictly stronger than V1, strictly weaker than normality.
6. **Quantitative block hitting:** one uniform $C \ge 1$ such that every $w \in D^k$ occurs fully within the first $C\,k\,10^k$ digits, for every $k$. The canonical target of *block-hitting*. **OPEN.** Stronger than V1; neither implies nor follows from C1 at these rates (recorded ambiguity A11 of the block-density statement).
7. **Base-10 normality:** every $w\in D^k$ has limiting frequency $10^{-k}$. **OPEN** — strictly the strongest rung; not a system target per se, but its solved analogue (Champernowne) was fully formalized as a template (§4.1).

As a Hasse diagram, the structure is: the chain irrationality baseline < SFC < PFE < V1 < C1 < normality is linearly ordered by the proved (or definitional) implications, and quantitative block hitting sits on a side branch attached above V1 — it implies V1 but, at the stated rates, neither implies nor follows from C1.

The load-bearing implications along the ladder are kernel-checked, not folklore: C1 ⇒ V1 [block-density T1]; V1 ⇔ $h_{10}=1$ [factor-entropy T1]; if a length-$k$ word is missing then $p_\pi(mk) \le (10^k-1)^m$ for every $m$, so $h_{10}(\pi) \le \frac1k\log_{10}(10^k-1) < 1$ — contrapositively, any entropy lower bound above that threshold certifies occurrence of *every* length-$k$ word [pi-digits T32]. On the V3 side: a stream whose recurrent alphabet has $r$ letters has entropy at most $\log r$ (after a finite cutoff), so entropy $> \log 9$ would force all ten digits to recur and hence V3; the bound is sharp, witnessed by an explicit nine-digit stream [pi-digits T33]. Separators keeping the ladder honest are also machine-checked: an explicit "sparse island" stream satisfies V1 (every word occurs) while the word $1$ has lower density zero — so V1 does not imply C1 [block-density T2]; and Champernowne's constant satisfies C1 [block-density T2].

## 3. What is unconditionally known about π here

The honest summary: for the fixed number π, the system's unconditional stock consists of the irrationality-measure lineage and its formal consequences, plus a collision-free region at very fine scales. Everything else is conditional or necessary-only.

**Irrationality and the linear baseline.** π is irrational (mathlib), giving $p_\pi(n) \ge n+1$ [pi-digits T11] and, kernel-checked, the existence of two distinct decimal digits each occurring beyond every threshold in π's expansion [pi-digits T13]. That — two digits occurring infinitely often — is essentially the strongest unconditional occurrence statement the system holds for π.

**Irrationality measure.** The relevant published bounds are pinned at source: Salikhov (2008), $\mu(\pi) \le 7.6063085\ldots$ [pi-digits T14], and Zeilberger–Zudilin (2020), $\mu(\pi) \le 7.103205334137\ldots$ [lacunary T18], [block-density T24], [factor-entropy T5]. (Recall $\mu(x)$ is the irrationality measure: the infimum of exponents $\mu$ such that $|x - p/q| < q^{-\mu}$ has only finitely many solutions.) From the Salikhov bound the system derived, in a source-pinned sketch note, a digit-change lower bound: the number $C_\pi(N)$ of adjacent digit changes among the first $N$ digits satisfies $C_\pi(N) \ge \log N/\log 8 - C$ for explicit constants — long constant runs would produce too-good rational approximations [pi-digits T14]. A kernel-checked module then converts this (taking T14's inequality as an explicit hypothesis) into logarithmic occurrence bounds along a subsequence of prefixes. The precise statement of the theorem `pi_fixed_pair_log_lower_bound_of_T14` [pi-digits T18]: there *exist* distinct digits $a \ne b$ such that *for every* threshold $B$ there *exists* $N \ge B$ at which the directed bigram $ab$ and each of the digits $a$, $b$ occur at least $\tfrac{1}{90\log 8}\log N - (C'/90 + 1)$ times among the first $N$ digits — one fixed pair, witnessed along an unbounded subsequence of prefix lengths, *not* at every sufficiently large prefix; the module's docstring states explicitly "This is not an eventual fixed-pair claim." The formal Lean statement was always this subsequence version; the prose summary in v1 of this document overstated it as a bound at every prefix. The result is conditional only on the pinned literature input, and it is exponentially far from any rung of the ladder.

**A collision-free fine region.** Combining the pinned effective irrationality bounds with the kernel-checked lag decomposition of collision energy: near returns $\|10^n(10^r-1)\pi\| < 10^{-m}$ are impossible once $m \ge (\mu-1)(n+r)$, so with $\mu = 7.104$ all non-diagonal collisions are excluded when the block length is comparable to the sample size ($m \ge (\mu-1)(N-1)$ forces $Q_\pi(m,N) = N$, diagonal only) [block-density T24], [block-density T25]. The same audit quantifies the fundamental *scale mismatch*: at the scales the ladder actually needs ($m = o(N)$), the irrationality-measure route leaves order $N^2$ pairs uncontrolled — a structural insufficiency, not a matter of constants [block-density T24].

**What the literature audits established negatively.** Roughly a dozen bounded, source-pinned audits ([pi-digits T6, T12, T19, T28], [factor-complexity T2, T11], [block-hitting T4, T9], [block-density T5, T24], [lacunary T3, T18, T21], [factor-entropy T5]) examined the published record against the exact quantifiers of each rung. The uniform outcome: **in the sources and search paths audited, no published theorem reaches any rung of the ladder for π itself.** This is a scoped negative — a dozen bounded audits cannot establish exhaustive absence from the literature; what they establish is that each examined candidate fails, with the failure point recorded. The recurring first-unmet-hypothesis patterns, each recorded per candidate with exact quotations and hashes:

- *Conditional and wrong base:* Bailey–Crandall reduces 2-normality of π to their unproved Hypothesis A about a dynamical iteration; the conclusion is base 2/16, and kernel-checked transfer is unavailable — indeed base-2 normality does not even imply base-10 disjunctivity for general reals (Schmidt's theorem plus a $T_{10,2}$-style construction; refuted-transfer audit [pi-digits T12]). BBP-type formulas give unconditional base-16 digit extraction — the strongest directly π-specific unconditional result found — but no decimal distribution information [pi-digits T6].
- *Almost-everywhere, not π:* the entire metric theory of lacunary sequences (Erdős–Gál, Philipp, Fukuyama LIL and discrepancy bounds, Rudnick–Zaharescu pair correlation, Salem–Zygmund CLT) instantiates the needed finite certificates for Lebesgue-almost every $x$ — but nothing puts π in the good set, the exceptional-set thresholds are ineffective, and π's transcendence does not bridge a metric exceptional set [pi-digits T28], [factor-entropy T5], [lacunary T3].
- *Wrong hypothesis class:* Adamczewski–Bugeaud's superlinear complexity theorem applies to algebraic irrationals; π is transcendental, so the central hypothesis is false for it [factor-complexity T2], [factor-entropy T5].
- *Individual versus collective:* irrationality-measure bounds separate phases pair by pair but supply no aggregate cancellation; the weighted sums stay at trivial scale [factor-complexity T11], [factor-entropy T5].

## 4. The seven programs, briefly

### 4.1 pi-digits (root; 25 accepted items; retired 2026-07-22, superseded)

Beyond the variant lattice (§1), the root program built four things. (a) *The Champernowne chain*, a complete kernel-checked normality proof for the solved analogue: the formal Champernowne stream is disjunctive [pi-digits T22]; every length-$k$ word has explicitly counted occurrences in each complete epoch, with $m$-independent coefficient $9k(10^{k-1}{+}1)$ [pi-digits T23]; a discrepancy bound for arbitrary prefixes cut mid-epoch [pi-digits T24]; and finally full base-10 normality — for every word $w$, overlapping occurrence frequency in the length-$N$ prefix tends to $10^{-|w|}$ — kernel-checked as the module's main theorem [pi-digits T25]. This is the system's template for what a resolution artifact looks like. (b) *Conditional bridges in both directions*: the explicit Weyl-cancellation hypothesis — for every nonzero integer $h$, $\frac1N\sum_{k<N} e^{2\pi i h 10^k \pi} \to 0$ — kernel-checked to imply orbit density and hence V1 [pi-digits T26]; and a finite Erdős–Turán-style certificate: if $|\sum_{j<N} e^{2\pi i h 10^j\pi}| \le \varepsilon N$ for all $0 < |h| \le H$, every length-$k$ decimal cylinder receives frequency at least $\bigl(1 - H\varepsilon - \tfrac{1}{(H+1)L^2}\bigr)/(H+1)$ with $L = 10^{-k}$ [pi-digits T27]. (c) *Necessary-only obstructions*: with $H(k) = 2\cdot 10^{2k}$ and $\varepsilon(k) = (8\cdot 10^{2k})^{-1}$, if some length-$k$ word never occurs, then some single fixed frequency $h$, $0<|h|\le H(k)$, resonates — $|\sum_{j<N} e^{2\pi i h 10^j\pi}| \ge \varepsilon(k) N$ for arbitrarily large $N$ — kernel-checked [pi-digits T29]; upgraded in a sketch note to an $S$-invariant weak-* limit measure $\mu$ of the orbit empiricals with $|\hat\mu(h)| \ge \varepsilon(k) > 0$ [pi-digits T30]; and the entropy deficits of §2 [pi-digits T32, T33]. (d) *No-go countermodels* showing these invariants cannot suffice: an explicit non-π stream satisfying full disjunctivity *and* carrying a fixed-frequency resonance of modulus tending to 1 — so resonance is not a signature separating V1 from ¬V1 [pi-digits T31]; and the decimal Thue–Morse-type constant with irrationality exponent exactly 2, linear factor complexity ($p(n) < 8n$), digit-change density $2/3$, yet using only the digits 0 and 1 — so irrationality-measure and digit-change information, however good, cannot by themselves yield V3, V1, or superlinear complexity [pi-digits T16].

### 4.2 factor-complexity (11 items; retired 2026-07-22, superseded)

Self-formulated first successor: prove $p_\pi(n)/n \to \infty$ (SFC). Main products: the kernel-checked reduction of SFC to divergence of average right-extension branching [factor-complexity T3]; the collision-energy route — defining $E_\pi(n,N) = \sum_w m_w^2$ (sum of squared multiplicities of length-$n$ blocks among the first $N$ starts), the Cauchy–Schwarz bridge shows the sibling hypothesis **FC-C1** ($\forall C>0$, eventually in $n$, $\exists N$: $N^2 > C\,n\,E_\pi(n,N)$) implies SFC, kernel-checked [factor-complexity T4]. A sketch-note countermodel proved FC-C1 is *strictly stronger* than needed: an explicit disjunctive stream refutes FC-C1 with $C=4$ while having full complexity — the program's own conjecture, refuted by its own skeptic lane [factor-complexity T5]. The random baseline: in the iid uniform model, almost surely blocks are eventually pairwise distinct at scale $N_n$ with $N_n/n \to\infty$ (Borel–Cantelli, sketch note) [factor-complexity T7]. The Diophantine reduction: $E_\pi \le Q_\pi$, where
$$Q_\pi(n,N) = \#\{(i,j) \in \{0,\ldots,N{-}1\}^2 : \|(10^i - 10^j)\pi\|_{\mathbb R/\mathbb Z} < 10^{-n}\}$$
(ordered pairs, diagonal included), and the chain C2 ⇒ FC-C1 ⇒ SFC is kernel-checked, where **C2** is near-return sparsity: $\forall C>0$, eventually in $n$, $\exists N$: $Q_\pi(n,N) < N^2/(Cn)$ [factor-complexity T8]. A self-contained Fejér-kernel argument (sketch note [factor-complexity T9], kernel-checked [factor-complexity T10]) reduces C2 to the weighted Fourier-energy hypothesis **HFE(π)**: for all $A,\varepsilon > 0$ there is $n^*$ such that for all $n \ge n^*$ some $N \ge 1$ satisfies
$$\sum_{h=1}^{\lceil An\rceil} \min\Bigl(2\cdot 10^{-n} + \tfrac{1}{\lceil An\rceil + 1},\ \tfrac{1}{\pi h}\Bigr)\, \Bigl|\sum_{j<N} e^{2\pi i h 10^j \pi}\Bigr|^2 \;<\; \varepsilon\, \frac{N^2}{n}.$$
The closing audit found no published theorem matching HFE(π)'s fixed-π quantifiers; the first unmatched clause per candidate is recorded [factor-complexity T11].

### 4.3 block-hitting (16 items; retired 2026-07-22, superseded)

Attacked the uniform cover-time bound $L_\pi(k) \le C\,k\,10^k$. Calibration: the Champernowne stream satisfies it with $C = 22$, kernel-checked constructively [block-hitting T2]; an iid uniform stream satisfies it with $C_{\mathrm{rand}} = 18$ simultaneously for all $k$ with positive probability (sketch note, exact symbolic union bounds, no simulation) [block-hitting T7]. A discrepancy certificate implying the bound is kernel-checked [block-hitting T3]; two audits found no π-specific quantitative result instantiating it [block-hitting T4, T9]. The program's main legacy is the **boundary-robust Fejér dichotomy toolkit** (necessary-only, all kernel-checked): failure of the cover bound alone forces, at every deadline $D = C\,k\,10^k$, a nonzero frequency $h$ with $|h| \le 128\cdot 10^k$ and normalized resonance at least $1/(16388\,(k{+}1)\,10^k)$ [block-hitting T6, T8]; refined through explicit Fejér convolution estimates on circular cylinders into a two-branch dichotomy [block-hitting T13, T14]: either aggregated Fourier resonance, or *boundary concentration* — the missing word's two cyclically adjacent neighbors (words with long all-zero or all-nine suffixes) must occur at least $\lceil N/(8\cdot 10^k)\rceil$ times [block-hitting T15, T16]. Finally, a power-of-ten Diophantine condition — $\mathrm{PowerTenDiophantine}(\pi,\mu,A)$: $|\pi - p/10^t| \ge 10^{-\mu t}$ for all $t \ge A$ and all integers $p$ — kernel-checked to exclude the boundary branch (long zero/nine runs are exactly power-of-ten rational approximations), reducing failure to the pure resonance branch [block-hitting T17]. Both hypotheses (the cover bound's negation, PowerTenDiophantine) are retained as explicit premises; nothing unconditional about π is claimed in the Lean artifact. (See §5 item 9: the non-effective existential form of PowerTenDiophantine is dischargeable from the pinned irrationality-measure bound.)

### 4.4 block-density (25 items; rotated out of FOCUS 2026-07-23 after converging)

The central program: C1, positive lower block density. Its formalization and equivalences (empirical-measure form, cylinder boundaries handled) are kernel-checked [block-density T1], with solved-analogue and separator streams [block-density T2, T4] and the exponential-sum sufficient condition in quantitative form — the π specialization keeps the sum bound as an explicitly named unproved hypothesis [block-density T3]. Two pinned audits closed the literature ([block-density T5], effective-irrationality [block-density T24]). The program's most developed product is the **¬C1 pincer**, a chain of kernel-checked necessary-only theorems, described in §6. On the positive side it produced the energy route now carrying the campaign: a full-dimensional cylinder-energy criterion — if for every $s \in (0,1)$ there are $C, N_0$ with normalized collision energy $E_\pi(m,N) \le C(10^{-sm} + 1/N)$ for all $N \ge N_0,\ m \ge 1$, then C1 holds — kernel-checked [block-density T23]; the partition of collision pairs into diagonal, irrationality-excluded, and residual classes, formalized with the published $\mu = 7.104$ bound as an explicit pinned premise [block-density T25]; and the short-lag/long-lag split showing ordered short-lag pairs contribute at most $2Nm$, reducing C1 to decay of only the *long-lag residual pairs* — the conditional implication is kernel-checked [block-density T26]. That final reduction was promoted to the collision-decay program and the program retired with its agenda honestly exhausted.

### 4.5 lacunary (18 items; active)

Successor to factor-complexity's HFE wall: the canonical target is near-return sparsity **NRS-A1**: for every $A \ge 1$ there is $n_0$ such that every $n \ge n_0$ admits $N \ge 1$ with $A\,n\,Q_\pi(n,N) \le N^2$. Kernel-checked infrastructure: the lag decomposition $Q_\pi(n,N) = N + 2\sum_r \#\{n' : \|10^{n'}(10^r{-}1)\pi\| < 10^{-n}\}$ [lacunary T1]; normality implies the near-return estimate for generic normal streams, with Champernowne specialization — locating NRS-A1 strictly below normality [lacunary T2]; two-sided comparison (factor 3) between metric near-returns and decimal-cylinder collisions, and the equivalence of NRS-A1 with its cylinder-energy form [lacunary T5, T6, T7]. Conditional bridges: the cluster small-ball hypothesis (lacunary C2: some weak-* limit $\nu$ of orbit empiricals satisfies $(\nu\times\nu)\{(x,y): \|x-y\| \le r\} \le Cr^\alpha$) implies NRS-A1 [lacunary T4]; a multiscale characterization of that hypothesis via coherent collision decay [lacunary T12]; and the **splitting premise**: $\mathrm{PiSufficientSplitting}(\mu,\eta)$ — at enough refinement levels, cylinder-occupancy mass sits on parents whose second-largest successor carries an $\eta$-fraction, each such level shrinking energy by $(1-\mu\eta)$ — implies NRS-A1, with the exact inverse (failure forces dominant-successor concentration at almost all levels), kernel-checked [lacunary T9, T14]. Necessary-only obstructions: failure of NRS-A1 forces low-harmonic resonance at explicit scales $N = 16AnK$ [lacunary T10] and arbitrary-depth autocorrelation-chain resonances [lacunary T13]. The sketch lane then mapped the obvious escape route and closed it: the resonances produce special rational approximations to π, but with error exponent tending to 1 relative to the available denominator bound — *quantitatively compatible* with $\mu(\pi) \le 7.1033$; verdict **INSUFFICIENT**, with the three missing statements (a resonance inverse theorem, a coefficient-growth bound $q \le cL^{0.1638\ldots}$, cross-scale coherence) recorded as the exact gap [lacunary T18], refined through a cycle/preperiod dichotomy for the resonant phase [lacunary T19] and a generalized concentration analysis, again INSUFFICIENT [lacunary T21]. The program also certified 1,048,596 decimal digits of π by exact rational interval arithmetic from a pinned Chudnovsky-type formula (Milla, Thm 10.12), independently replayed [lacunary T17], feeding the splitting measurements of §7.

### 4.6 factor-entropy (11 items; active)

The staircase program for PFE. Kernel-checked: formalization and the $h_{10}=1 \Leftrightarrow$ V1 endpoint [factor-entropy T1]; the collision bridge — hypothesis **C2** ($\exists \eta > 0$: eventually in $n$, some $M$ has $E_\pi(n,M) \le M^2 10^{-\eta n}$) implies PFE via Cauchy–Schwarz [factor-entropy T2]; a Parseval lower bound and dichotomy under ¬C1 (here C1 = PFE's own canonical claim) [factor-entropy T3, T4]. The hypothesis staircase, each implication kernel-checked with explicit constants: **C3**, Poisson pair correlation for the fixed orbit $x_i = \{10^i\pi\}$ — for every $s>0$, $M^{-1}\#\{(i,j): i \ne j < M,\ \|x_i - x_j\| < s/M\} \to 2s$ — implies C2 with $\eta = 1/2$ at $M = 10^n$, hence PFE [factor-entropy T6]; the Fejér spectral hypothesis implies C2 [factor-entropy T7]; a dyadic-shell pair bound implies the Fejér hypothesis (constant $5A+1$) [factor-entropy T8]; and **C5** — for $M_n = 10^n$, some $A$ with $\#\{(i,j) < M_n : \|x_i - x_j\| < 2^k/M_n\} \le A(2^k{+}1)M_n$ for all $k$ with $4^k \le M_n$ — implies the whole chain down to PFE [factor-entropy T9, T10]. The pinned audit [factor-entropy T5] identified fixed-π Poisson pair correlation (C3) as the single strongest missing hypothesis in the literature-adjacent landscape; the closing coherent-amplification audit returned INSUFFICIENT, with an explicit unit-circle counterexample showing one large exponential sum does not self-amplify [factor-entropy T11].

### 4.7 collision-decay (1 item; active — the current frontal program)

The reduction chains described above terminate here. The canonical question: with $B_\pi(i,m)$ the length-$m$ block starting at digit $i{+}1$ and
$$R_\pi(m,N) = \#\{(i,j)\in\{0,\ldots,N{-}1\}^2 : |i-j| \ge m,\ B_\pi(i,m) = B_\pi(j,m)\},$$
does every $s \in (0,1)$ admit $C_s \ge 1$ with
$$R_\pi(m,N) \;\le\; C_s\,(N + N^2\cdot 10^{-sm}) \quad\text{for all } m, N \ge 1\ ?$$
The additive $N$ term repairs finite-sample granularity; the lag condition removes diagonal and overlapping blocks. The first accepted artifact fixes the architecture: kernel-checked, the canonical predicate, the exact comparison $E_\pi \le R_\pi + \text{diagonal} + 2Nm$ short-lag pairs, and the theorem that the canonical bound **implies positive lower block density** — hence, composing with [block-density T1], implies V1 [collision-decay T1]. The intended meaning: if some word were absent, its forbidden language would have entropy strictly below $\log 10$, contradicting the collision bound for $s$ close to 1. One open conjecture and one theorem now stand between this single estimate and the root question.

## 5. The named open hypotheses that carry the problem

Each hypothesis below is OPEN for π, with one exception: item 9's non-effective existential form is dischargeable from the pinned irrationality-measure bound (see there). What is *proved* (kernel-checked unless noted) is the implication arrow to the ladder. They are ordered roughly by how much of the problem each one carries.

1. **Long-lag collision decay** (collision-decay A1, displayed above). Implies C1, hence V1 [collision-decay T1] + [block-density T1]. This is a deterministic additive-energy-type statement: among $N$ consecutive windows of the digit stream, non-overlapping equal length-$m$ blocks number at most a constant times the random-model count $N^2 10^{-sm}$, uniformly in $m,N$, for every $s<1$. True for a.e. real and for Champernowne-type streams by the sibling results; open for every naturally occurring constant.
2. **Residual long-lag decay** (block-density C2): the same decay required only for the pair class left after irrationality-measure exclusions — for every $s\in(0,1)$, residual pairs with lag $\ge m$ number at most $C N^2(10^{-sm} + 1/N)$ [block-density T25, T26]. Weaker premise, same conclusion C1.
3. **Cylinder-energy decay** ([block-density T23] hypothesis): normalized collision energy $E_\pi(m,N) \le C(10^{-sm} + 1/N)$. Implies C1.
4. **Fixed-π Poisson pair correlation** (factor-entropy C3, displayed in §4.6). Implies positive factor entropy with $\eta = 1/2$ [factor-entropy T6, T2]. Known for almost every $\alpha$ in place of π (Rudnick–Zaharescu, pinned); known for no explicit transcendental constant, per the audits.
5. **Dyadic-shell bound C5 / Fejér spectral bound C4** (factor-entropy): band-limited versions of 4, each implying PFE through the kernel-checked staircase [factor-entropy T7–T10].
6. **HFE(π)** (factor-complexity, displayed in §4.2): weighted Fourier energy $o(N^2/n)$ at linear frequency cutoff. Implies near-return sparsity C2, hence FC-C1, hence superlinear complexity [factor-complexity T8–T10]. The weakest Fourier hypothesis on the list, attacking the lowest rung.
7. **NRS-A1 / the splitting premise** (lacunary): the near-return sparsity target itself, and the combinatorial $\mathrm{PiSufficientSplitting}(\mu,\eta)$ premise implying it [lacunary T9]; the cluster small-ball hypothesis (lacunary C2) also implies it [lacunary T4].
8. **Weyl cancellation for $\{h\,10^k\pi\}$** ([pi-digits T26] hypothesis): $\frac1N\sum_{k<N} e^{2\pi i h 10^k\pi} \to 0$ for every fixed $h \ne 0$. Implies orbit density, hence V1 directly. Strictly stronger in spirit than the collision bounds (it is what normality proofs actually establish for artificial constants).
9. **PowerTenDiophantine** ([block-hitting T17]): $\mathrm{PowerTenDiophantine}(\pi,\mu,A)$ — $|\pi - p/10^t| \ge 10^{-\mu t}$ for all $t \ge A$ and all integers $p$. Used to close the boundary branch of the cover-bound dichotomy. **Reclassified in v2 — dischargeable, not open.** The existential form $\exists A,\ \mathrm{PowerTenDiophantine}(\pi, 8, A)$ follows non-effectively from the pinned bound $\mu(\pi) \le 7.1032\ldots < 8$: by the definition of the irrationality measure, only finitely many rationals $p/q$ violate the exponent-8 inequality $|\pi - p/q| \ge q^{-8}$; restricting to denominators $q = 10^t$ and choosing $A$ past the finitely many exceptional exponents $t$ yields the predicate. A discharge item recording this implication is queued in the system. The genuinely open refinement is an *effective* numeral $A$, which needs effective onsets from the published proofs (Question 5 of §9, now sharpened to effectivity only).
10. **Bailey–Crandall Hypothesis A** (external, pinned [pi-digits T6]): the one published reduction of comparable ambition; conditional, base 2/16, and non-transferable to base 10 by [pi-digits T12].

**Why these are hard — the fixed-point versus almost-everywhere barrier.** Every hypothesis above is a statement about the *single orbit* $\{10^j\pi\}$. The available machinery proves such statements (i) for almost every starting point, with ineffective exceptional sets that no property of π is known to avoid [pi-digits T28], [factor-entropy T5]; or (ii) for engineered constants whose digits are constructed to make the estimate true (the Champernowne chain [pi-digits T22–T25], [block-density T2], [lacunary T2]); or (iii) pair-by-pair via irrationality measures, which operate at the wrong scale — they clear collisions only when $m \gtrsim 6.1\,(n+r)$, leaving the entire bulk regime untouched [block-density T24], and cannot be leveraged through the resonance obstructions without a presently nonexistent inverse theorem [lacunary T18, T21]. The system's countermodels sharpen the barrier from below: the invariants that *are* accessible for π (irrationality exponent, digit-change density, single resonances) are all realized by streams that fail V1 badly [pi-digits T16, T31], [factor-complexity T5] — so no proof can succeed from those invariants alone; genuinely new π-specific input is required.

## 6. What failure would have to look like

The ¬C1 pincer is the campaign's most developed structure: a chain of kernel-checked necessary-only theorems, all with the literal negation of C1 (positive lower block density) as hypothesis. Assembled, they portray the world in which the density target fails. In that world there is a least deficient block length $k_0$ and a specific word $w$ of that length with lower density zero, while every shorter word retains uniformly positive eventual density [block-density T19]. Along one common subsequence of prefix lengths [block-density T20]: the empirical measures of the orbit $\{10^j\pi\}$ converge weakly to a shift-invariant probability measure $\nu$ on the circle that gives *zero mass to a nonempty open set* (the missing cylinder, propagated under powers of ten) [block-density T7]; $\nu$ carries a strictly positive Fourier coefficient at a fixed bounded frequency — persistent spectral resonance [block-density T6], echoing [pi-digits T29, T30]; $\nu$ has Shannon entropy strictly below $\log 10$, with the deficit quantified [block-density T8] and visible in finite π prefixes at growing scales [block-density T9, T15]; $\nu$ is mutually singular with Haar (Lebesgue) measure [block-density T10]; $\nu$-almost all of the circle sits in a set of Hausdorff dimension strictly less than 1, with an explicit bound through the forbidden-language growth rate [block-density T11, T12, T13, T21]; the block-frequency limit organizes into a stationary de Bruijn flow with positive vertex marginals but a forced zero edge [block-density T19]; and the forbidden-language entropy deficit is certifiable by finite transfer-matrix computations with exact rational certificates [block-density T14, T16]. Simultaneously, from the other programs' necessary-only lanes: multiscale low-harmonic resonances at explicit scales [lacunary T10, T13] and dominant-successor concentration at almost every refinement level [lacunary T9]. In short: for π's digits to avoid some word with density zero, the orbit of one specific, explicitly computable transcendental number would have to imitate — along a subsequence, with machine-checked precision — a fractal, spectrally rigid, entropy-deficient invariant system, while every finite window ever computed looks statistically flat (§7). None of this refutes ¬C1: the system proved [pi-digits T31] that resonance alone is satisfiable by disjunctive streams, and it claims no probabilistic conclusion. But it is a precise account of what any disproof of the mission must construct, and of the many independent finite signatures (spectral, entropic, dimensional, combinatorial) failure would eventually have to exhibit.

## 7. Experiments and heuristic evidence

All computations below carry the system's **experiment** label: finite, independently replayed, heuristic-only; the immutable problem statements assign them zero resolution leverage, and every report states so.

- **Collision energy at scale $10^6$** [factor-complexity T6]: on 1,000,011 fractional digits (two pinned independent sources, hash-matched), exact integer energies $E(n,N)$ for $n \le 12$, $N \le 10^6$, against the exact iid expectation $N + N(N-1)10^{-n}$ and three fixed-seed pseudorandom controls: π's ratio $E/E_{\mathrm{iid}}$ stayed within $[0.9909, 1.0040]$ across the grid, inside the controls' spread.
- **Near-return counts** [lacunary T8]: high-precision (36 certified digits of working precision, stability-margin-checked) computation of $Q_\pi(n,N)$ and cylinder energy for $n = 3,\ldots,8$, $N \le 32{,}000$, with lag histograms: minima broadly follow diagonal-plus-uniform scaling; no persistent bad lag visible at these scales.
- **Certified digits** [lacunary T17]: 1,048,596 decimal digits certified by exact rational interval arithmetic from a pinned published formula, replayed twice (once under a 4 GiB memory cap); this replaces trust in third-party digit files for subsequent experiments.
- **Successor-splitting measurement** [lacunary T20]: on the certified digits, exact rational Pareto envelope of the splitting parameters $(\eta,\mu,d)$ of [lacunary T9] at checkpoints up to $N = 65{,}536$: π exhibits splitting behavior (e.g. a retained point $\eta = 1/10$, $d = 4/7$) comparable to seeded iid and Champernowne controls; the T9 refinement identity held on all 168 measured rows.
- **Failure-signature calibration** [block-density T18]: on 10,003 digits reproduced by two independent algorithms, all 166,650 word counts for $k \le 4$, block spectra, and the T14–T16 automaton certificates: the finite ¬C1 signatures do fire on an engineered zero-density control stream and do not fire on π, which is indistinguishable from the iid and normal controls at these cutoffs. This calibrates detectability of the pincer's signatures; it says nothing about the liminf.

Under the random model (heuristic only, stated as such in the pinned artifacts), every rung of the ladder holds almost surely with room to spare [factor-complexity T7], [block-hitting T7]; all finite evidence is consistent with π behaving like a random stream. The system treats this exclusively as attack-side guidance — evidence about which side to prove, never progress on proving it.

## 8. Honest status assessment

**What is claimed.** As inventory — the counts describe the corpus's size, not its depth, and formal theorem counts inflate easily via bookkeeping lemmas — across the seven programs the record holds 107 accepted items, including 75 kernel-checked Lean modules exposing about 530 named theorems, roughly a dozen pinned literature audits, five replayed experiments, and a sketch-note lane. Every theorem *about π specifically* in this corpus is one of: (i) **unconditional but far below the target** — the irrationality baseline, two recurrent digits, logarithmic digit-change and occurrence bounds resting on pinned irrationality measures, and the fine-scale collision-free region; (ii) **conditional** — a kernel-checked implication whose π-specific premise is one of the named open hypotheses of §5; or (iii) **necessary-only** — a kernel-checked consequence of the *negation* of a target, with no converse claimed. No rung of the ladder — superlinear complexity, positive entropy, V1, C1, the cover bound, normality — is established for π, and the system has never claimed otherwise. The reader need not audit for hidden overclaiming: the immutable problem statements forbid it, an adversarial skeptic reviewed each item against them, and the acceptance records quoted throughout preserve the labels.

**Map versus wall.** What the campaign has genuinely produced is a *map*: the variant lattice and ladder with machine-checked implications; the reduction of the entire problem to a single family of collision/correlation estimates on one orbit; the exact first-unmet-hypothesis inventory of the audited literature (scoped as in §3: the audits found no theorem reaching a rung, which is not proof that none exists); countermodels closing off every route that uses only currently-π-accessible invariants; and a machine-checked portrait of failure. The *wall* — some fixed-point estimate of the type in §5 — is untouched, and the two attempts to break a piece of it with existing Diophantine input returned honest INSUFFICIENT verdicts with the missing lemmas named [lacunary T18, T21], [factor-entropy T11]. What would move the needle: any fixed-π estimate beating the trivial $N^2$ bound on collisions or the trivial bound on one lacunary exponential sum by an unbounded factor at the relevant scales; a resonance inverse theorem in the sense of [lacunary T18]; or a transfer principle importing a.e. lacunary results to points with effective Diophantine properties. Absent that, the honest expectation recorded in the problem statements stands: the open hypotheses are hard, and the system's role is to keep the reduction frontier sharp and formally checked.

## 9. Questions for the reader

1. **The collision bound.** Is the long-lag estimate $R_\pi(m,N) \le C_s(N + N^2 10^{-sm})$ (§4.7) — or any hypothesis of §5 — known, partially known, or approachable with current technology for *any* explicitly given non-engineered constant? Its formal shape is an additive-energy bound ("no more ordered collisions than the random count") for the exponentially growing sequence $10^j\pi$. Which field's toolkit best matches this shape — additive-combinatorial energy/inverse theorems, sieve-type almost-all arguments localized at one point, shrinking-target dynamics, or something else we have not audited?
2. **Fixed-point pair correlation.** Rudnick–Zaharescu give Poisson pair correlation for $\{\alpha g^j\}$ for a.e. $\alpha$. Is there any known — or plausibly provable — instance of this for a *specific* natural transcendental $\alpha$ (factor-entropy C3, §4.6)? Is there folklore on why the exceptional set cannot currently be avoided?
3. **The no-go results.** The audits' structural conclusions — a.e. lacunary theory cannot be specialized to π and transcendence does not bridge metric exceptional sets [pi-digits T28]; irrationality-measure bounds have a quantified scale mismatch against energy decay [block-density T24]; resonance obstructions are necessary but not separating [pi-digits T31] — are these known folklore in the metric-number-theory community, or would a careful write-up be a useful contribution?
4. **The ladder.** Does the reduction ordering of §2 (superlinear complexity < positive entropy < disjunctivity < positive lower block density < normality, with the cover bound off to the side) match the folklore ordering of digit questions for π? Are we missing a known intermediate result — e.g., is positive decimal factor entropy of π, or superlinear $p_\pi(n)/n$, known by some route the audits did not surface?
5. **PowerTenDiophantine, effectivity.** The existential form $\exists A$ of the hypothesis $|\pi - p/10^t| \ge 10^{-8t}$ ($t \ge A$; §5 item 9) follows non-effectively from $\mu(\pi) < 8$ and is queued for discharge in the system. What remains open is an explicit numeral $A$: do the published proofs (Salikhov 2008; Zeilberger–Zudilin 2020) yield effective denominator onsets, so that a concrete $A$ can be extracted and the cover-bound dichotomy of [block-hitting T13–T17] collapses to its resonance branch with all constants explicit?
6. **Where would you attack?** Given the map — one kernel-checked chain from a single collision estimate to the root question — which wall of §5 would you invest in, and with what tool?

## How this document was produced

The results surveyed here were generated autonomously by a director/builder/skeptic research system operating on immutable problem statements: each program's canonical question, quantifiers, recorded ambiguities, and verification rules were frozen in a hashed statement file before work began, and no accepted item may weaken or substitute them. Every formal claim was compiled by the Lean 4 kernel against a pinned mathlib commit under a deterministic gate that rejects `sorry`, `admit`, and any axiom outside the standard three (`propext`, `Classical.choice`, `Quot.sound`); an independent statement referee checked line-by-line fidelity between each Lean formalization and the immutable statement. Literature claims are pinned to SHA-256-hashed retrieved sources with exact locators and quotations; numerical experiments ship with reproduction scripts and were independently replayed before acceptance; proof notes not machine-checked are labeled as sketches. Each item was adversarially reviewed by a skeptic agent whose acceptance notes — quoted or paraphrased throughout — record exactly what was and was not established. "Verified" in this document therefore means: checked by the Lean kernel (for theorems), replayed (for computations), or hash-pinned and adversarially audited (for literature); nothing else is asserted.

---

## Appendix A: auditability

This appendix supplies what an independent auditor needs to check the load-bearing claims of this document against the formal corpus.

### A.1 Repository

The corpus is a local git repository at `/home/Marcel/dev/AllMath`. The state cited by this document is commit `5e55722c77e34a38cd2807f37e6014ff32f663e6` (HEAD when this revision was prepared; the commit adding this v2 file follows it). Formal modules live in two synchronized locations: the compiled build tree `TheoryLib/` at the repository root, and the per-item accepted copies under `work/theory/<program-slug>/library/t<n>/`. For every file in the manifest below the two copies were verified byte-identical; the paths and SHA-256 hashes given are those of the `work/theory` copies.

### A.2 Theorem-to-file manifest

The most load-bearing kernel-checked results cited above. Format: item — path (under `work/theory/`) — main theorem name(s) — one-line statement — SHA-256.

1. **[pi-digits T8]** `pi-digits/library/t8/PiDigitsV2Diagonal.lean` — `not_v2` — variant V2 (every infinite digit sequence occurs contiguously) is false, via an explicit diagonal sequence avoiding every tail of π.
   `223ca0054e8979cd3f2f084d97bbb6fcf561462d27b5f671c63b00117b9ceb05`
2. **[pi-digits T20]** `pi-digits/library/t20/BaseTenOrbitDensity.lean` — `v1_iff_pi_baseTenOrbitDense` — V1 holds iff the orbit $(\{10^k\pi\})_k$ is dense in $[0,1)$.
   `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126`
3. **[pi-digits T18]** `pi-digits/library/t18/FiniteAlphabetSubsequentialCounting.lean` — `pi_fixed_pair_log_lower_bound_of_T14` — conditional on T14's digit-change bound: a fixed unequal digit pair has logarithmically lower-bounded bigram and digit counts along an unbounded set of prefix lengths (verbatim statement in A.3).
   `1974b01f1e7238d11a656ac2e909dd110525385e86dee9945b05e65b885175d5`
4. **[pi-digits T25]** `pi-digits/library/t25/ChampernowneNormality.lean` — `champernowne_full_baseTen_normality` — the formal Champernowne stream is base-10 normal (solved-analogue template).
   `619c9dc5497cd3a05d339ac57ccc954c7b138e06e813f9e4ebd62aafb86b46b2`
5. **[pi-digits T26]** `pi-digits/library/t26/WeylCancellationV1.lean` — `pi_baseTen_weylCancellation_implies_canonicalV1` — Weyl cancellation for $\{h\,10^k\pi\}$ (every fixed $h \ne 0$) implies V1.
   `3825d0dcb5bd4d22ffa3cd8853db1bbf79c2ad1faa4ff0f1db96dbf7efc11871`
6. **[pi-digits T29]** `pi-digits/library/t29/FixedFrequencyResonance.lean` — `not_canonicalV1_implies_fixed_frequency_resonance` — a missing word forces one fixed bounded frequency to resonate on arbitrarily large prefixes.
   `36bccfb678a9e3452bb4321a518541d2d0c9af79b995e1305ae47bc35d11c171`
7. **[pi-digits T32]** `pi-digits/library/t32/FactorEntropyObstruction.lean` — `not_canonicalV1_implies_factorEntropy_deficit` — a missing length-$k$ word caps $h_{10}(\pi)$ at $\frac1k\log_{10}(10^k-1) < 1$.
   `a4220356635f89e96724ce4a60167c09026bfcff98b6e34073f0a52794259a34`
8. **[factor-complexity T10]** `pi-decimal-factor-complexity/library/t10/PiWeightedFourierReduction.lean` — `HFE_pi_implies_lacunaryNearReturnC2` — the weighted Fourier-energy hypothesis HFE(π) implies near-return sparsity C2 (Fejér majorant argument).
   `45003707a7b30447c9dd9ed5843f8c899a7c7107814c99f9b7a7a9f4ab8bf4ff`
9. **[block-hitting T17]** `pi-quantitative-block-hitting/library/t17/T17PowerTenDiophantineReduction.lean` — `PowerTenDiophantine` (def), `powerTenDiophantine_excludes_zero_run` / `powerTenDiophantine_excludes_nine_run`, `not_C1_implies_unbounded_aggregated_resonance_of_powerTenDiophantine` — the power-of-ten Diophantine predicate excludes long zero/nine runs and closes the boundary branch of the cover-bound dichotomy, leaving pure resonance.
   `165dcd2b5f6339a9aa42285aff617c11c89c140a04fba26e0fcde3c3828338c1`
10. **[block-density T1]** `pi-positive-lower-block-density/library/t1/PiPositiveLowerBlockDensity.lean` — `PiPositiveLowerBlockDensity` (def), `piPositiveLowerBlockDensity_implies_T7V1`, `piPositiveLowerBlockDensity_iff_everyEmpiricalClusterFullSupport` — the C1 formalization, C1 ⇒ V1, and the empirical-measure equivalence.
    `12c590ae25c2399ba9d0dc7c75ff31ef4ab52e58a3c0d4f321d8dba11e801cdf`
11. **[block-density T10]** `pi-positive-lower-block-density/library/t10/T10HaarSingularCluster.lean` — `not_piPositiveLowerBlockDensity_implies_haar_singular_cluster` — ¬C1 yields an invariant empirical cluster measure mutually singular with Haar measure (verbatim statement in A.3).
    `212b052cc200ab1df9a44ddc80ba72ce48b1defb522b497abc44a82bad3acc03`
12. **[block-density T23]** `pi-positive-lower-block-density/library/t23/T23FiniteCylinderEnergyCriterion.lean` — `piFullDimensionalCylinderEnergyDecay_implies_piPositiveLowerBlockDensity` — cylinder-energy decay at every $s \in (0,1)$ implies C1.
    `8e8f560806f13a8e56bd4432aef2b689309837c8a1adb2bab72cf7c9349e6aa6`
13. **[block-density T26]** `pi-positive-lower-block-density/library/t26/T26LongLagResidualReduction.lean` — `piLongLagResidualPairDecay_implies_piPositiveLowerBlockDensity` — decay of the long-lag residual pair class alone implies C1.
    `744731fcaa2e252a8f63b0a0bbaf09ea86bdc72f379616437cc5b570f282e6b0`
14. **[lacunary T1]** `pi-lacunary-near-return-sparsity/library/t1/LagDecomposition.lean` — `Q_pi_orderedPair_lag_decomposition` — exact lag decomposition of the near-return pair count $Q_\pi(n,N)$.
    `932faf3f1515b5073e07ba81f70aae3cdea9d168bb7ea280bd57e2300e643a68`
15. **[factor-entropy T1]** `pi-positive-decimal-factor-entropy/library/t1/CanonicalEntropy.lean` — `pi_entropy_eq_one_iff_canonical_word_quantifiers`, `entropyBaseTen_eq_one_iff_disjunctive`, `pi_positive_entropy_implies_superlinear` — $h_{10} = 1 \Leftrightarrow$ V1; PFE ⇒ SFC.
    `8f424db10d98a42ab0e547b2abdef0db9c5b45443c05a4e01033502a2934dbdf`
16. **[factor-entropy T6]** `pi-positive-decimal-factor-entropy/library/t6/T6PairCorrelationConditional.lean` — `c3_implies_piPositiveFactorEntropyC1` — fixed-π Poisson pair correlation implies positive factor entropy.
    `9e83797e1ac488dd02a6c607f7f1d99ca2c50eb6c65bd331d7f254bc60775da4`
17. **[collision-decay T1]** `pi-long-lag-block-collision-decay/library/t1/T1LongLagBlockCollisionDecay.lean` — `PiLongLagBlockCollisionDecay` (def), `E_pi_le_R_pi_add_diagonal_add_short`, `piLongLagBlockCollisionDecay_implies_piPositiveLowerBlockDensity` — the canonical long-lag collision bound and its implication to C1 (verbatim statements in A.3).
    `64ff2687e84edc22a843da65a54b3f801713455ff54df457f508cc5ef14a20b0`

Each module ends with `#print axioms` directives on its main theorems; the acceptance gate checks the output against the allowlist of A.4.

### A.3 Verbatim Lean statements of the four central objects

Statements only, quoted verbatim from the files in A.2; proof bodies (and, for the collision-decay implication, its docstring) are omitted.

**(1) Collision decay: canonical definition and main implication** ([collision-decay T1], namespace `Theory.PiDigits.LongLagBlockCollisionDecay`):

```lean
/-- The length-`m` decimal cylinder label of the block starting at `i`.
Via `piCylinderCode`, this is the tuple of the `m` decimal digits, encoded in
base ten with leading zeroes retained. -/
def B_pi (i m : ℕ) : Fin (10 ^ m) := piCylinderCode m i

/-- Ordered equal-block pairs at the canonical nonoverlapping lags.  The
condition `m ≤ Nat.dist i j` is the literal `|i-j| ≥ m` convention. -/
def R_pi (m N : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin N × Fin N)).filter fun ij =>
    m ≤ Nat.dist (ij.1 : ℕ) (ij.2 : ℕ) ∧
      B_pi ij.1 m = B_pi ij.2 m).card

/-- The canonical predicate, including the additive finite-sample term and
the one constant for all positive `m` and `N`. -/
def PiLongLagBlockCollisionDecay : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        (R_pi m N : ℝ) ≤
          C * ((N : ℝ) + (N : ℝ) ^ 2 *
            (10 : ℝ) ^ (-s * (m : ℝ)))

theorem piLongLagBlockCollisionDecay_implies_piPositiveLowerBlockDensity
    (hDecay : PiLongLagBlockCollisionDecay) :
    PiPositiveLowerBlockDensity
```

**(2) PowerTenDiophantine: definition and one exclusion theorem** ([block-hitting T17], namespace `Theory.PiDigits.PowerTenDiophantineReduction`):

```lean
/-- A lower bound restricted to rational approximations whose denominator is
exactly a power of ten.  `A` is a threshold on the exponent, not on the
denominator itself. -/
def PowerTenDiophantine (x : ℝ) (mu A : ℕ) : Prop :=
  ∀ t : ℕ, A ≤ t → ∀ p : ℤ,
    1 / (10 : ℝ) ^ (mu * t) ≤ |x - (p : ℝ) / (10 : ℝ) ^ t|

/-- Under the stated predicate, the explicit suffix cannot be all zeroes at
any exponent between `A` and `D`. -/
theorem powerTenDiophantine_excludes_zero_run
    {mu A t D : ℕ} (hmu : 1 ≤ mu)
    (hpi : PowerTenDiophantine Real.pi mu A)
    (hAt : A ≤ t) (htD : t ≤ D) :
    ¬ ∀ i < (mu - 1) * D + 1,
      Theory.PiDigits.piDigit (t + i) = (0 : Fin 10)
```

**(3) C1 and the singularity theorem** ([block-density T1] definitions, namespace `Theory.PiDigits.PositiveLowerBlockDensity`; [block-density T10] theorem, sub-namespace `T10`):

```lean
/-- Number of starts `0 ≤ n < N` at which `w` occurs in `s`.
Occurrences overlap, and every start before `N` is tested even when the word
extends beyond the first `N` stream entries. -/
def blockCount (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) : ℕ :=
  (Finset.univ.filter fun n : Fin N =>
    ∀ i : Fin w.length, s (n.val + i) = w.get i).card

/-- Canonical normalization of the overlapping block count.  The value at
`N = 0` is immaterial to the limit along `atTop`. -/
def blockFrequency (s : ℕ → Fin 10) (w : List (Fin 10)) (N : ℕ) : ℝ :=
  (blockCount s w N : ℝ) / N

/-- Positive lower asymptotic frequency for every nonempty decimal word.
Lists include words with leading zeros. -/
def HasPositiveLowerBlockDensity (s : ℕ → Fin 10) : Prop :=
  ∀ w : List (Fin 10), w ≠ [] →
    0 < liminf (blockFrequency s w) atTop

/-- A1, specialized to the exact floor-based pi stream from T7. -/
def PiPositiveLowerBlockDensity : Prop :=
  HasPositiveLowerBlockDensity Theory.PiDigits.piDigit

/-- Necessary-only T10 conclusion. Literal failure of canonical C1 yields an
invariant pi empirical cluster carried by measurable unions of positive-mass
aligned decimal cylinders. Their Haar masses decay geometrically, and their
full-`ν` intersection witnesses mutual singularity with Haar measure. This
theorem makes no unconditional assertion about pi or C1. -/
theorem not_piPositiveLowerBlockDensity_implies_haar_singular_cluster
    (hnot : ¬ PiPositiveLowerBlockDensity) :
    ∃ ν : ProbabilityMeasure UnitAddCircle,
      MapClusterPt ν atTop piEmpiricalMeasure ∧ timesTenMap ν = ν ∧
      ∃ k : ℕ, 0 < k ∧ ∃ a : Fin (10 ^ k),
        (ν : Measure UnitAddCircle) (decimalCylinder k a) = 0 ∧
        let E : ℕ → Set UnitAddCircle :=
          fun m => positiveAlignedCylinderUnion ν k m
        let S : Set UnitAddCircle := ⋂ m : ℕ, E m
        (∀ m : ℕ, MeasurableSet (E m)) ∧
          (∀ m : ℕ, (ν : Measure UnitAddCircle) (E m) = 1) ∧
          (∀ m : ℕ, volume (E m) ≤
            (((10 ^ k - 1 : ℕ) : ENNReal) /
              ((10 ^ k : ℕ) : ENNReal)) ^ m) ∧
          MeasurableSet S ∧
          (ν : Measure UnitAddCircle) S = 1 ∧
          volume S = 0 ∧
          (ν : Measure UnitAddCircle) ⟂ₘ volume
```

**(4) The T18 subsequence theorem** ([pi-digits T18], namespace `Theory.PiDigits.T18`):

```lean
/-- Conditional pi specialization of the finite-alphabet theorem. The
hypothesis is T14's explicit bound with `c = 1 / log 8`, `N₀ = 1`, and its
additive constant `C14`. The explicit positive output coefficient is
`(1 / log 8) / 90`; the output additive constant is `C14 / 90 + 1`.

The same fixed unequal pair works along an unbounded set of prefix lengths for
the directed-bigram count and for both endpoint digit counts. This is not an
eventual fixed-pair claim. -/
theorem pi_fixed_pair_log_lower_bound_of_T14 (C14 : ℝ)
    (hT14 : ∀ N : ℕ, 1 ≤ N →
      (1 / Real.log 8) * Real.log N - C14 ≤
        (changeCount Theory.PiDigits.piDigit N : ℝ)) :
    ∃ a b : Fin 10, a ≠ b ∧ 0 < (1 / Real.log 8) / 90 ∧
      ∀ B : ℕ, ∃ N : ℕ, B ≤ N ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (directedBigramCount Theory.PiDigits.piDigit a b N : ℝ) ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (occurrenceCount Theory.PiDigits.piDigit a N : ℝ) ∧
        (1 / Real.log 8) / 90 * Real.log N - (C14 / 90 + 1) ≤
          (occurrenceCount Theory.PiDigits.piDigit b N : ℝ)
```

### A.4 Build instructions

- Toolchain: `leanprover/lean4:v4.30.0` (repository `lean-toolchain` file).
- Dependency: mathlib, required at `v4.30.0` in `lakefile.toml`, resolved in `lake-manifest.json` to the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Build: `lake build TheoryLib` at the repository root compiles the entire formal corpus surveyed here.
- Gate: acceptance ran each candidate module through `tools/lean_candidate_gate.py`, which rejects `sorry` and `admit` and rejects any axiom outside the allowlist `{propext, Classical.choice, Quot.sound}`, as reported by the `#print axioms` directives at the end of each module.

### A.5 Full per-item records

The complete per-item record — acceptance decisions, adversarial skeptic transcripts, prompts, and run traces — lives under `.opencodeworkflow/records/` and under `work/theory/<slug>/` (per-program `knowledge.jsonl` with per-file SHA-256 for every accepted artifact, `log.jsonl`, `program.json`, and the `library/` copies). Pinned literature sources (PDF/HTML with hashes and locators) sit beside the audit notes in the corresponding `library/t<n>/` directories.
