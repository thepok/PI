# Full BBP endpoint phase at epoch 16

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Frozen inputs:

| artifact | SHA-256 |
|---|---|
| [full-phase report through epoch 14](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [independent audit through epoch 14](bbp_three_grid_full_phase_experiment_20260813_independent_audit.md) | `6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9` |

Primary artifacts:

| artifact | SHA-256 |
|---|---|
| [checker](bbp_endpoint_e16_experiment_20260813.py) | `d9fc5d4f8bff417bb50812788c0f893a03d9c02c343b1a031f69b390a2320e13` |
| [retained output](bbp_endpoint_e16_experiment_20260813_record.txt) | `2a9b25378bdf0a0a7a8d796c76c5e7058932876bb0a8004f21322d792edf982d` |

## Outcome and exact claim boundary

This finite computation has label `experiment`.  It proves no asymptotic gap
law, Fourier decay, fixed return, or occurrence of words of unbounded length.
Canonical V1 remains a `conjecture`; nothing here is a `candidate resolution`
or a `verified resolution`.

The complete epoch-16 pre-drop and first-drop rows each contain 5,491,685
phases.  Their common truncated center gap is

\[
 \widetilde G={2736782005017\over10^{18}}
              =2.736782005017\cdot10^{-6},                 \tag{E16.1}
\]

and

\[
             {L\widetilde G\over\log L}=0.968476769148622. \tag{E16.2}
\]

This extends the prior twelve-row range through epoch 14 by two rows and more
than a factor nine in row length.  The normalized gap remains inside the
previous empirical range

\[
                    0.899<{LG\over\log L}<1.084.           \tag{E16.3}
\]

There is also a strictly finite digit consequence.  For the actual pi orbit,
not merely the BBP partial sum, the largest-gap upper bound is

\[
                G_\pi<{2736782005019\over10^{18}}<10^{-5}. \tag{E16.4}
\]

Consequently the finite exponent window meets every decimal cylinder of
length five, including those with leading zeros.  Equivalently, every decimal
word of length at most five occurs somewhere in this certified pi prefix.
This bounded fact is still an `experiment`; it says nothing about arbitrary
word length.

## 1. Exact rows and quantifiers

For even epoch \(e=16\), put

\[
 A_e={3^e-1\over8},\qquad M_e^-=5A_e-1,\qquad M_e^+=5A_e,
 \qquad U(M)=\lfloor\log_{10}(16^M)\rfloor.                \tag{E16.5}
\]

The two complete rows are:

| stage | \(M\) | \(U(M)\) | \(L=U-M+1\) |
|---|---:|---:|---:|
| pre-drop | 26,904,199 | 32,395,883 | 5,491,685 |
| first-drop | 26,904,200 | 32,395,884 | 5,491,685 |

The BBP row under measurement is

\[
 X_M=\{\{(10^n-16)B_M\}:M\le n\le U(M)\},                \tag{E16.6}
\]

with the same partial sum \(B_M\) as the frozen full-phase report.  The
pi-centered comparison set is

\[
 Y_M=\{\{(10^n-16)\pi\}:M\le n\le U(M)\}.                \tag{E16.7}
\]

The digit occurrence in (E16.4) refers to the unshifted set
\(\{\{10^n\pi\}\}\).  Translation by \(16\pi\) preserves circular gaps,
so (E16.7) and the unshifted set have the same largest gap.

## 2. Directed prefix and exact transfer

The checker uses MPFR 4.2.2 through gmpy2 2.3.1.  It computes
\(\lfloor\pi10^N\rfloor\) independently under downward and upward rounding
at sufficient binary precision and accepts the 32,395,907-place prefix only
when both integers agree.  It similarly brackets \(4M\log_{10}2\), then
checks the resulting \(U(M)\) by the exact integer inequalities

\[
                         10^{U(M)}\le16^M<10^{U(M)+1}.      \tag{E16.8}
\]

For every retained exponent, the next 18 certified decimal digits give an
exact rational center \(\widetilde y_n\).  The independent truncations of
\(\{10^n\pi\}\) and \(\{16\pi\}\) imply

\[
             \|\widetilde y_n-\{(10^n-16)\pi\}\|_{\mathbb T}<10^{-18}.
                                                                    \tag{E16.9}
\]

The positive BBP-tail bound from the frozen report then gives

\[
 \|\widetilde y_n-\{(10^n-16)B_M\}\|_{\mathbb T}
 <\eta_M:=10^{-18}+{1\over15(M+1)^2}.                    \tag{E16.10}
\]

Moving every point by less than \(\eta_M\) changes a largest circular gap by
less than \(2\eta_M\) and a prescribed-target distance by less than
\(\eta_M\).  Thus the checker reports exact rational outward intervals, not
binary-floating enclosures.  For the two rows,

| stage | \(\eta_M\) | rigorous BBP-gap interval |
|---|---:|---:|
| pre-drop | \(9.3101897012673\cdot10^{-17}\) | \([2.7367820048307962059,\ 2.7367820052032037940]\cdot10^{-6}\) |
| first-drop | \(9.3101890166018\cdot10^{-17}\) | \([2.7367820048307962197,\ 2.7367820052032037803]\cdot10^{-6}\) |

The exact numerators and denominators are retained in the output artifact.

For the actual pi orbit, (E16.9) alone gives

\[
                   G_\pi<\widetilde G+2\cdot10^{-18},      \tag{E16.11}
\]

which is (E16.4).  A circle set whose largest gap is strictly less than
\(10^{-5}\) meets every half-open interval
\([k/10^5,(k+1)/10^5)\).  Those intervals are exactly the five-digit decimal
cylinders.  The corresponding one-indexed starting positions lie between
26,904,200 and 32,395,884 on the pre-drop row.

## 3. Retained values

Both rows have the same exact truncated target distance

\[
                  \widetilde d_0={6212346013\over10^{17}}
                  =6.212346013\cdot10^{-8}.                \tag{E16.12}
\]

Their first two normalized Fourier magnitudes were also computed:

| stage | \(|\widehat\mu(1)|\) | \(|\widehat\mu(2)|\) |
|---|---:|---:|
| pre-drop | 0.0001591580933441 | 0.000165938039838824 |
| first-drop | 0.00015935600452984 | 0.000165767821489929 |

These Fourier entries are explicitly ordinary float diagnostics.  They are
not directed enclosures and support no Fourier-decay claim.

The checker also rejects truncated-phase collisions and sorts all 5,491,685
residues to obtain the complete circular gap, including the wraparound gap.
The run completed with `status=PASS` in 112.78 seconds wall time and used a
maximum resident set of 518,148 KiB on the recorded machine.  Reproduction
changes neither the mathematical label nor the finite scope.

## 4. What this does and does not change

The stable scale in (E16.2) is stronger falsification evidence against the
possibility that the epoch-14 behavior was a small-sample accident.  It is
also numerically aligned with a random covering law.  None of that supplies
the missing uniform-in-epoch estimate.

The exact missing statement remains an all-sufficiently-large-epoch bound,
for example

\[
        \exists C,e_0\ \forall e\ge e_0\text{ even}\ \forall\sigma\in\{-,+\},
        \qquad G_e^\sigma\le C{\log L_e^\sigma\over L_e^\sigma}.      \tag{E16.13}
\]

That statement is a `conjecture`.  The experiment neither proves (E16.13)
nor replaces its universal quantifier by a legitimate argument.
