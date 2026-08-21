# Independent audit: BBP three-primary twisted sum

Audit date: **2026-08-13 UTC**

## Verdict and claim boundary

**PASS on the frozen primary snapshot, with two nonfatal wording
clarifications and no fatal mathematical issue found.** The CRT identity,
the nonlinear grid permutation, the sparse exponent-coordinate Fourier
transform, its fixed-harmonic extension, the restricted Fourier-algebra
bound, and the $M=40$ joint-order obstruction were independently re-derived.
All signs and constants in (TS5)–(TS12), (TS17)–(TS24), and (TS27)–(TS31)
are correct.

The all-depth statements retain label **proof sketch**. The independent
finite replay has label **experiment**. The source audit in Section 7 has
label **literature-checked**. No theorem in this branch is
**machine-checked**, and this audit adds no formal declaration.

The result is an exact reduction to a still-unproved estimate on the
**actual** synchronized BBP complement. It proves neither full-phase
cancellation nor a return to sixteen. Canonical V1 remains a **conjecture**.
This is not a **candidate resolution** or **verified resolution**.

## Frozen inputs

| input | SHA-256 |
|---|---|
| [canonical source](../../problems/local/pi-digits.txt) | 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825 |
| [primary twisted-sum report](bbp_three_primary_twisted_sum_20260813.md) | 0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12 |
| [primary checker](bbp_three_primary_twisted_sum_20260813_check.py) | 7d8a8f7ff85c02b251845ba781d373dbf222a87ba69e0d6f82b1e995b9315e2c |
| [three-primary epoch report](bbp_three_primary_epoch_20260813.md) | 5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7 |
| [large-sieve report](bbp_large_sieve_short_orbit_20260813.md) | 23b3cba4c2b7c5846b4b18748994db8c9e897725612eaf80d08b32b3a97b781d |
| [T73](../../TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean) | 1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009 |
| [Bourgain–Chang PDF](../theory/pi-lacunary-near-return-sparsity/library/t124/bourgain-chang-2006.pdf) | a4c130e401ff03a5b91fbd20339f06021f26bf871ca2bb375f2ce25e3ee5d1d7 |
| [Kerr PDF](../theory/pi-long-lag-block-collision-decay/library/t70/kerr-1302.4170v1.pdf) | 9136dc3965da376942f653b2b06de8d92d7e5e997ee536e1257979698b73e4bd |
| [independent checker](bbp_three_primary_twisted_sum_20260813_independent_check.py) | 42c575e7d5446b46b26941c2c0db8b8289ae44846987f45a3e47beb0e12075be |

The canonical target is Marcel's immutable local question and has no
external source URL; none is invented here. Its exact quantifiers range over
every finite decimal word, including leading zeros, and ask for at least one
contiguous occurrence in pi. This audit does not replace that target with
normality, infinitely many occurrences, or an isolated CRT-coordinate
statement.

This audit did not edit either primary artifact, any Lean source,
AxiomAudit.lean, TheoryLib.lean, or ultrapi.md.

## 1. CRT factorization and nonlinear grid: (TS5)–(TS12)

Put $q=3^E$, $T=3^{E-2}$, and write

\[
 B_M=\frac{P}{qC},\qquad (P,qC)=1,\qquad(q,C)=1.
\]

Define

\[
 \beta\equiv PC^{-1}\pmod q,\qquad
 \kappa\equiv Pq^{-1}\pmod C.
\]

For every integer $N$, the combined numerator of
$e_q(\beta N)e_C(\kappa N)$ is $N(\beta C+\kappa q)$. It is congruent to
$PN$ modulo both $q$ and $C$, hence modulo $qC$. This proves (TS5) with no
sign choice. Substituting $N=h(10^n-16)$ gives (TS6), including negative
$h$ and $h=0$.

Because $10^n\equiv1\pmod9$,

\[
 r_E(n)=\frac{10^n-1}{9}\pmod T
\]

is well-defined. For nonnegative $m,n$,

\[
 r_E(n)=r_E(m)\pmod T
 \iff 3^E\mid10^n-10^m
 \iff n=m\pmod T,
\]

using $\operatorname{ord}_{3^E}(10)=3^{E-2}$. Thus every $T$ consecutive
exponents give a bijection to the additive grid; no zero-based-window
assumption is hidden.

The primary phase satisfies

\[
 10^n-16\equiv9r_E(n)-15\pmod q,
\]

and therefore

\[
 e_q\!\left(h\beta(10^n-16)\right)
 =e_q(-15h\beta)e_T(h\beta r_E(n)).
\]

Pulling the $C$-coordinate through the inverse grid permutation gives
(TS10). With

\[
 \mathcal F_TW(k)=\frac1T\sum_{r\bmod T}W(r)e_T(-kr),
\]

the positive character in (TS10) selects $k=-h\beta$, not $+h\beta$.
Thus the sign and normalization in (TS12) are correct. For fixed nonzero
$h$, its conductor is $T/(T,h)$. The identities also hold at $h=0$, but
the conductor-growth sentence does not.

Finally, the artificial choice $W(r)=e_T(-h\beta r)$ cancels the selected
character term by term and gives magnitude $T$. Orthogonality alone cannot
prove cancellation.

## 2. Sparse primary transform: (TS17)–(TS22)

Let $3\nmid a$ and set

\[
 f(j)=e_{3^E}(a10^j),\qquad
 \widehat f(\ell)=\sum_{j\bmod T}f(j)e_T(-\ell j).
\]

Its circular autocorrelation is

\[
 C_a(d)=\sum_{j\bmod T}
 e_{3^E}\!\left(a10^j(10^d-1)\right).
\]

Writing $10^j=1+9r$, where $r$ runs once modulo $T$, yields

\[
 C_a(d)=e_{3^E}\!\left(a(10^d-1)\right)
 \sum_{r\bmod T}e_T\!\left(ar(10^d-1)\right).
\]

The final sum is $T$ precisely when $T\mid10^d-1$, and zero otherwise.
Put $H=T/9=3^{E-4}$. Since
$\operatorname{ord}_{T}(10)=H$, the surviving shifts are exactly
$d=mH$, $0\le m<9$.

For $E\ge4$, the binomial expansion gives

\[
 10^H=(1+9)^H\equiv1+3^{E-2}\pmod {3^E}.
\]

If $H=3^r$, every term of degree $k\ge2$ has valuation at least

\[
 r-v_3(k)+2k\ge r+4=E.
\]

The range is empty when $E=4$, so the smallest edge case is covered.
Since $2(E-2)\ge E$, raising the congruence to $m<9$ gives

\[
 10^{mH}\equiv1+m3^{E-2}\pmod {3^E},\qquad
 C_a(mH)=T e_9(am).
\]

With the report's transform sign, Wiener–Khinchin becomes

\[
 |\widehat f(\ell)|^2
 =\sum_{d\bmod T}C_a(d)e_T(-\ell d)
 =T\sum_{m=0}^{8}e_9((a-\ell)m).
\]

The last sum is $9$ exactly when $\ell\equiv a\pmod9$, and zero otherwise.
Hence there are $T/9$ surviving coefficients, each with squared magnitude
$9T$ and magnitude $3\sqrt T$. Parseval closes exactly:
$(T/9)(9T)=T^2$.

At $E=4$, $T=9$ and $H=1$. Then
$f(j)=e_{81}(a)e_9(aj)$, so one coefficient survives with magnitude
$9=3\sqrt9$, exactly as claimed.

## 3. Fixed-harmonic extension: (TS23)–(TS24)

For nonzero $h$, write

\[
 h=3^s h_0,\qquad 3\nmid h_0,\qquad R=3^s,
\]

and suppose $E-s\ge4$. After cancelling $3^s$, the sequence is

\[
 e_{3^{E-s}}(a_0 10^j),\qquad a_0=h_0\beta10^{n_0},
\]

with period $T/R$. Across the original length $T$, it repeats exactly $R$
times. Splitting $j=u+v(T/R)$ produces

\[
 \sum_{v=0}^{R-1}e_R(-\ell v),
\]

which vanishes unless $R\mid\ell$ and equals $R$ otherwise. If
$\ell=Rk$, the remaining transform has length $T/R$ and frequency $k$.
Section 2 therefore gives

\[
 \ell=Rk,\qquad k\equiv a_0\pmod9,
\]

with surviving magnitude

\[
 R\,3\sqrt{T/R}=3\sqrt{RT}.
\]

Thus (TS23)–(TS24), including their constant, are correct. Negative
harmonics only change the unit class of $a_0$. The first nonfatal wording
clarification is that $h\ne0$ should be stated where $s=v_3(h)$ is
introduced; the valuation of zero is not being used.

## 4. Restricted Fourier-algebra bound: (TS27)–(TS30)

For $3\nmid h$, absorb the $C$-coordinate and its $-16$ shift into $w(j)$.
Apart from the harmless constant $e_{3^E}(-16h\beta)$, the full sum is

\[
 S=\sum_{j\bmod T}f(j)w(j),
\]

where $a=h\beta10^{n_0}\equiv h\beta\pmod9$. Using the same negative-sign
unnormalized transforms for both factors gives

\[
 S=\frac1T\sum_{\ell\bmod T}
       \widehat f(\ell)\widehat w(-\ell).
\]

Only $\ell\equiv a\pmod9$ survive, each with magnitude $3\sqrt T$. Hence

\[
 |S|\le\frac3{\sqrt T}
 \sum_{\ell\equiv a\ (9)}|\widehat w(-\ell)|,
\]

which is (TS27). Dividing the restricted sum by $T$ gives (TS28) and the
equivalent factor $3\sqrt T$ in (TS29). Therefore

\[
 \mathcal A_{T,a}(w)=o(\sqrt T)
 \quad\Longrightarrow\quad |S|=o(T),
\]

so (TS30) is correct.

The limitation is exact. Unnormalized Parseval for $|w(j)|=1$ is

\[
 \sum_{\ell}|\widehat w(\ell)|^2=T^2.
\]

There are $T/9$ selected frequencies, so Cauchy–Schwarz gives only
$\mathcal A_{T,a}(w)\le\sqrt T/3$. Inserted into (TS29), this returns the
trivial bound $|S|\le T$. No unconditional estimate for the actual BBP
complement has been inserted.

## 5. Fixed ordinary periods: (TS31)

Let an infinite sequence $w(j)$ have fixed ordinary period $d$, and restrict
it to $0\le j<T$. Fourier expansion on one period writes it as a linear
combination of the $d$ rational exponentials $e(mj/d)$. One component
contributes

\[
 D_T\!\left(\frac md-\frac\ell T\right)
 =\sum_{j<T}e\!\left(j\left(\frac md-\frac\ell T\right)\right).
\]

The geometric-sum estimate

\[
 |D_T(x)|\le\min\{T,(2\|x\|)^{-1}\}
\]

and the $1/T$ spacing of the sampled frequencies give

\[
 \frac1T\sum_{\ell\bmod T}|D_T(m/d-\ell/T)|=O(\log T).
\]

Restricting to one residue class modulo nine can only decrease the sum.
Summing the fixed $d$ components proves

\[
 \mathcal A_{T,a}(w)=O_d(\log T),\qquad
 |S|=O_d(\sqrt T\log T).
\]

Thus (TS31) is valid. The second nonfatal wording clarification is that when
$d\nmid T$, “period $d$” means an ordinary infinite periodic sequence
restricted to the length-$T$ window; it is not literally a periodic function
on $\mathbb Z/T\mathbb Z$.

## 6. Independent $M=40$ joint-order replay

The independent checker reconstructs the coefficient from the original four
pole terms:

\[
 \frac4{8k+1}-\frac2{8k+4}-\frac1{8k+5}-\frac1{8k+6}.
\]

For reduced $B_{40}$ it obtains

\[
 v_2(\operatorname{den}B_{40})=160,\quad
 v_3=4,\quad v_5=3,\quad v_7=2.
\]

The upper row exponent is $48$, so $40\le n\le48$ contains nine terms,
equal to $\operatorname{ord}_{81}(10)=9$. Exact CRT reconstruction was
replayed for every term and for harmonics $-2,1,5$.

Projecting to the coprime unit modulus $81\cdot49$ gives

\[
 \operatorname{ord}_{49}(10)=42,\qquad
 \operatorname{ord}_{81\cdot49}(10)=\operatorname{lcm}(9,42)=126.
\]

The nine-term window is a complete primary period but only a prefix of the
126-term joint orbit. On the full reduced denominator, ten is not a unit
because powers of two and five remain. This supports the no-go exactly as
stated. The bounded $M=40$ calculation has label **experiment**; it refutes
only the unrestricted inference from primary completeness to joint
completeness.

## 7. Source and mathlib applicability

### literature-checked

Independent check date: **2026-08-13 UTC**.

The pinned Bourgain–Chang PDF was checked directly. At the start of Section
4 it defines “few prime factors” for
$q=\prod p_\alpha^{\nu_\alpha}$ by a uniform bound on
$\sum\nu_\alpha$. Corollary 4.5 assumes $t>q^\delta$ and
$\operatorname{ord}_p(\theta)>q^\delta$ for every $p\mid q$. The remark
following Theorem 4.7 explicitly says that the stronger prime-projection
condition remains necessary for a proper incomplete prefix. At
$q=3^EQ$, $\theta=10$, applicability fails twice: $E$ is unbounded and
$\operatorname{ord}_3(10)=1$.

The open 2007 Bourgain summary linked by the primary report was checked
directly. Item (2) under its “Remarks” states the arbitrary-modulus complete
subgroup result for $|H|>q^\varepsilon$; it concerns the entire subgroup,
not a $T$-term prefix of a larger joint orbit. The retrieved primary PDF had
SHA-256
905fb1c0a6b81a3861566533ad4e99b9f9660b5953e057cc017da3a06508979f.
The primary phrase “Remark 2” refers to this list item, not the earlier
separately numbered Remark 2; this is only a bibliographic-location
clarification.

The pinned Kerr paper states its sums for prime modulus $p$, base
$g\in\mathbb F_p^*$, and $N\le\operatorname{ord}_p(g)$. It does not treat
the growing synchronized CRT product in (TS9). Fisher's paper concerns
complete prime-power stationary-phase sums with multiplicative characters;
the elementary proof of (TS17) does not rely on it.

The local mathlib search confirms the listed generic infrastructure:

- Mathlib/Analysis/Fourier/ZMod.lean defines the DFT on ZMod and inversion;
- Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean contains finite
  character orthogonality;
- Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean contains primitive
  Dirichlet-character Gauss-sum identities.

No located declaration states the BBP-specific nonlinear pullback (TS10),
the sparse transform (TS17), or a bound for the selected actual complement
coefficient. This is a bounded applicability audit, not an exhaustive or
novelty claim.

## 8. Independent checker and retained output

The [independent checker](bbp_three_primary_twisted_sum_20260813_independent_check.py),
SHA-256
42c575e7d5446b46b26941c2c0db8b8289ae44846987f45a3e47beb0e12075be,
imports no code from the primary checker. It freezes the inputs, replays CRT
and grid identities, checks both Fourier sign conventions, exercises all
allowed small harmonic valuations including negative harmonics and $E=4$,
checks the restricted-norm constants and fixed periods, and reconstructs the
$M=40$ row from the four poles.

Retained output:

    status=PASS
    bounded_claim_label=experiment
    analytic_claim_label=proof sketch
    frozen_primary_report_sha256=0a7e6015782afdfa407242fe3e191cfffec414d7c9215ec8854a439c2fb08a12
    frozen_primary_checker_sha256=7d8a8f7ff85c02b251845ba781d373dbf222a87ba69e0d6f82b1e995b9315e2c
    crt_congruences=1320
    grid_points=3267
    window_bijections=15
    exact_phase_factors=351
    transform_sign_checks=9
    order_checks=12
    shift_congruences=54
    autocorrelation_cases=3276
    support_cases=19656
    harmonic_dft_cases=10224
    convolution_sign_checks=8
    restricted_norm_bounds=8
    periodic_weight_rows=20
    maximum_periodic_mass_over_log=0.142518204388
    depth=40
    upper_exponent=48
    row_length=9
    crt_row_checks=27
    seven_exponent=2
    order_49=42
    joint_order=126
    joint_prefix_is_complete=false
    full_denominator_base_is_unit=false
    adversarial_checks=9
    asserts_actual_complement_fourier_bound=false
    asserts_full_phase_cancellation=false
    asserts_fixed_sixteen_return=false
    asserts_v1=false

Reproduce from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_three_primary_twisted_sum_20260813_independent_check.py

Every bounded DFT and finite row in the checker has label **experiment**;
none is used as an all-depth proof.

## 9. Exact stopping point

The primary report correctly isolates the unresolved task as one selected
Fourier coefficient of the actual complement, equivalently a restricted
Fourier-algebra estimate. The sparse primary transform gives square-root
cancellation against low-complexity complements, but the BBP complement has
growing modulus and no established bound of that kind.

The audit therefore supports the report exactly at label **proof sketch**,
with the two wording clarifications above. It does not support a claim that
the selected coefficient is $o(1)$, the full phase is equidistributed, or V1
follows.

## 10. Coordination record

This audit registered descendant-area watch
ultrapi-twisted-audit-20260813 on local:pi-digits for agent
codex-ultrapi-twisted-audit. Its initial poll was empty at cursor and
delivered sequence 57,300, so no event was acknowledged. Observation events
are coordination signals only and were not used as mathematical evidence.
