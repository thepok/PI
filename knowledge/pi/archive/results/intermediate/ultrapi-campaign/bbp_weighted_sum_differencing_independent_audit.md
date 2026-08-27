# Independent audit of the BBP weighted-sum differencing branch

Audit date: **2026-08-12 UTC**

Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Canonical target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

The immutable local target records no external source URL, so none is
invented here.

Audited report:
[`bbp_weighted_sum_differencing_attack.md`](bbp_weighted_sum_differencing_attack.md),
SHA-256
`33fe8e27130e7ed4acfb8b9ee017cb17df2a612a1a4674b5d5ccef88c4404713`.

Primary checker SHA-256:
`70a4ca42b1bd2c6ec212587662ab667b8c1940a3a95d94b03a1f054ba71066bc`.

Self-audit SHA-256:
`e4a88f502f710165d06faa2926d654ff5020cae9570acd01c680e3774f4a073d`.

Self-audit checker SHA-256:
`39665d0cc03870755e0a3b9f3ab84fb727d128c22bdcd9f51d35804f4b4bf512`.

Parent BBP quotient report SHA-256:
`d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`.

Independent checker SHA-256:
`b348e090a0d85e77623af99d73fe22222de1e91a494dfb211402025961790b71`.

## Verdict and claim boundary

**PASS of the corrected report.**  I reconstructed the collapse, transfer
constant, endpoint recursion, finite-difference hierarchy, additive CRT,
both selector constructions, and their reducedness arguments without using
either earlier checker.  I found no further mathematical correction after
the endpoint correction already recorded by the self-audit.

The report's new results retain status `proof sketch`.  Its finite checks and
the independent checker have status `experiment`.  The dated source search
recorded in the primary report has status `literature-checked`.  The cited
T13 and T26 dependencies have status `machine-checked`; this audit inspected
their pinned declarations but adds no new formal theorem.  This agent audit
is not independent domain-expert review.

Most importantly, the branch proves no weighted cancellation, Fourier
limit, fixed-sixteen return, or canonical V1.  V1 remains a `conjecture`.
Nothing here is a `candidate resolution` or `verified resolution`.

## 1. Exact weighted-sum collapse and transfer constant

Put

\[
 A_n=\frac{10^n-16}{16},\qquad
 L_M=\lfloor(\log_{10}16)M\rfloor,
\]

and retain the parent's exact decomposition

\[
 16B_M=\frac{w_M}{D_M}+\frac{c_M}{R_M},\qquad
 \frac{c_M}{R_M}\equiv
 \Xi_M+\frac{\eta_M}{C_M}\pmod 1.
\]

For every integer row index, multiplication inside the character is valid
because \(A_n\) is an integer.  Thus

\[
\begin{aligned}
 e(hA_n(w_M/D_M+\Xi_M))e(hA_n\eta_M/C_M)
 &=e(hA_n16B_M)\\
 &=e(h(10^n-16)B_M).
\end{aligned}
\]

There is no omitted local factor and no dependence on a choice of CRT
representatives.

For \(k\ge1\), the four-pole coefficient obeys \(0<a(k)<k^{-2}\).  After
putting the coefficient over its displayed denominator, the numerator of
\(k^{-2}-a(k)\), apart from positive denominator factors, is

\[
 392k^4+873k^3+665k^2+194k+15>0.
\]

Consequently the positive BBP tail satisfies

\[
 0<\pi-B_M
 \le \frac1{(M+1)^2}\sum_{k=M+1}^{\infty}16^{-k}
 =\frac{16^{-M}}{15(M+1)^2}.
\]

For \(M\le n\le L_M\), \(10^n\le16^M\), hence

\[
 0\le(10^n-16)(\pi-B_M)\le\frac1{15(M+1)^2}.
\]

The chord inequality \(|e(x)-e(y)|\le2\pi|x-y|\), followed by averaging,
therefore gives exactly

\[
 \left|
 \frac{\mathcal S_{M,h}}{T_M}
 -e(-16h\pi)\frac{\mathcal W_{M,h}}{T_M}
 \right|
 \le\frac{2\pi|h|}{15(M+1)^2}.
\]

No factor \(T_M\) is missing on the right: it cancels upon normalization.
For each fixed \(h\) and any chosen unbounded common sequence of depths, one
normalized sum tends to zero if and only if the other does.  This is an
equivalence of two still-unproved limits, not an estimate of either sum.

## 2. All-depth cancellation versus the required subsequence

The report's normality distinction is correct after the self-audited
endpoint repair.  Let

\[
 P_h(N)=\sum_{0\le n<N}e(h10^n\pi).
\]

Cancellation on every proportional row means

\[
 P_h(L_M+1)-P_h(M)=o(M)\qquad(M\to\infty).
\]

Given a large endpoint \(N\), choose

\[
 M=\left\lceil\frac{N-1}{\log_{10}16}\right\rceil.
\]

Since \(1<\log_{10}16<2\), exact floor arithmetic gives

\[
 L_M+1\in\{N,N+1\}.
\]

Thus

\[
 P_h(N)=P_h(M)+o(M)+O(1),
 \qquad M=\frac{N}{\log_{10}16}+O(1).
\]

Iteration produces a geometric sequence of smaller endpoints.  For any
\(\varepsilon>0\), all sufficiently large row errors are at most
\(\varepsilon M\); the geometric sum of their depths is \(O(\varepsilon N)\),
endpoint discrepancies contribute only \(O(\log N)\), and the terminal
finite segment is \(o(N)\).  Hence \(P_h(N)=o(N)\).  The reverse implication
follows immediately by subtracting two global partial sums.  Applying Weyl's
criterion for every nonzero integer \(h\) shows:

\[
 \boxed{\text{cancellation through all depths is equivalent to base-10
 normality.}}
\]

The parent's equation (43) asks instead for cancellation along one common
unbounded subsequence of depths.  That condition would give Haar limits for
those selected finite rows and is sufficient for a return, but it does not
assert normality.  The report proves neither the all-depth nor subsequence
condition.

## 3. Finite differencing closes on the missing family

For

\[
 f(n)=h(10^n-16)B_M,
\]

the convention \(\Delta_rf(n)=f(n+r)-f(n)\) gives

\[
 \Delta_rf(n)=h(10^r-1)10^nB_M.
\]

Direct subset expansion, or induction, gives for arbitrary positive lags

\[
 \Delta_{r_k}\cdots\Delta_{r_1}f(n)
 =h10^nB_M\prod_{j=1}^k(10^{r_j}-1).
\]

At the first correlation level the exact range is
\(M\le n\le L_M-r\), and rewriting \(10^n\) as
\((10^n-16)+16\) contributes only the unit factor displayed in the report.
Every subsequent step promotes the frequency again; no phase estimate is
created.

The nontermination statement also has the claimed scope.  In reduced form

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 K_M=4M-v_2(M+1),
\]

where \(P_M,R_M\) are odd.  Every \(10^r-1\) is odd, so for fixed nonzero
\(h\) and \(n\le L_M\), the residual dyadic denominator exponent is

\[
 K_M-n-v_2(h)\longrightarrow\infty.
\]

A further unit lag contributes the odd factor 9 and therefore cannot make
the derivative character constant on adjacent surviving indices.  This is
only a proof that polynomial-style differencing has no finite terminal base
case.  It supplies no cancellation.  The general geometric-phase identity
is already `machine-checked` in the pinned T13 declaration.

## 4. Exact CRT product, but no product of sums

Writing \(D_M=2^{K_M-4}\), additive CRT gives

\[
 e(hA_n16B_M)=e_{D_M}(hA_nw_M)
 \prod_{p\in\mathcal Q_M^\star}e_p(hA_n\widehat\gamma_{M,p})
 e_{C_M}(hA_n\eta_M).
\]

Reducedness is genuine: \(w_M\) is odd, \((c_M,R_M)=1\), the high primes
occur to exponent one on the pinned parent branch, and the cofactor is
coprime to their product.  The independent replay reconstructed these
coordinates directly from finite BBP truncations.

The CRT identity is pointwise.  A single integer \(n\) simultaneously
selects every local power \(10^n\), so summing follows one diagonal cyclic
orbit with period an lcm of local orders.  It does not introduce independent
local indices and therefore does not algebraically factor the short sum.
Moreover, the explicit high product has logarithm \((6+o(1))M\), while the
row has only \(O(M)\) terms.  Standard completion at square-root-in-modulus
scale is therefore not an estimate in the required range.  This is a precise
applicability boundary, not a theorem that every possible CRT method must
fail.

## 5. Full-odd-coordinate dyadic selector

Fix the actual \(R_M,c_M/R_M\), let \(r=v_2(M+1)\), and put

\[
 D=2^{4M-r-4},\qquad Q=2^{3M-r}.
\]

Then \(D/Q=2^{M-4}\), so \(Q\mid D\) for \(M\ge5\).  For an odd dyadic
coordinate \(w\), the starting seed is

\[
 \frac{10^M}{16}\left(\frac wD+\frac{c_M}{R_M}\right)
 \equiv\frac{5^Mw}{Q}+\frac{10^Mc_M}{16R_M}\pmod1.
\]

Multiplication by \(5^M\) permutes the odd residues modulo \(Q\).  These
residues have circular spacing \(2/Q\), so one class makes the seed lie
within \(1/Q\) of \(1/9\).  Among that class's representatives in
\([0,D)\), one lies within linear distance \(Q\) of the actual \(w_M\),
including when \(w_M\) is near either endpoint.

For this representative \(w'_M\), define

\[
 P'_M=R_Mw'_M+Dc_M,
 \qquad B'_M=\frac{P'_M}{16DR_M}.
\]

Oddness of \(w'_M\), together with \((c_M,R_M)=1\), gives the stronger
reducedness statement

\[
 (P'_M,16DR_M)=1.
\]

The whole odd quotient is unchanged, and

\[
 |B'_M-B_M|=\frac{|w'_M-w_M|}{16D}\le2^{-M}.
\]

If \(n=M+t\le L_M\), the fixed-point congruence
\(10^t/9\equiv1/9\pmod1\) and the seed bound give

\[
 \left\|\frac{10^n(16B'_M)}{16}-\frac19\right\|_{\mathbb T}
 \le\frac{10^t}{Q}
 \le\frac{2^r}{5^M}
 \le\frac{M+1}{5^M}.
\]

Since \(A_n16B'_M=10^n(16B'_M)/16-16B'_M\), the chord inequality yields
the report's exact normalized bound

\[
 \left|
 \frac1{T_M}\sum_{n=M}^{L_M}e(hA_n16B'_M)
 -e\!\left(h\left(\frac19-16B'_M\right)\right)
 \right|
 \le\frac{2\pi|h|(M+1)}{5^M}.
\]

Thus the alternative row average has magnitude tending to one for every
fixed \(h\).  The construction fixes all actual odd CRT information but
changes the dyadic carry and does not satisfy the four-pole cross-depth
recurrence.  It therefore rules out bounds uniform over that discarded
carry; it is not a counterexample or model for the actual BBP row.

## 6. Coarse-coordinate selector

Let \(S\) be any squarefree product of primes greater than 3 with prescribed
nonzero additive coordinates, and let \(\Xi\) be their additive CRT sum.
Choose

\[
 C=3^a,\qquad a=\min\{j:3^j\ge(M+1)^3\}.
\]

Then \(C<3(M+1)^3\), \(P^+(C)=3\), and \(\log C=O(\log M)\).  If
\(b=\lfloor\log_3(8M+5)\rfloor\), then
\(3^b>(8M+5)/3>2M\), and \((2M)^4\ge(M+1)^3\) for the stated range.  Hence
\(a\le4b\), exactly the fixed-prime exponent allowance used by the parent.

The residues coprime to 6 have cyclic gaps at most four.  Since \(DC\) is a
multiple of 6, there is a numerator \(t\) coprime to 6 such that

\[
 \left\|\Xi+\frac{t}{DC}-\frac13\right\|_{\mathbb T}
 \le\frac2{DC}.
\]

Set

\[
 w\equiv tC^{-1}\pmod D,qquad
 \eta\equiv tD^{-1}\pmod C.
\]

Then \(w\) is odd, \(\eta\) is a unit modulo \(C\), and
\(w/D+\eta/C\equiv t/(DC)\pmod1\).  Additive CRT reconstructs a numerator
\(c\) coprime to \(R=SC\), preserving every prescribed coordinate and the
cofactor coordinate \(\eta\).  The full numerator \(Rw+Dc\) is coprime to
\(16DR\).

Finally \(3\mid A_n\), and

\[
 \frac{2A_{L_M}}{DC}
 <\frac{2^{r+1}}C
 \le\frac2{(M+1)^2}.
\]

This proves the claimed phase and chord bounds

\[
 \|A_n(\Xi+w/D+\eta/C)\|_{\mathbb T}
 \le\frac2{(M+1)^2},
\]

\[
 \left|\frac1{T_M}\sum_{n=M}^{L_M}
 e(hA_n(\Xi+w/D+\eta/C))-1\right|
 \le\frac{4\pi|h|}{(M+1)^2}.
\]

This second selector can preserve the actual high-prime coordinate list and
all stated cofactor size/support restrictions, but it selects both unresolved
coordinates and again violates the actual carry recurrence.  Its conclusion
is a barrier to coarse-data estimates only.

## 7. Independent exact replay

The companion
[`bbp_weighted_sum_differencing_independent_check.py`](bbp_weighted_sum_differencing_independent_check.py)
imports neither earlier checker.  It uses exact integer and rational
arithmetic for all theorem-facing checks.  It deliberately includes exact
row floors, every legal first-correlation boundary in its test window,
dyadic carry endpoints, cyclic selector seams, arbitrary reduced odd
quotients, actual finite BBP CRT rows, and an exhaustive finite audit of the
mod-six covering lemma.

Run from the repository root:

```bash
python -m py_compile \
  work/ultrapi-resume/bbp_weighted_sum_differencing_independent_check.py
python work/ultrapi-resume/bbp_weighted_sum_differencing_independent_check.py
```

The retained run returned `PASS` after **17,762** exact checks:

```text
coefficient and majorant checks: 641
row-collapse checks: 995
finite-tail checks: 995
inverse-normality-endpoint checks: 1993
iterated-difference checks: 3000
correlation-boundary checks: 1806
actual-CRT-coordinate checks: 745
dyadic-exactness checks: 1104
full-odd-coordinate-selector checks: 3495
mod-six-covering checks: 1840
coarse-coordinate-selector checks: 1148
asserts_weighted_cancellation: false
asserts_normality: false
asserts_fixed_return: false
asserts_v1: false
```

Finite computations remain `experiment`; they support the hand proofs above
but cannot establish any limiting statement.

## Final boundary

The corrected report survives independent audit.  It sharply identifies why
the current quotient localization does not yet solve the problem: its
weighted sum is the actual proportional decimal Weyl block of pi up to an
explicit \(O_h(M^{-2})\) normalized error; finite differencing only changes
frequency; and all odd CRT data can coexist with resonant rows if the actual
dyadic carry is discarded.  Coarse cofactor information can likewise
coexist with resonance if the actual residue is discarded.

The only remaining version of this route must control the simultaneous
actual carry and cofactor residue through the four-pole recurrence, or replace
all-frequency cancellation with a genuinely weaker cylinder-hitting method.
No such control is present here.  V1 remains a `conjecture`.
