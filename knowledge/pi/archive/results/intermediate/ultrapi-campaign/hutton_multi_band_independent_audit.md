# Independent audit: Hutton multi-band local coordinates

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

**PASS after four corrections to the research note.**  The generic local
coordinate, exact denominator-valuation dichotomy, (A_2) exceptional band,
fixed-depth radical squeeze, and weighted CRT decomposition form a coherent
`proof sketch`.  The supplied exact replay is an `experiment` and passed.
None of these statements proves a decimal-cylinder hit for pi, so V1 remains
a `conjecture`; this work is not a `candidate resolution`.

The audited artifact hashes are:

| Artifact | SHA-256 |
|---|---|
| [`hutton_multi_band_attack.md`](hutton_multi_band_attack.md) | `fe4c2325e178d0fa788b50cb360b7490bc09f400a50c9b2464efb7b8331b4d26` |
| [`hutton_multi_band_check.py`](hutton_multi_band_check.py) | `423007e81cbbe17ac19274fb9ce42eb35bfaa57bcb60f333690260936ccaecf2` |

The note's results are not yet generic `machine-checked` theorems.  The
concurrently developed T65 module covers the (n=2) band, but this audit does
not promote the generic identity or radical asymptotic on the strength of
that narrower module.

## Corrections made during review

1. Equation (23) originally asserted (log G\sim R) for the modulus (G)
   defined with a fixed depth (L).  That is false: the prime number theorem
   gives
   
   \[
   \log G=\left(1-\frac1{2L+1}\right)R+o(R).
   \]
   
   The coefficient approaches (1) only after the fixed-depth limiting
   argument.  The scale-ceiling comparison now uses the proved
   `proof sketch` consequence
   (log\operatorname{rad}(Q_K)\sim R).
2. The local theorem's opening hypotheses now include (p\le R), matching
   the proof and avoiding an implicit (A_0) convention.  The note also now
   says accurately that T64 is the full (n=1) band while T61 is its narrower
   upper-half subband.
3. Three literature citations had incorrect abbreviated authorships.  They
   were corrected to Franc--Gannon--Mason, Wituła--Hetmaniok--Słota, and
   Amdeberhan--Medina--Moll.  The linked works are only nearby context, not
   sources for the new formulas.
4. The repository paragraph now distinguishes a pre-existing generic theorem
   from the concurrently developed T65 (n=2) module.

No change to the checker was needed.

## 1. Generic local residue

Let (R=4K+3), let (p>7) be prime, and assume (p\le R<p^2).  Put
(q=\lfloor R/p\rfloor).  Then (q<p).  Because both (p) and every
Hutton exponent are odd, the exponents divisible by (p) are exactly

\[
r=cp,\qquad c\in\{1,3,\ldots,q\}.
\]

For these terms, (c<p), so (v_p(cp)=1).  Every other term is
(p)-integral.  Fermat's congruence (a^p\equiv a\pmod p), together with
(chi_4(cp)=\chi_4(c)\chi_4(p)), gives

\[
p\,\chi_4(cp)\left(\frac8{cp3^{cp}}+\frac4{cp7^{cp}}\right)
\equiv
\chi_4(p)\frac{\chi_4(c)}c
\left(\frac8{3^c}+\frac4{7^c}\right)\pmod p.
\]

There are (n=\lfloor(q+1)/2\rfloor) such odd multipliers.  Their sum is
exactly (chi_4(p)A_n), while multiplying every regular term by (p)
makes its residue zero.  All denominators in (A_n) are (p)-units because
their odd linear factors are at most (q<p), and (p>7).  This verifies

\[
pH_K\equiv\chi_4(p)A_n\pmod p.
\]

This derivation uses no assumption about decimal digits and no finite
experiment.

## 2. Exact valuation dichotomy

The singular and regular terms show (v_p(H_K)\ge-1), so (pH_K) is
(p)-integral.  Its residue is nonzero precisely when
(p\nmid\operatorname{num}(A_n)).  Hence

\[
v_p(H_K)=
\begin{cases}
-1,&p\nmid\operatorname{num}(A_n),\\
\ge0,&p\mid\operatorname{num}(A_n).
\end{cases}
\]

For (H_K=P_K/Q_K) in lowest terms, these cases say respectively that the
exponent of (p) in (Q_K) is exactly one or exactly zero.  The zero-residue
case is therefore genuine absence from the reduced denominator, not merely
failure of the survival argument.

## 3. The (A_2) band and exception

Independent rational arithmetic reproduced

\[
A_1=\frac{68}{21},\qquad
A_2=\frac{87112}{27783}
=\frac{2^3\cdot10889}{3^4\,7^3}.
\]

Independent trial division through (lfloor\sqrt{10889}\rfloor=104)
confirmed that (10889) is prime.  Under (3p\le R<5p), one has
(q\in\{3,4\}), hence (n=2); also (5p<p^2) because (p>7).  It follows
that all primes in this band survive exactly once except (10889), which is
absent.  The endpoint witness is arithmetically admissible:

\[
3\cdot10889=32667=4\cdot8166+3<10889^2.
\]

The alternative combined numerator was independently expanded as

\[
24\,3^{2p}7^{3p}+12\,3^{3p}7^{2p}-8\,7^{3p}-4\,3^{3p},
\]

and Fermat reduction gives the integer residue (87112), which vanishes
exactly at the displayed exceptional prime among primes above (7).

The first five factorizations in the note were also reproduced independently:

| (n) | factorization of (operatorname{num}(A_n)) |
|---:|---|
| 1 | (2^2\cdot17) |
| 2 | (2^3\cdot10889) |
| 3 | (2^2\cdot13\cdot1233899) |
| 4 | (2^4\cdot12377338601) |
| 5 | (2^2\cdot67\cdot15683\cdot26716073) |

## 4. Fixed-depth threshold and radical asymptotic

For each fixed (L), every (A_n) with (1\le n\le L) is positive: in
each of the base-(3) and base-(7) sums, consecutive alternating terms
have strictly decreasing magnitude and positive pair sums.  Thus the finite
bound

\[
X_L=\max\left(7,2L+1,
\max_{1\le n\le L}|\operatorname{num}(A_n)|\right)
\]

is valid.  If (R>(2L+1)X_L) and
(R/(2L+1)<p\le R), then (p>X_L), (R<p^2), and the corresponding prefix
index lies in ([1,L]).  Therefore (p) cannot divide its fixed nonzero
prefix numerator, and it occurs once in (Q_K).  This yields

\[
\vartheta(R)-\vartheta(R/(2L+1))
\le\log\operatorname{rad}(Q_K).
\]

Conversely, a common denominator for the Hutton sum divides

\[
3^R7^R\operatorname{lcm}\{r\le R:r\text{ odd}\},
\]

so every prime in the reduced denominator is at most (R), and
(log\operatorname{rad}(Q_K)\le\vartheta(R)).  For each fixed (L), the
prime number theorem gives the lower limiting ratio
(1-1/(2L+1)).  Given an arbitrary error tolerance, first choose fixed (L)
large enough and then let (K\to\infty).  This correctly proves

\[
\log\operatorname{rad}(Q_K)=R+o(R).
\]

No estimate uniform in (n) is smuggled into this two-stage limit.

## 5. Weighted CRT identity

For fixed (L) beyond its threshold, every prime in
(G=\prod_{R/(2L+1)<p\le R}p) has exact exponent one in (Q_K).  Therefore
(Q_K=CG) with (gcd(C,G)=1).  If (B) is the least common multiple of the
first (L) prefix denominators and (a_n=BA_n), then (gcd(B,G)=1).

Modulo a prime (p\mid G), the local residue becomes

\[
BP_K\equiv C\,\chi_4(p)a_{n(p)}\frac Gp\pmod p.
\]

All other terms in the proposed CRT sum contain (p), so the primewise
congruences combine to

\[
BP_K\equiv C\sum_{p\mid G}\chi_4(p)a_{n(p)}\frac Gp\pmod G.
\]

Writing the difference as (TG) and dividing by (BCG) gives exactly

\[
H_K=\sum_{p\mid G}\frac{\chi_4(p)A_{n(p)}}p+\frac{T}{BC}.
\]

For fixed (L), the prime number theorem in the two reduced residue classes
modulo (4), followed by partial summation on each fixed multiplicative
band, does give an (o(1)) weighted reciprocal phase.  It does not give the
exponential accuracy needed after a shift (s=\Theta(R)).  After correction,
the note also compares the maximal radical scale
(log_{10}\operatorname{rad}(Q_K)\sim R/\log 10) with the larger Hutton
transfer scale (R\log_{10}3).  The residual natural-log gap is
((\log3-1)R>0).  The stated selected-numerator/primary-coordinate barrier is
therefore real.

## 6. Computational replay

The submitted checker was run directly and ended with `all exact checks
passed`.  Its reported counts matched the note:

```text
generic local-coordinate assertions: 102404
generic exact-valuation assertions: 51202
one-fifth-band assertions: 7449
weighted CRT/decomposition assertions: 60
```

I also ran a separate implementation that did not import the submitted
checker.  It verified:

```text
independent local identities 5432 valuation iff 5432
A2/F2/exception 87112/27783 87112 32667
independent CRT identities 20
independent radical rows [(43, 12, 0.781016542),
                          (123, 29, 0.864850872),
                          (243, 52, 0.929631111),
                          (483, 91, 0.942575533)]
```

The exact checks corroborate the algebra but remain an `experiment`; the
PNT argument, not the finite ratios, is what supports the radical asymptotic
at `proof sketch` level.

## 7. Sources, labels, and limitations

- The immutable local target hash was rechecked.  It has no external source
  URL, and the note invents none.
- Metadata for the three nearby references was checked against the linked
  records.  Their topics are adjacent, but none was used as a source for the
  local congruence or radical squeeze.  This bounded search is not enough to
  establish novelty, so no `literature-checked` label is assigned.
- The note consistently calls the generic mathematics a `proof sketch` and
  finite replay an `experiment`.  It explicitly leaves V1 a `conjecture`.
- Denominator support does not localize the actual reduced numerator in a
  decimal cylinder.  The CRT remainder and weighted phase are precisely the
  unresolved information, and the prime-support modulus is exponentially too
  short for the full Hutton transfer window.

Final audit status: the corrected note is a strong, inspectable `proof
sketch` advance in Hutton-denominator structure, with no complete proof of
V1 and no claim-status promotion.
