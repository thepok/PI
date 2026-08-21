# Independent audit: finite-type avoidance and \(\operatorname{Log}(-1)\)

Audit date: **2026-08-12 UTC**  
Verdict: **PASS after corrections**, at the stated labels only  
Audited report: `subshift_log_algebraic_bridge.md`  
Report SHA-256:
`b4e4fb05397f75e1e4af7bbd6d4d32e80d489893fead9773de51a57a28aca896`  
Independent checker: `subshift_log_algebraic_bridge_check.py`  
Checker SHA-256:
`3e5c325ee6eead178a085804d2c399190f948e56e5b379e68a2e4f10cc6db118`

This is an independent audit of a `literature-checked` bounded search and
local `proof sketch` reductions.  It is not `machine-checked`, a candidate
resolution, or a proof of V1.  In particular, the audit confirms the negative
verdict: the branch isolates an obstruction but does not prove that every
finite decimal word occurs in \(\pi\).

## Corrections made during review

The report was edited directly to correct or delimit the following points.

1. “One-word survivor” was replaced by “single-forbidden-word survivor” to
   remove an ambiguity about the length of the forbidden word.
2. The repetition ledger now states the direction of the pigeonhole estimate
   correctly.  It guarantees exponent \(1+L/M_L\) in the displayed
   **unreduced** denominator; because \(M_L\geq9^L\), that weak guaranteed
   exponent is at most \(1+L/9^L\).  This does not exclude favorable
   denominator cancellation for a special path.
3. The overlapping-period argument now records the harmless all-nine
   alternative expansion.  The repeating representation may be noncanonical,
   but its rational value and the \(10^{-(j+L)}\) error bound are unchanged.
4. The Adamczewski--Faverjon alternative was restricted to the actual
   hypotheses: an algebraic point inside the unit disk at which the Mahler
   function has no pole, with the algebraic alternative lying in the stated
   coefficient field.
5. The Thue--Morse separator now explicitly handles decimal nonuniqueness:
   its digit word is not eventually constant, so allowing digit nine does not
   create an ambiguous eventually-nine tail.
6. The Euler-tail display's missing `\\leq` was fixed, and “nonvanishing
   scale” was replaced by the accurate “first-order normalized scale.”
7. The transfer of Cijsouw's measure from \(i\pi\) to \(\pi\) is now written
   out, including degree and height.  Its domain is correctly stated as
   nonconstant integer polynomials.
8. The auxiliary-polynomial conclusion was narrowed to the direct product
   scheme actually audited.  The report no longer suggests that the ledger
   rules out every possible growing-degree construction.

## Mathematical re-derivation

### Statement, cylinders, and entropy

The normalized quantifiers allow leading zeros.  For a word \(w\) of length
\(m\), omission is exactly membership in the one-sided SFT \(X_w\), or
equivalently \(\{10^n\pi\}\notin I_w\) for every \(n\geq0\).  Decimal endpoint
ambiguity is absent for \(\pi\), which is irrational.

Choosing any digit \(c\) in \(w\) embeds the full shift on the other nine
digits in \(X_w\), giving \(9^L\leq |\mathcal L_L(w)|\).  If
\(L=qm+r\), each of the \(q\) aligned length-\(m\) blocks has at most
\(10^m-1\) choices, giving

\[
 |\mathcal L_L(w)|\leq10^r(10^m-1)^q.
\]

Taking logarithmic growth rates proves the displayed entropy interval.  If a
single infinite word misses \(w\), its factor language lies inside
\(\mathcal L_L(w)\), so its factor entropy is strictly below \(\log 10\).
Conversely, a word containing every finite decimal word has complexity
exactly \(10^L\) at every length.  Thus the report's entropy equivalence is
correct.

### Repetition and approximation ledger

Among the \(M_L+1\) legal length-\(L\) factors starting at positions
\(0,\ldots,M_L\), choose equal factors at \(i<j\), and set \(r=j-i\).
The decimal with preperiod \(U=d_1\cdots d_i\) and repeated block
\(B=d_{i+1}\cdots d_j\) has value

\[
 y_L=\frac{[U]}{10^i}+\frac{[B]}{10^i(10^r-1)}.
\]

If \(r>L\), equality of the two factors directly verifies the next \(L\)
digits.  If \(r\leq L\), equality gives
\(d_{i+r+s}=d_{i+s}\) for \(1\leq s\leq L-r\); iteration gives precisely the
needed periodicity through position \(j+L\).  Hence

\[
 |\theta-y_L|\leq10^{-(j+L)},\qquad
 Q_L=10^i(10^r-1)<10^j.
\]

Therefore the unreduced-denominator exponent is
\(1+L/j\geq1+L/M_L\).  The lower bound \(M_L\geq9^L\) shows why this
uniformly guaranteed threshold tends to one.  A de Bruijn word on the
nine-symbol subsystem has \(9^L\) distinct cyclic length-\(L\) windows; after
its first \(L-1\) wraparound digits it can be extended by a non-eventually
periodic legal tail.  This gives an irrational legal path whose first repeated
length-\(L\) block is delayed to at least exponential scale.  It validates the
claimed separator against any recurrence theorem based on SFT membership
alone.

The caveat is material: reduction of \(Q_L\) can improve a particular
approximation.  Neither the report nor this audit claims a uniform lower
bound on that gcd, so this is an exponent ledger, not a proof that every
repetition-based attack fails.

### Thue--Morse separator for arbitrary \(w\)

Take \(c\) to be, for example, the first digit of \(w\), including when it is
zero, and take any two distinct digits \(a<b\) different from \(c\).  Since

\[
 \frac a9=\sum_{n\geq0}a10^{-n-1},
\]

the number
\(\eta_w=a/9+(b-a)\sum t_n10^{-n-1}\) has termwise digits \(a\) or \(b\),
with no carry.  Every digit omits \(c\), so the whole word \(w\) is absent,
regardless of its other digits or leading zeros.

Splitting the generating series into even and odd indices re-derives

\[
 T(z)=T(z^2)+\frac{z}{1-z^2}-zT(z^2)
     =(1-z)T(z^2)+\frac{z}{1-z^2}.
\]

For completeness, non-eventual-periodicity has an elementary check.  If
\(p\) were an eventual period, choose arbitrarily large \(k\) of both
parities with \(2^k>p\).  Periodicity at \(2^k-p\) would require
\(t_{2^k-p}=t_{2^k}=1\).  But the low \(k\) bits of \(2^k-p\) are the bitwise
complement of \(p-1\), so
\(t_{2^k-p}\equiv k-t_{p-1}\pmod2\), which flips when the parity of \(k\)
flips.  Contradiction.

Bugeaud's theorem applies to
\(S_{10}=\sum t_n10^{-n}\), while
\(\eta_w=a/9+(b-a)S_{10}/10\).  Irrationality exponent is invariant under a
nonconstant rational affine map: rational approximants transport in both
directions with denominators changed by only fixed factors.  Thus
\(\mu(\eta_w)=2\).  The decimal word is 2-automatic and has factor complexity
\(O(L)\); Adamczewski--Bugeaud Theorem 1 (or their automatic-number Theorem
2) then gives transcendence because the word is not eventually periodic.

For Fishman's Corollary 3, use the nine similarities
\(x\mapsto(x+d)/10\), \(d\ne c\).  They satisfy the open set condition and,
because there are distinct translations, form an irreducible family in
dimension one.  Hence badly approximable points have full relative dimension
in this Cantor set.  Badly approximable irrational numbers have
irrationality exponent two, and removing the countable algebraic set leaves
transcendental examples.  This independently confirms the report's broader
separator.

### Euler-tail and polynomial ledgers

From \(q_n\pi=p_n+x_n\) and \(e^{i\pi}=-1\),

\[
 e^{ip_n/q_n}+1=1-e^{-ix_n/q_n},
\]

so \(|1-e^{-it}|\leq t\) gives (17), and Taylor expansion gives
\(q_n(1-e^{-ix_n/q_n})=ix_n+O(q_n^{-1})\).  The normalized coefficient is
exactly the original decimal tail, so no independent cylinder estimate is
created.

For \(F(Z)=Z(1-Z)\), direct expansion gives

\[
 F(tX-A)=-t^2X^2+t(1+2A)X-A(1+A).
\]

Using \(0<A<4t\), its coefficient \(\ell^1\)-norm is at most \(30t^2\).
Multiplication over \(t=10^n\), \(1\leq n\leq N\), gives exactly degree
\(2N\), height at most \(30^N10^{N(N+1)}\), and
\(0<P_N(\pi)\leq4^{-N}\).

The Cijsouw transfer was checked without invoking a direct \(\pi\) theorem.
For integer \(P\),

\[
 Q(Y)=P(-iY)P(iY)\in\mathbb Z[Y],\quad
 \deg Q\leq2D,\quad H(Q)\leq(D+1)H^2,
\]

and \(Q(i\pi)=P(\pi)P(-\pi)\).  The elementary upper bound on
\(|P(-\pi)|\) absorbs the second factor into Cijsouw's effective constant.
Since
\(\log H(P_N)\leq N\log30+N(N+1)\log10\leq9N^2\), the theorem's exponent is
bounded by a constant times

\[
 (2N)^2(2N+9N^2)(1+\log(2N))^2
 \leq44N^4(1+\log(2N))^2.
\]

That lower bound is fully compatible with the universal \(4^{-N}\) upper
bound.  The ledger is therefore correct and does not establish V1.

## Primary-source audit

On 2026-08-12 UTC I independently fetched and hashed the eleven available
Numdam/arXiv PDFs and rehashed the pinned final Springer PDF.  Every one of
the twelve hashes agrees with the report.  The Cijsouw theorem statement,
the Bugeaud main theorem, Fishman Corollary 3, Adamczewski--Faverjon
Corollary 1.8, the 2026 Mahler-value Theorems 1.1--1.2 and Corollary 5.2,
Nguyen Theorems A--B, and the Fischler--Rivoal simple-zero consequence were
checked in the pinned texts.

The source/derivation boundary is as follows.

- **Sourced:** Cijsouw's degree--height measure; automatic-number
  transcendence/complexity; Bugeaud's exact Thue--Morse irrationality
  exponent; Fishman's relative-dimension theorem; the two Mahler-value
  alternatives/measures; Fischler--Rivoal's E-function-zero measure;
  Nguyen's recurrence hypotheses; and the cited metric/complexity results.
- **Locally derived (`proof sketch`):** the SFT entropy bounds, overlap
  rational, explicit separator construction and Mahler identity, Euler-tail
  normalization, both polynomial ledgers, the Cijsouw transfer to \(P(\pi)\),
  and all applicability comparisons.
- **Bounded negative search only:** no theorem excluding an algebraic
  logarithm from every proper decimal SFT was located.  This is not a claim
  of exhaustive literature coverage.

The known bound \(\mu(\pi)\leq7.10321\) recorded by Bugeaud--Kim is indeed
outside their nontrivial ranges (below approximately \(2.324\), and below
\(2.2\) in the companion refinement).  Moreover, those theorems provide
linear lower bounds for factor complexity, far short of the \(10^m\) factor
coverage required here.

## Reproducibility

Run:

```text
python work/ultrapi-resume/subshift_log_algebraic_bridge_check.py
```

Independent result:

```text
PASS: 553,628 exact finite assertions
```

The checker exhausts every decimal forbidden word of length at most four for
the finite entropy and Thue--Morse separator tests; checks overlap cases over
an alphabet containing zero and nine; verifies de Bruijn, Mahler, Euler,
polynomial-height, and Gaussian Cijsouw-transfer identities; checks the
canonical source SHA; and ensures all twelve literature pins remain in the
report.  These finite checks are `experiment` evidence for the local algebra,
not a proof of the asymptotic or literature theorems.

## Final disposition

The corrected branch is internally sound at its declared levels:
`literature-checked` for the bounded source audit and `proof sketch` for the
local reductions.  It establishes a meaningful obstruction and a sharp
separator, but no unconditional digit-occurrence theorem.  V1 remains a
`conjecture`.
