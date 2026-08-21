# T85: adversarial audit of T79's least-valuation step

Date: 2026-08-09 UTC.

Status: `proof sketch` with a self-contained exact-arithmetic replay. This note
corrects an unverified step in the T79 note. It proves no normality,
equidistribution, C1, C2, or canonical near-return estimate for pi. The
universal algebra below is an informal proof; finite replay checks illustrate
and falsify claims but are not proofs of universal statements.

## 1. Scope, normalization, and quantifiers

`canonical_statement.txt` is a byte-exact copy of the immutable statement and
has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical target remains

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\},
\]

with ordered pairs and the diagonal included, and with quantifiers

\[
 \forall A\ge1\ \exists n_0\ \forall n\ge n_0\ \exists N\ge1.
\]

The recorded ambiguities matter here: changing to infinitely many `n`, fixing
`A`, prescribing `N`, deleting diagonals, changing base, or replacing circle
distance gives a different or weaker problem. T85 changes none of them. It
audits only a rational-transfer heuristic aimed at T10, which is itself only a
sufficient strategy for the canonical question.

## 2. Exact T79 assertion under audit

Let

\[
 P=147153121,\qquad B=1758719,\qquad E=2K-1,
\]

and write T79's partial sum as

\[
 S_E=\sum_{\substack{1\le e\le E\\e\equiv1\pmod 2}}
 \left(\frac{32(-1)^{(e-1)/2}}{e10^e}
 -\frac{4(-1)^{(e-1)/2}B^e}{eP^e}\right)=\frac{p_E}{q_E}
\tag{2.1}
\]

in lowest terms with `q_E>0`. Abrarov--Quine supply the general Machin-like
identity, not this valuation analysis; see `SOURCE_PINS.md`.

The exact passage in the delivered `prior-t79-REPORT.md`, Section 5, is:

> For \(2K-1<P\), the second summand with \(r=K-1\) in (3.5) has
> \(P\)-adic valuation \(-(2K-1)\). Every earlier second summand has valuation
> at least \(-(2K-3)\), and every first summand has nonnegative \(P\)-adic
> valuation. The minimum is unique, so
> \[
> v_P(q_K)=2K-1,\qquad m_K\ge P^{2K-1}.
> \]

This quote includes the essential range `E<P`. The argument is correct in that
range. It is not valid without that range because an odd coefficient `e` can
itself contain powers of `P`.

## 3. Tie-complete least-valuation lemma

For an odd prime `p`, a `p`-adic unit `b`, and odd `e`, define the second-family
term

\[
 T_e=-\frac{4(-1)^{(e-1)/2}b^e}{e p^e}.
\]

Then

\[
 v_p(T_e)=-e-v_p(e).                                      \tag{3.1}
\]

Thus least valuation means maximizing

\[
 F_p(e)=e+v_p(e)                                          \tag{3.2}
\]

over odd `e<=E`. The following finite description includes every tie.

For each `a>=0` with `p^a<=E`, let `u_a` be the largest odd integer such that

\[
 u_a\le \left\lfloor E/p^a\right\rfloor,
 \qquad p\nmid u_a,
\]

and put

\[
 e_a=p^a u_a,\qquad M(E,p)=\max_a(e_a+a).                 \tag{3.3}
\]

Then the complete maximizing set is

\[
 \boxed{\mathcal T(E,p)=\{e_a:e_a+a=M(E,p)\}.}            \tag{3.4}
\]

**Proof.** On the class `v_p(e)=a`, equation (3.2) is `e+a`, strictly
increasing with `e`. Hence only the largest member `e_a` of that class can be a
global maximizer. Every odd `e` lies in exactly one such class. Taking the
maximum over the finitely many possible `a` proves (3.4). This also proves that
the replay's enumeration is exhaustive rather than a bounded search over `e`.

An equivalent local test is useful. If `t=v_p(E)` and `e=E-d` has
`a=v_p(e)`, then

\[
 F_p(e)-F_p(E)=a-t-d.                                    \tag{3.5}
\]

So `e` beats, ties, or loses to the terminal exponent according as `d` is less
than, equal to, or greater than `a-t`. Since both exponents are odd, `d` is
even. Two-term audits are not sufficient in general: Section 7 gives a
three-way tie.

### Cancellation criterion

For `e` in `mathcal T(E,p)`, write `a_e=v_p(e)` and `w_e=e/p^(a_e)`.
Multiplication of the second-family sum by `p^M` leaves, modulo `p`, exactly

\[
 R(E,p,b)=-4\sum_{e\in\mathcal T(E,p)}
 (-1)^{(e-1)/2}b^e w_e^{-1}\pmod p.                      \tag{3.6}
\]

All omitted second-family terms are divisible by `p` after this
normalization. If additionally `p` is coprime to 10, the first-family terms in
(2.1) have valuations at least `-floor(log_p E)`, strictly larger than `-M`
because `M>=E`. Therefore, for odd `p` with `p` not equal to 5,

\[
 R(E,p,b)\ne0\pmod p\quad\Longrightarrow\quad
 v_p(S_E)=-M(E,p),\quad v_p(q_E)=M(E,p).                 \tag{3.7}
\]

If `R=0`, the implication fails and the next `p`-adic layer must be computed.
This is the corrected replacement for any unrestricted "least term is unique"
step at primes coprime to 10. It is a finite exact test for every terminal `E`,
but it is not a claim that cancellation never occurs. At `p=5`, equations
(3.1)--(3.6) still classify the second-family layer, but first-family terms can
lie on that same layer and must be included. For example `p=5,b=4,E=1` makes
the two full summands `32/10` and `-16/5`, whose sum is zero; (3.7) is
deliberately not asserted there.

## 4. Corrected proof in T79's stated range

If `E<P`, every odd `e<=E` has `v_P(e)=0`; hence `F_P(e)=e`. The unique
maximizer is `e=E`, and (3.6) consists of one nonzero unit. Every first-family
term is `P`-integral because its denominator is `e10^e` with `e<P` and
`P` coprime to 10. Therefore

\[
 \boxed{E<P\Longrightarrow v_P(S_E)=-E,
        \quad v_P(q_E)=E.}                              \tag{4.1}
\]

Consequently the T79 note's displayed implication
`m_E>=P^E` is valid exactly where it was stated. The external tie objection
does not refute (4.1); it refutes an extension of its uniqueness argument past
`E<P`.

## 5. External reviewers' configuration `E=P^2+2`

Set

\[
 E=P^2+2=21654041020040643.
\]

Equations (3.3)--(3.4) give exactly two maximizers:

\[
 \mathcal T(E,P)=\{E,P^2\},\qquad
 F_P(E)=E,\quad F_P(P^2)=P^2+2=E.                       \tag{5.1}
\]

They are the only ones: below `P^2`, an exponent has `P`-valuation at most 1,
so its `F_P` value is at most `P^2-1`.

Because every odd square is 1 modulo 8, the two normalized residues in (3.6)
are

\[
 \rho_{P^2}\equiv-4B^{P^2}\equiv-4B=140118245\pmod P,
\]

\[
 \rho_E\equiv\frac{4B^{P^2+2}}{P^2+2}
 \equiv2B^3=57367864\pmod P.                            \tag{5.2}
\]

Here Fermat's theorem and `E=2 mod P` were used. Their sum is

\[
 R(E,P,B)\equiv2B(B^2-2),\qquad
 B^2\equiv81070662\pmod P,
\]

and exactly

\[
 \boxed{R(E,P,B)=50332988\not\equiv0\pmod P.}           \tag{5.3}
\]

Thus the reviewers correctly identified a tie and correctly predicted no
leading cancellation. The terminal term is not unique, but the denominator
conclusion survives:

\[
 \boxed{v_P(S_E)=-E,\qquad v_P(q_E)=E.}                 \tag{5.4}
\]

For comparison, at a formal `P^2+2` tie cancellation occurs exactly when
`b^2=2 mod p`. It actually occurs in the replayable case `p=7,b=3,E=51`.

## 6. Reduced denominator, transient, modulus, and orbit

Define

\[
 L_E=\operatorname{lcm}(1,3,\ldots,E),\qquad
 D_E=10^E P^E L_E,
\]

and let `A_E=D_E S_E`. Then the exact reduced denominator is

\[
 \boxed{q_E=D_E/\gcd(A_E,D_E).}                         \tag{6.1}
\]

Equation (6.1), rather than the unreduced `D_E`, is used throughout.

### Exact valuations at `P^2+2`

The terminal first-family term has 2-adic valuation `5-E`; it is uniquely
least because preceding first terms increase by at least 2 and every
second-family term has 2-adic valuation 2. Thus

\[
 v_2(q_E)=E-5=21654041020040638.                         \tag{6.2}
\]

For the prime 5, applying (3.3) to the first family shows that `e=E` is the
unique maximizer of `e+v_5(e)` and its normalized residue is `2 mod 5`.
Second-family terms have valuation only `-v_5(e)`. Hence

\[
 v_5(q_E)=E=21654041020040643.                           \tag{6.3}
\]

Together with (5.4),

\[
 a_E=v_2(q_E)=E-5,\quad b_E=v_5(q_E)=E,\quad
 t_E=\max(a_E,b_E)=E,                                   \tag{6.4}
\]

and

\[
 m_E=\frac{q_E}{2^{E-5}5^E},\qquad (m_E,10)=1,
 \qquad P^E\mid m_E.                                   \tag{6.5}
\]

Equations (6.1)--(6.5) exactly determine the 2-, 5-, and `P`-primary parts of
the reduced denominator and define the remaining cofactor without pretending
to evaluate it. They do **not** compute the complete reduced denominator: doing
so would require evaluating `gcd(A_E,D_E)` across all odd prime factors through
the roughly `E log_10(P)`-digit integer. The T79 data and the least-valuation
verdict do not determine that cofactor. This is a displayed obstruction to the
agenda's literal request for a numerical `q_E`, not a hidden occupancy
assumption.

### Multiplicative order

Trial division gives

\[
 P-1=2^5\cdot3\cdot5\cdot113\cdot2713,
 \qquad \operatorname{ord}_P(10)=12262760.              \tag{6.6}
\]

Exact modular exponentiation gives

\[
 \frac{10^{12262760}-1}{P}\equiv4247150\not\equiv0\pmod P.
\tag{6.7}
\]

The elementary prime-power lifting argument therefore yields, for every
`j>=1`,

\[
 \operatorname{ord}_{P^j}(10)=12262760\,P^{j-1}.         \tag{6.8}
\]

Writing `m_E=P^E r_E`, with `(P,r_E)=1`, the exact total order and its forced
component are

\[
 d_E=\operatorname{ord}_{m_E}(10)
 =\operatorname{lcm}\left(12262760P^{E-1},
                           \operatorname{ord}_{r_E}(10)\right).           \tag{6.9}
\]

Thus `12262760 P^(E-1)` divides `d_E`. Equation (6.9) computes the exact forced
prime-power order but leaves the total order conditional on the explicitly
unknown cofactor `r_E`. A numerical total orbit length cannot be recovered from
T79's least-valuation argument; claiming one without factoring `r_E` would be
an unsupported leap. The next subsection shows that this missing total order
cannot affect the transferred prefix because that prefix never reaches the
tail.

### Orbit and occupancy range

For `j=t_E+s`, reduction gives the same exact post-transient orbit formula as
T79:

\[
 \frac{p_E10^j}{q_E}\equiv
 \frac{p_E2^{t_E-a_E}5^{t_E-b_E}10^s}{m_E}\pmod1.       \tag{6.10}
\]

It has period `d_E`, distinct residues for `0<=s<d_E`, and for a tail of
length `H` its exact ordered equality count is

\[
 \sum_{r=0}^{d_E-1}c_r^2,\qquad
 c_r=\max\left(0,1+\left\lfloor\frac{H-1-r}{d_E}\right\rfloor\right).
\tag{6.11}
\]

But T79's transfer schedule is

\[
 N+n+4\le2K=E+1,
\]

so

\[
 N\le E-n-3<E=t_E.                                     \tag{6.12}
\]

Therefore the post-transient interval `[t_E,N)` is empty for every admissible
canonical prefix in this configuration. Its orbit occupancy is exactly zero;
none of the `N` transferred phases is governed by (6.9)--(6.11). This is a
stronger immediate obstruction than merely observing that the modulus is
large. The order calculation remains correct but acts outside the affected
prefix range.

## 7. Adversarial tie census

The universal census is (3.3)--(3.4). The replay includes the following cases
to exercise every distinct verdict rather than only the favorable T79 data.

| `p,b,E` | complete least layer | verdict and downstream arithmetic |
|---|---|---|
| T79 `P,B,E<P` | `{E}` | Corrected proof (4.1): `v_P(q_E)=E`. |
| T79 `P,B,P^2+2` | `{P^2,E}` | Nonzero residue `50332988`; `v_P(q_E)=E`, (6.2)--(6.12). |
| `3,1,11` | `{9,11}` | Nonzero residue `1 mod 3`; `q=6089428125000000`, `v_3(q)=11`, `v_2(q)=6`, `v_5(q)=11`, `t=11`, `m=1948617=3^11*11`, `ord_m(10)=39366`. A hypothetical 12-point tail has 12 distinct occupancies and 12 ordered equality collisions. |
| `7,3,51` | `{49,51}` | Leading residue cancels. Exact reduction gives `v_7(q)=50`, not 51. Here `v_2(q)=46`, `v_5(q)=51`, `t=51`; `m` and its full factorization/order are printed by the replay. This is an exact counterexample to inferring the denominator exponent from tied valuations without (3.6). |
| `3,*,29` | `{27}` | Strict reversal: `F_3(27)=30>F_3(29)=29`; the terminal term is not even least-valued. |
| `3,*,3^20+20` | `{E,E-2,E-20}` | Three-way tie with exact valuations `0,2,20`; pairwise tie checking is incomplete. |

For the cancelling `p=7` example, the exact reduced denominator is

```text
4443178576606349409975463081101373485514240886722103443946343750000000000000000000000000000000000000000000000
```

and the coprime modulus is

```text
142181714451403181119214818595243951536455708375107310206283
```

with exact order

```text
46801198881236085232621466691166760779943931120
```

These finite cases are exact counterexamples or checks of finite statements;
they are not evidence for a universal noncancellation theorem.

## 8. Corrected `N` versus `log q` frontier

There are three separate statements that T79 conflated.

### 8.1 Denominator-size arithmetic: derived

Whenever the tie audit gives `v_P(q_E)>=E`, one has `q_E>=P^E`. Conversely,
`q_E` divides `D_E=10^E P^E L_E`. An elementary Chebyshev argument gives
`log L_E=O(E)`: primes in `(x,2x]` divide the central binomial coefficient,
so dyadic summation gives `theta(x)=O(x)`; summing
`psi(E)=sum_(a>=1) theta(E^(1/a))` gives `psi(E)=O(E)`, and
`log lcm(1,...,E)=psi(E)`. Hence

\[
 E\log P\le\log q_E\le
 E(\log10+\log P)+O(E),
\]

or

\[
 \boxed{\log q_E=\Theta(E)}                             \tag{8.1}
\]

on every audited family with `v_P(q_E)>=E`. There is an unbounded safe family:
for `E=P^a`, the terminal exponent uniquely maximizes `e+v_P(e)`, so
`v_P(q_E)=E+a`.

At near-minimal transfer truncation, `E=Theta(N+n)`. In regimes where
`n=O(N)` and `N` is also a positive proportion of `E`, (8.1) gives

\[
 \boxed{N=\Theta(\log q_E).}                            \tag{8.2}
\]

This is a derived arithmetic scale, not a theorem from any cited paper. It is
also conditional on a specified scaling of `n,N,E`; the one-sided transfer
inequality alone permits arbitrary overshoot in `E` and does not imply
(8.2).

For the coprime modulus, `log m_E=Theta(E)` follows whenever the audit leaves a
non-2/5 prime power of exponent `Theta(E)`, as at `P^2+2`. It must not be
inferred from the unreduced common denominator.

### 8.2 What the pinned theorems actually say

- Bailey--Crandall Theorem 4.6, printed pp. 12--13, fixes coprime integers
  `b,c>1`, assumes sufficiently large `n` and `gcd(H,c^n)<D c^n`, treats the
  pure-power modulus `c^n`, and has a square-root-modulus leading cost. T79's
  `m_E` need not be a pure power. This is one benchmark, not a universal lower
  frontier.
- Bourgain Theorem 3.2, printed p. 325, gives a power saving for prime modulus
  and length `t>p^epsilon`, assuming the base and pairwise ratios have
  multiplicative order exceeding `p^epsilon`. For `r=1` this matches the shape
  `sum e_p(a theta^s)`, but `log p<p^epsilon` eventually. It does not apply to
  logarithmic length, composite `m_E`, or T79 without additional factor and
  order hypotheses.
- Konyagin--Shparlinski Theorem 1, printed p. 12, assumes prime modulus and that
  the base is a primitive root. Its first estimate is
  `p^(1/8+o(1))N^(71/96)` for `N<=sqrt(p)`. Comparing this with the trivial
  bound `N` becomes nontrivial only for
  `N>p^(12/25+o(1))`; that threshold is our algebraic deduction, not wording
  from the paper. The theorem does not reach logarithmic length and its
  primitive-root hypothesis is unverified for T79's factors.

No checked primary theorem supplies cancellation for the actual composite
modulus, numerator, fixed base 10, and `N=Theta(log m_E)` sum. In the
`P^2+2` configuration, Section 6 shows a still earlier problem: the transferred
prefix never reaches the periodic tail.

### 8.3 Uniform logarithmic cancellation is impossible: derived

A modulus-only theorem uniform over all unit numerators cannot solve the gap.
Take numerator `a=1`, `(q,10)=1`, and suppose

\[
 q\ge12\cdot10^{N-1}.
\]

Then every angle `2 pi 10^s/q`, `0<=s<N`, lies in `[0,pi/6]`, so

\[
 \Re\sum_{s=0}^{N-1}e^{2\pi i10^s/q}
 \ge\frac{\sqrt3}{2}N.                                 \tag{8.3}
\]

Thus no all-unit-numerator `o(N)` estimate is possible throughout

\[
 N\le1+\log_{10}(q/12),
\]

which is part of the logarithmic scale. This does not show that T79's special
numerators are small, and it does not exclude a structure-sensitive theorem.

## 9. Verdict

1. T79's least-valuation implication is correct in its printed range `E<P`.
2. The uniqueness step is false outside that range. `E=P^2+2` is an exact
   two-way tie, but for T79's `B,P` its leading residue is nonzero, so the
   claimed `P^E` denominator factor survives there.
3. Tied valuations can cancel (`p=7,b=3,E=51`), can be replaced by a strictly
   earlier minimum (`p=3,E=29`), and can occur three at a time. Formulae
   (3.3)--(3.7) are the required complete replacement.
4. At the reviewers' configuration, the exact power-of-5 transient is `E`,
   while transfer forces `N<E`. The post-transient orbit, its enormous order,
   and its occupancy formula govern none of the relevant prefix.
5. `N=Theta(log q)` is the correct derived denominator scale only under the
   explicit noncancellation and balanced-schedule hypotheses in Section 8. It
   is not a published cancellation theorem. The checked literature starts at
   polynomial modulus lengths under hypotheses absent here, and uniform
   logarithmic cancellation over numerators is elementarily false.

This is a corrected proof plus an exact counterexample to the unrestricted
uniqueness step and a fully displayed transient/short-sum obstruction. It does
not resolve the canonical question.

## 10. Reproduction

From a directory containing only this artifact set, run

```bash
python3 verify_note.py
```

The script uses only Python's standard library. It hash-checks every vendored
input and source, certifies `P` by trial division, exhaustively enumerates
valuation classes, checks all displayed residues and denominator valuations,
derives exact small-case denominators/moduli/orders/collisions, verifies the
prime-power order lift, and exercises the short-arc inequality. Its complete
stdout is supplied as `raw_output.txt`.
