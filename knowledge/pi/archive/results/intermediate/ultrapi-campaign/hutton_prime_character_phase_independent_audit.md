# Independent audit: Hutton signed prime-character phase

Audit date: **2026-08-12 UTC**  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Audit scope: [`hutton_prime_character_phase.md`](hutton_prime_character_phase.md)
and both finite checkers

## Verdict

**PASS at the stated `proof sketch` level, after four substantive precision
corrections.** The Abel transform, explicit unconditional and GRH bounds,
symmetric-product expansion, sparse recurrence, period lower bound, and
logarithmic shadowing constant are correct in their corrected domains. The
primary-source claims below are `literature-checked` as of 2026-08-12. The
finite and high-precision replays are `experiment` evidence only.

The four corrections were:

1. Equation (11) now states its exact domain (K\ge8). Before correction, its
   unrestricted Chebyshev function included the deliberately excluded prime
   (17) at (K=7).
2. Equation (38) is now identified as equidistribution of the real
   reciprocal-sum proxy, not of the actual modular (21^{-1}) CRT coordinate.
   A stronger, correctly lifted target (38') was added.
3. The symmetric product formerly called (B_K) was renamed (V_K), avoiding
   collision with the complementary CRT modulus in (39).
4. The prime-race section now displays the exact Abel identity (31a). The
   ratio-free limiting operator (31) remains explicitly a `proof sketch`
   pending the required endpoint and limiting-distribution argument.

No complete proof of V1 follows. V1 remains a `conjecture`; this branch is not
`machine-checked`, not a `candidate resolution`, and not a `verified
resolution`.

## Audited pins

- Canonical target SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Corrected report SHA-256:
  `906415f951332f46052eb9cda2841f67327e9d9befd9a1e6c64b0ddaa915580a`
- Original checker SHA-256:
  `3a9ff832735bcb705a3ac6b90a30a9b233b95626d3c4e9e41587d41dfa1a62a0`
- Independent checker SHA-256:
  `7e26966384d59cd3b59ccc8eb7389044c0fbee620172c720ef156620e850cbcb`

Primary PDFs were fetched afresh from the versioned arXiv URLs. Their bytes
match the report's pins:

- Bennett--Martin--O'Bryant--Rechnitzer v3:
  `e51f8b8f63486c2259efe076d367504f08dda0fe9e99dc35bf36de544ffc0601`
- Lee v2:
  `d36de57c5bdaad1470f318dc7423cde1ae234e7348a8edaa01f7c683d115f4cc`
- Thorner--Zaman v2:
  `588ec896e0820c3620175b25da58850efbefc67b71227acac1d5c3fa4f6b3b09`
- Khale v1:
  `e232e295f93e4b3be4e33d4a0043145645832316fd765fde89eadfc7b735c136`

## 1. Abel transform and explicit unconditional bound

Let (a=R/2), (f(t)=1/(t\log t)), and

\[
 \vartheta_\chi(x)=\sum_{p\le x}\chi_4(p)\log p.
\]

For (K\ge8), all excluded primes are at most (17<a), so

\[
 \Delta_K=\int_{(a,R]}f(t)\,d\vartheta_\chi(t).
\]

Stieltjes integration by parts gives

\[
 f(R)\vartheta_\chi(R)-f(a)\vartheta_\chi(a)
 -\int_a^R\vartheta_\chi(t)f'(t)\,dt,
\]

and

\[
 -f'(t)={\log t+1\over t^2(\log t)^2}.
\]

This is exactly (11). The qualification is necessary: at (K=7), the
right-hand side using unrestricted (artheta_\chi) exceeds the eligible
(Delta_7) by exactly (1/17). The independent checker confirms this at
80-decimal precision, but the displayed derivation is the `proof sketch`.

Bennett--Martin--O'Bryant--Rechnitzer give, for (q=4),

\[
 \left|\vartheta(x;4,a)-{x\over2}\right|
 <0.0004822{x\over\log x},\qquad x\ge4{,}800{,}162{,}889.
\]

Taking the difference of the two reduced classes gives (c_4=0.0009644).
The boundary terms in (11) contribute
(c_4(L^{-2}+L_0^{-2})). The integral is

\[
 c_4\int_{L_0}^{L}(u^{-2}+u^{-3})\,du
 =c_4\left({1\over L_0}-{1\over L}
   +{1\over2L_0^2}-{1\over2L^2}\right).
\]

Adding them yields exactly (14). The threshold must be doubled so that the
whole interval ([R/2,R]) lies in the source theorem's range. The numerical
endpoint (5.128429860125545\times10^{-6}), (b_K=14), and shifted value
(5.128429860125545\times10^8) reproduce.

## 2. Effective Vinogradov--Korobov estimate

Thorner--Zaman Corollary 1.4 contains a possible exceptional-zero factor
(lambda); this detail cannot simply be omitted in general. It is harmless
for (q=4): the only real nonprincipal character is (chi_4), and for real
(s>0),

\[
 L(s,\chi_4)=\sum_{n\ge0}ig((4n+1)^{-s}-(4n+3)^{-s}\big)>0.
\]

Each paired summand is positive and the paired series converges for (s>0),
so there is no exceptional real zero and (lambda=1). Corollary 1.4 then
gives, with effectively computable constants,

\[
 \vartheta_\chi(x)\ll x
 \exp\!\left(-c{(\log x)^{3/5}\over(\log\log x)^{1/5}}\right).
\]

Substitution in (11) over a fixed-ratio dyadic interval supplies the extra
(1/\log R) in (2). Khale Theorem 1.1 states the quoted zero-free region

\[
 \sigma\ge1-
 {1\over10.5\log q+61.5(\log|t|)^{2/3}(\log\log|t|)^{1/3}},
 \qquad |t|\ge10.
\]

This independently supports the Vinogradov--Korobov shape. The phrase
“strongest input found in the bounded search” should be read literally as a
dated bounded-search statement, not as a novelty or exhaustive-survey claim.
A 2026-08-12 re-search found later work on short arithmetic progressions but
no primary theorem that changes the fixed-(q=4), full-interval exponent or
controls the moving frequency needed here.

## 3. Explicit GRH bound

Lee Corollary 4.4 for a nonprincipal character, specialized to (q=4) and
(x_0=e^{10}), has Table 5 values

\[
 \Omega_0=7.73253,\quad \Omega_1=0.78834,
 \quad\Omega_2=-8311.79.
\]

Thus

\[
 |\vartheta_\chi(t)|\le\sqrt t\left(
 {y^2\over8\pi}+left({\log4\over2\pi}+1.44270+7.73253\right)y
 +0.78834\right)
\]

for (y=\log t\ge10), after dropping the favorable negative
(Omega_2). This is the report's (M(y)), since
(1.44270+7.73253=9.17523).

Monotonicity of (M), the two boundary terms, and

\[
 \int_{R/2}^{R}t^{-3/2}\,dt={2(\sqrt2-1)\over\sqrt R}
\]

give (21). Replacing (1/L) by (1/L_0) produces the coefficient
((3\sqrt2-1)/L_0), and the (1/L_0^2) part is
(2(\sqrt2-1)/L_0^2). At (R=2e^{10}), the independent replay gives
(0.167645225442396\), (b_K=6), and (1.67645225442396\times10^5).

## 4. Symmetric product and logarithmic window

For every selected prime,

\[
 {1\over2}\log{p+\epsilon_p\over p-\epsilon_p}
 =\operatorname{atanh}{\epsilon_p\over p}
 ={\epsilon_p\over p}+
 \sum_{j\ge1}{\epsilon_p\over(2j+1)p^{2j+1}}.
\]

The absolute tail is bounded by

\[
 \sum_{j\ge1}{1\over(2j+1)p^{2j+1}}
 \le {1\over3p^3}\sum_{j\ge0}p^{-2j}
 ={1\over3p(p^2-1)}.
\]

Summing proves (7) with its exact constant. Since every selected prime is
(>R/2) and there are (O(R/\log R)) of them, the total error is
(O(R^{-2}/\log R)).

Let (alpha=\log 10/\log5). The exact bounds

\[
 {R^\alpha\over10}<10^{\lfloor\log_5R\rfloor}\le R^\alpha
\]

and (10^s\le R^{2-\alpha}) show that the scaled tail is
(O(1/\log R)) whenever

\[
 0\le s\le(2-\alpha)\log_{10}R.
\]

The independently recomputed constants are

\[
 \alpha=1.43067655807339305067\ldots,qquad
 2-\alpha=0.56932344192660694933\ldots.
\]

Thus the report's shifted logarithmic window is correct. It is only
(O(\log R)); it does not approach the (O(R)) Hutton transfer horizon.

The exact (2)-adic and mod-(4) assertions also check directly:
(p+\epsilon_p\equiv2\pmod4), (p-\epsilon_p\equiv0\pmod4), and
(epsilon_p p^{-1}\equiv1\pmod4). The independent checker replays these
for (2\le K\le1000).

## 5. Sparse recurrence and period bound

From (K) to (K+1), the upper endpoint admits (4K+5) and (4K+7),
while the lower endpoint removes (2K+3). Their character signs are

\[
 \chi_4(4K+5)=1,\quad \chi_4(4K+7)=-1,
 \quad-\chi_4(2K+3)=(-1)^K.
\]

This proves (29), including the eligibility exclusions. The independent
checker verifies the Fraction identity through (K=1000); that finite replay
has `experiment` status.

For each (p\mid G_K), reduction of (S_K) modulo (p) leaves the unique
nonzero term (epsilon_pG_K/p), so ((S_K,G_K)=1). Since also
((10,G_K)=1), (d_K=\operatorname{ord}_{G_K}(10)) exists and

\[
 G_K\mid10^{d_K}-1\quad\Longrightarrow\quad
 d_K\ge\log_{10}(G_K+1).
\]

The prime number theorem gives
(log G_K=R/2+o(R)), hence (36). This is a period lower bound only; it gives
no discrepancy or interval-hitting conclusion.

## 6. Prime-race transform and the corrected lift issue

With (A(x)=\sum_{p\le x}\chi_4(p)), partial summation gives exactly

\[
 \Delta(x)={A(x)\over x}-{A(x/2)\over x/2}
 +\int_{x/2}^{x}{A(t)\over t^2}\,dt.
\]

Substituting (x=e^y) and
(A(e^v)=e^{v/2}E(v)/v) gives corrected equation (31a), including the two
ratios (y/(y-\log2)) and (y/(y+\log u)). Dropping those ratios leads to
the limiting operator (31). For a mode (e^{i\gamma y}),

\[
 \int_{1/2}^{1}u^{-3/2+i\gamma}\,du
 ={1-\sqrt2e^{-i\gamma\log2}\over-1/2+i\gamma},
\]

so its multiplier is exactly (32), and its modulus is at least
(sqrt2-1). The algebra is correct. What remains unproved is the passage
from the exact transform to a limiting distribution with a justified
(o(1)); the report now says so.

The earlier implication from (38) to the actual (G_K)-coordinate was false.
If (u_K\equiv68\,21^{-1}S_K\pmod {G_K}), then

\[
 {u_K\over G_K}={n_K\over21}+{68\over21}\Delta_K
\]

for a correlated integer branch (n_K). Equidistribution of
(10^{b_K}\Delta_K) does not choose these inverse branches uniformly. A
simple exact countermodel takes an equidistributed rational grid (x_j) and
(y_j=\{68x_j\}/21): then (21y_j\equiv68x_j\pmod1), while every (y_j)
lies in ([0,1/21)). The independent checker includes this construction.
The corrected (38') asks directly for Weyl cancellation of the actual lifted
coordinate. Even that omits the correlated complementary CRT phase and is
strictly weaker than V1.

## 7. Source audit

The following primary sources were re-read from the pinned PDFs:

1. Michael A. Bennett, Greg Martin, Kevin O'Bryant, and Andrew Rechnitzer,
   [*Explicit bounds for primes in arithmetic progressions*](https://arxiv.org/abs/1802.00085),
   v3, Theorem 1.2 and the (q=4) table.
2. Ethan S. Lee,
   [*The prime number theorem for primes in arithmetic progressions at large values*](https://arxiv.org/abs/2301.13457),
   v2, Corollary 4.4 and Table 5.
3. Jesse Thorner and Asif Zaman,
   [*Refinements to the prime number theorem for arithmetic progressions*](https://arxiv.org/abs/2108.10878),
   v2, Corollary 1.4 and Remark 1.5.
4. Tanmay Khale,
   [*An explicit Vinogradov--Korobov zero-free region for Dirichlet L-functions*](https://arxiv.org/abs/2210.06457),
   v1, Theorem 1.1.
5. Michael Rubinstein and Peter Sarnak,
   [*Chebyshev's Bias*](https://doi.org/10.1080/10586458.1994.10504289).
   It supports only the conditional research direction; the dyadic weighted
   transform is not attributed to it as a proved theorem.

The explicit unconditional and GRH formulas in the report match the first
four sources. No searched source proves a moving-frequency estimate for
(10^b\Delta_K), its modular (21^{-1}) lift, or the joint CRT state.

## 8. Reproduction commands and outputs

The original checker was run exactly as documented:

```text
python3 work/ultrapi-resume/hutton_prime_character_phase_check.py
```

Its output reproduced the report, ending with:

```text
all exact checks passed; distribution rows are experiments only
```

The independent checker was compiled and run with:

```text
python3 -m py_compile \
  work/ultrapi-resume/hutton_prime_character_phase_check.py \
  work/ultrapi-resume/hutton_prime_character_phase_independent_check.py
python3 work/ultrapi-resume/hutton_prime_character_phase_independent_check.py
```

Output:

```text
PASS: independent exact recurrence, gcd, 2-adic, mod-4, order, and lift checks
EXPERIMENT PASS: 80-digit Abel, log-tail, endpoint, and multiplier replays
```

The source bytes were reproduced with:

```text
audit_tmp=$(mktemp -d /tmp/prime-phase-audit.XXXXXX)
curl -L --fail --silent --show-error https://arxiv.org/pdf/1802.00085v3 -o "$audit_tmp/bennett.pdf"
curl -L --fail --silent --show-error https://arxiv.org/pdf/2301.13457v2 -o "$audit_tmp/lee.pdf"
curl -L --fail --silent --show-error https://arxiv.org/pdf/2108.10878v2 -o "$audit_tmp/thorner.pdf"
curl -L --fail --silent --show-error https://arxiv.org/pdf/2210.06457v1 -o "$audit_tmp/khale.pdf"
sha256sum "$audit_tmp"/*.pdf
```

Focused formatting and pin checks were:

```text
git diff --check -- \
  work/ultrapi-resume/hutton_prime_character_phase.md \
  work/ultrapi-resume/hutton_prime_character_phase_independent_check.py
sha256sum \
  work/ultrapi-resume/hutton_prime_character_phase.md \
  work/ultrapi-resume/hutton_prime_character_phase_check.py \
  work/ultrapi-resume/hutton_prime_character_phase_independent_check.py \
  problems/local/pi-digits.txt
```

All passed. These checks substantiate the arithmetic ledger and source
transcription only. They are not a proof of V1.

## Remaining barrier

The branch ends at a genuine moving-frequency problem. Known unconditional
and GRH pointwise cancellation is overwhelmed by the mandatory
(10^{b_K+s}) shift. The symmetric logarithmic product remains accurate for
only (0.5693234419\ldots\log_{10}R) post-transient steps. Neither the proxy
Weyl conjecture (38), the correctly lifted conjecture (38'), nor the joint
complementary CRT estimate is proved. The report's corrected bottom line is
therefore appropriately conservative.
