# Actual twelve-term Machin forcing: exact experiment report

Claim status: `experiment`, except for the explicitly labeled algebraic
`proof sketch`.  Nothing here proves decimal-word recurrence, density,
normality, or V1.

## Target and normalization

The immutable local problem statement is
[`problems/local/pi-digits.txt`](../../../problems/local/pi-digits.txt).  This
run studies only the exact T40 forcing from equation (11w) of `ultrapi.md`.
For $N\ge0$, put

\[
 a_k=12N+5+2k\quad(0\le k\le6)
\]

and

\[
 \Delta_N=10^{N+1}\sum_{j=0}^{5}(-1)^j
 \left(\frac{16}{a_j5^{a_j}}+
       \frac{4}{a_{j+1}239^{a_{j+1}}}\right).
\]

The individually reduced denominators are

\[
 d_{5,j}=a_j5^{a_j-N-1},\qquad
 d_{239,j}=\frac{a_{j+1}239^{a_{j+1}}}
 {\gcd(a_{j+1},5^{N+1})}.
\]

Define the exact term LCD, cleared numerator, and cancellation quotient by

\[
 \Lambda_N=\operatorname{lcm}_{0\le j<6}(d_{5,j},d_{239,j}),\qquad
 T_N=\Lambda_N\Delta_N\in\mathbb Z,
\]

\[
 g_N=\gcd(T_N,\Lambda_N)
     =\frac{\Lambda_N}{\operatorname{den}(\Delta_N)}.
\]

The equality on the right uses the reduced positive denominator convention.
These definitions distinguish the actual twelve summands from the loose
product grid used by the separator in (11ad)--(11ae).

## Reproducibility and independent check

The production program is
[`machin_forcing_gmp.cpp`](machin_forcing_gmp.cpp).  It uses GMP rationals,
explicitly canonicalizes every individual summand before forming the LCD,
and independently compares the rational sum with the integer sum over that
LCD.  The small reference
[`machin_forcing_reference.py`](machin_forcing_reference.py) uses Python's
`Fraction` and fresh direct powers.  The retained analysis is produced by
[`analyze_results.py`](analyze_results.py).

The initial cross-check used these exact commands:

```bash
python -m py_compile \
  work/ultrapi-resume/experiments/machin_forcing_reference.py \
  work/ultrapi-resume/experiments/analyze_results.py

podman run --rm -v "$PWD:/workspace:Z" -w /workspace \
  localhost/allmath-research:latest bash -lc \
  'g++ -O3 -DNDEBUG -std=c++23 \
     work/ultrapi-resume/experiments/machin_forcing_gmp.cpp \
     -lgmpxx -lgmp -o /tmp/machin_forcing_gmp && \
   /tmp/machin_forcing_gmp --max-n 20 \
     --out-dir work/ultrapi-resume/experiments/data-smoke'

python work/ultrapi-resume/experiments/machin_forcing_reference.py \
  --max-n 20 \
  --gmp-small-exact \
    work/ultrapi-resume/experiments/data-smoke/small_exact.tsv \
  --output work/ultrapi-resume/experiments/data-smoke/reference.json
```

The primary run and its deterministic post-analysis used:

```bash
podman run --rm -v "$PWD:/workspace:Z" -w /workspace \
  localhost/allmath-research:latest bash -lc \
  'g++ -O3 -DNDEBUG -std=c++23 \
     work/ultrapi-resume/experiments/machin_forcing_gmp.cpp \
     -lgmpxx -lgmp -o /tmp/machin_forcing_gmp && \
   /tmp/machin_forcing_gmp --max-n 5000 \
     --out-dir work/ultrapi-resume/experiments/data-5000'

python work/ultrapi-resume/experiments/machin_forcing_reference.py \
  --max-n 20 \
  --gmp-small-exact \
    work/ultrapi-resume/experiments/data-5000/small_exact.tsv \
  --output work/ultrapi-resume/experiments/data-5000/reference.json

python work/ultrapi-resume/experiments/analyze_results.py \
  --data-dir work/ultrapi-resume/experiments/data-5000 \
  --output work/ultrapi-resume/experiments/data-5000/analysis.json \
  --bm-prefix 5001
```

The two implementations agree exactly on all six retained integers
$(N,T_N,\Lambda_N,g_N,\operatorname{num}\Delta_N,
\operatorname{den}\Delta_N)$ for every $0\le N\le20$.  The production
run also checks the displayed denominator formulas, positivity, the direct
integer sum, reduction by $g_N$, the expected 2-adic numerator valuation,
and the 3-adic component of $g_N$ at every row.

## A local cancellation criterion specific to the twelve terms

The strongest structural finding is the following algebraic `proof sketch`.
It is not a Lean declaration and is not promoted to `machine-checked`.

Fix a prime $p\ge7$, $p\ne239$, and suppose $p\mid a_k$ for an interior
index $1\le k\le5$.  Since the seven $a_i$'s differ by nonzero even
integers of absolute value at most 12, this $a_k$ is the unique member
divisible by $p$.  Then

\[
 \boxed{\quad p\mid g_N
 \iff 4\,239^{a_k}\equiv5^{a_k}\pmod p.\quad} \tag{LC}
\]

Here are both directions, with the assumptions exposed.

1. Write $a=a_k=p^ec$, with $p\nmid c$.  Because $p\nmid5\cdot239$ and no
   other $a_i$ is divisible by $p$, both terms sharing $a_k$ have
   denominator valuation $e$, every other term has denominator valuation
   zero, and $v_p(\Lambda_N)=e$.
2. In $T_N=\Lambda_N\Delta_N$, all ten other terms therefore vanish modulo
   $p$.  The surviving base-5 term has index $j=k$ and sign
   $s=(-1)^k$; the surviving base-239 term has index $j=k-1$ and sign
   $-s$.
3. In the field \(\mathbb F_p\), let
   \(C=(\Lambda_N/p^e)c^{-1}\), which is nonzero.  Direct substitution of
   the two coefficients gives

   \[
   T_N\equiv
   s\,4\,10^{N+1}C
   \left(4\,5^{-a}-239^{-a}\right)\pmod p.
   \]

   The factor before the parentheses is nonzero.
4. Since $p\mid\Lambda_N$, one has $p\mid g_N\iff p\mid T_N$.  The last
   display therefore gives
   $p\mid g_N\iff4\,5^{-a}=239^{-a}$.  Multiplication by the nonzero
   $5^a239^a$ proves (LC) in both directions.

This argument also explains why the word *interior* is essential.  At
$N=176$, $29\mid a_0=2117=29\cdot73$, and the same congruence is zero, but
only one term carries $a_0$; accordingly $29\nmid g_{176}$.

The congruence has two useful equivalent forms.  With
$r_p=239/5\in\mathbb F_p^\times$,

\[
 4r_p^{a_k}=1.
\]

If $a_k=p^em$ with $p\nmid m$, Frobenius gives
$r_p^{a_k}=r_p^m$, hence

\[
 p\mid 4\cdot239^m-5^m. \tag{LC'}
\]

If $d_p=\operatorname{ord}_p(r_p)$, either
$4^{-1}\notin\langle r_p\rangle$ and no such cancellation is possible, or
the allowed $m$'s form one residue class modulo $d_p\mid p-1$.  For a fixed
$p$, the cancellation indicator as a function of $N$ is consequently
periodic with period dividing $p(p-1)$: increasing $N$ by that amount
preserves both $p\mid a_k$ and the exponent modulo $p-1$.  More precisely,
for each fixed interior $k$, once a solution exists its period divides

\[
 \frac{p d_p}{\gcd(12,d_p)}.
\]

This proves, at `proof sketch` status, that extra cancellation occurs on
explicit infinite arithmetic progressions.  Two small families are:

\[
 19\mid g_{7+57t}\qquad(t\ge0). \tag{P19}
\]

Indeed $239/5\equiv6\pmod {19}$,
$\operatorname{ord}_{19}(6)=9$, and $4\cdot6^5\equiv1$.  For
$N=7+57t$, the interior index $a_3=95+684t$ is divisible by 19 and is
congruent to 5 modulo 9, so (LC) applies.  Likewise,

\[
 29\mid g_N\quad\text{if}\quad
 N\equiv6,40,74,108,142\pmod {203}. \tag{P29}
\]

Here $239/5\equiv13\pmod {29}$,
$\operatorname{ord}_{29}(13)=14$, and $4\cdot13^3\equiv1$.  At the five
listed residues, respectively $a_5,a_4,a_3,a_2,a_1$ is divisible by 29
and congruent to 3 modulo 14; adding 203 to $N$ adds
$2436=29\cdot84$ to the same $a_k$.  Thus (LC) proves every member of
both families.  These progressions show that $g_N=3$ fails infinitely
often, but they do not constrain the forced orbit's archimedean cell.

There is also an exact prime-adic strengthening of (LC).  Under the same
assumptions, let $e=v_p(a_k)$.  Reducing the LCD-cleared sum modulo $p^e$
rather than only $p$ leaves the same two terms, while all other ten are
multiples of $p^e$.  Since all omitted factors are $p$-adic units,

\[
 \boxed{\quad
 v_p(g_N)=\min\!\left(e,
 v_p(4\cdot239^{a_k}-5^{a_k})\right).
 \quad} \tag{LCv}
\]

If $p$ instead divides a boundary index $a_0$ or $a_6$, exactly one
term survives after clearing modulo $p$, so $v_p(g_N)=0$.  Consequently
every prime $p\ge7$, $p\ne239$, dividing $g_N$ comes from a unique interior
index and is governed by (LCv).

### Compatibility with T45

The result is consistent with the independently machine-checked
[T45T45MachinPrimeSurvival.lean](../../../TheoryLib/PiQuantitativeBlockHitting/T45T45MachinPrimeSurvival.lean).
T45 assumes that the entire interior index is prime, $a_k=p$, in one of the
only possible prime slots $k\in\{1,3,4\}$.  Specializing (LC) to $a_k=p$ and
using Fermat gives

\[
 p\mid g_N
 \iff p\mid4\cdot239^p-5^p
 \iff p\mid4\cdot239-5
 \iff p\mid951.
\]

Now $951=3\cdot317$, and T45 proves that 317 cannot occupy any of those three
slot congruences.  Hence T45's conclusion $v_p(\Delta_N)=-1$—the denominator
prime survives—is exactly the prime-index special case of (LCv).  The new
cancellation examples do not contradict it: each uses a composite interior
index $a_k=p^em$ with $m>1$ (for example, $87=29\cdot3$ and
$8207=29\cdot283$).  Direct recompilation of T45 passed, with only propext,
Classical.choice, and Quot.sound reported.

The order observation gives only weak unconditional size information when
$p$ is allowed to vary.  If

\[
 h_N=\prod_{\substack{p\ge7,\ p\ne239\\p\text{ prime}}}
 p^{v_p(g_N)},
\]

then the proof above implies

\[
 h_N\mid\prod_{k=1}^{5}a_k,\qquad
 h_N\le(12N+15)^5,\qquad
 \omega(h_N)\le\frac{5\log(12N+15)}{\log7}.
\]

It supplies no uniform bound across all $N$, because both the prime and the
cofactor $m$ in (LC') vary.  Nor does finite data prove that the number or
size of actual cancelling primes is unbounded.

## Exact finite results

The primary retained $0\le N\le5000$ run is in
[`data-5000`](data-5000/summary.json) and is labeled only `experiment`.
It contains 5,001 exact rows and took 1,024.93 seconds.  Every internal check
has zero failures.  It reproduces

\[
 v_2(\operatorname{num}\Delta_N)=N+4,
 \qquad v_3(g_N)=1
\]

at all 5,001 tested indices.  The stronger exact local formula (LCv),
including the boundary-index exclusion, has zero mismatches for every prime
$p\ge7$, $p\ne239$, dividing one of the seven local indices.  The independent
Python reference again exactly matches all retained integers through $N=20$.

There are 332 rows with $g_N\ne3$.  Four exact counterexamples retire
tempting stronger guesses:

- $N=6$: $a_5=87=29\cdot3$,
  $29\mid4\cdot239^3-5^3$, and $g_6=87=3\cdot29$.  Thus $g_N=3$
  is not universal.
- $N=576$: $g_{576}=75=3\cdot5^2$.  Thus the extra cancellation need
  not be squarefree.
- $N=683$: $a_3=8207=29\cdot283$, both primes satisfy (LC'), and
  $g_{683}=24621=3\cdot29\cdot283$.  Thus one row can have more than one
  extra cancelling prime; in particular, the large-prime part is not always
  a single prime.
- $N=2451$: $g_{2451}=375=3\cdot5^3$.  Thus even the corrected guess
  $v_5(g_N)\le2$, suggested by the first 1,001 rows, is false.

The first family also refutes any proposed uniform bound $p\le N$ for an
extra cancelling prime: already $29\mid g_6$.  A more pronounced example is
$4649\mid g_{1936}$, arising from the interior
$a_4=23245=5\cdot4649$ and
$4649\mid4\cdot239^5-5^5$.  These are counterexamples to those simple size
bounds, not evidence that the largest cancelling prime is unbounded.

The normalized odd reduced numerators

\[
 u_N=\operatorname{num}(\Delta_N)/2^{N+4}
\]

show no small constant-coefficient linear recurrence in this sample.  On the
5,001-term prefix their Berlekamp--Massey complexities over
\(\mathbb F_{101},\mathbb F_{251},\mathbb F_{1009}\) are all 2501, for
both $u_N$ and the unreduced $T_N/2^{N+4}$.  The detector is checked
against constant (complexity 1) and Fibonacci (complexity 2) controls.  This
is a finite falsification of low-order recurrences on the tested prefix, not
a proof of high linear complexity at later indices.  (The retained
[`data-1000`](data-1000/analysis.json) audit gives the separate 1,001-term
residue statistics: modulo 101, both sequences visit every residue, with
chi-squares approximately 97.29 and 97.69.)

After removing the forced powers of two, nearby numerator gcds are sparse
but not always one.  The first adjacent event is

\[
 \gcd(u_{80},u_{81})=67,
\]

and the largest event among lags 1 through 10 through $N=5000$ has 16 bits.
Thus pairwise-coprime normalized numerators are also refuted.

The exact rational orbit reproduces the earlier finite code counts: all ten
one-digit cells first appear by $N=31$, all 100 two-digit cells by
$N=604$, and 997 of 1,000 three-digit cells appear through $N=5000$.  The
three missing cells are 373, 483, and 500.  It sees 3,952 distinct four-digit
cells in those 5,001 positions.  These counts distinguish this finite prefix
from the explicit avoiding separators, but they have zero proof leverage for
future coverage.

## Interpretation and remaining obstruction

The local criterion is actual twelve-term information: it comes from the
opposite signs and coefficient ratio of the two Machin summands sharing each
interior odd index.  It explains the sparse non-3 LCD cancellations and
turns every eligible large-prime cancellation into a concrete
multiplicative-order test.

It does not control the archimedean residue of the forced orbit.  Fixed-prime
periodicity, high sampled linear complexity, residue occupancy, and finite
cell coverage do not imply recurrence.  The remaining proof obstruction is
still a uniform mechanism forcing the single moving rational orbit into
every decimal cell; no such mechanism is established here.
