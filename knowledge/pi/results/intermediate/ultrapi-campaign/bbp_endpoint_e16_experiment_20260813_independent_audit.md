# Independent audit: full BBP endpoint phase at epoch 16

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

## Conclusion and exact claim boundary

The frozen epoch-16 calculation survives an independent adversarial replay.
No fatal or nonfatal mathematical defect was found.  The replay confirms:

1. both exact exponent windows and their 5,491,685 points;
2. a separately directed 32,395,907-place pi prefix;
3. every overlapping 18-digit window by a non-rolling construction;
4. both complete translated circle gaps, including wraparound;
5. the exact BBP-tail and gap-transfer intervals;
6. the implication from the strict gap bound to all five-digit cylinders;
7. independently of that implication, direct occurrence of every one of the
   100,000 five-digit words in each certified row.

All finite computed conclusions retain label `experiment`.  The elementary
transfer arguments below have label `proof sketch`.  This audit proves no
asymptotic gap law, Fourier decay, fixed return, length-six coverage, or
canonical V1.  V1 remains a `conjecture`; this is neither a
`candidate resolution` nor a `verified resolution`.

## 1. Frozen artifacts and independent route

| artifact | SHA-256 |
|---|---|
| canonical local source | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| [full-phase report through epoch 14](bbp_three_grid_full_phase_experiment_20260813.md) | `f58f45259f19feb4f2e72f505199ed4476dfdec02bbdb82fbf6892bd6ec80b80` |
| [independent audit through epoch 14](bbp_three_grid_full_phase_experiment_20260813_independent_audit.md) | `6cd9d451df087ad0208af9f4b02bcd16fbf5af5b0603b36a9bee6c61a0466ed9` |
| [audited primary script](bbp_endpoint_e16_experiment_20260813.py) | `d9fc5d4f8bff417bb50812788c0f893a03d9c02c343b1a031f69b390a2320e13` |
| [audited retained output](bbp_endpoint_e16_experiment_20260813_record.txt) | `2a9b25378bdf0a0a7a8d796c76c5e7058932876bb0a8004f21322d792edf982d` |
| [audited primary report](bbp_endpoint_e16_experiment_20260813.md) | `b9dfc7682b525afae6d70379982f6503962dfce55389c4b0d2a8efb87505c9aa` |
| [independent checker](bbp_endpoint_e16_experiment_20260813_independent_check.py) | `332c9bcaae58d626a0aa5614f5a5f928b2be9245532241ec6061d4d0e7fb46db` |

The independent checker imports no definition from the primary script.  Its
main computational differences are:

- 512 extra precision bits beyond a strict rational bit-count upper bound;
- exact correction of a base-ten `mpz` digit-count estimate by integer
  boundary comparisons;
- direct column-polynomial construction of each 18-digit word rather than
  the primary rolling recurrence;
- translation-invariant Fourier diagnostics evaluated before $16\pi$
  shift;
- direct frequency tables for all words of lengths one through five;
- independently sorted phase arrays and fixed-endian SHA-256 digests.

The primary run was also reproduced separately and ended in `status=PASS`.
Its two JSON rows reproduce exact-record SHA-256
`421dae474d0735647e5a6d7b4358cc40416142c50d1763d385e9a56c593ceadf`.

## 2. Exponent and digit-window audit

For $e=16$, exact integer evaluation gives

\[
 A_{16}=\frac{3^{16}-1}{8},\qquad
 M^-_{16}=26{,}904{,}199,\qquad M^+_{16}=26{,}904{,}200.
\]

The independent checker forms $16^M=2^{4M}$ as an exact integer.  It uses a
decimal digit-count only as an estimate, corrects that estimate until the
exact inequalities $10^U\le16^M<10^{U+1}$ hold, and obtains

| row | $M$ | $U$ | $U-M+1$ |
|:---:|---:|---:|---:|
| pre-drop | 26,904,199 | 32,395,883 | 5,491,685 |
| first-drop | 26,904,200 | 32,395,884 | 5,491,685 |

If `digits[0]` is the first digit after the decimal point, then the slice
`digits[n:n+18]` is exactly the 18-digit truncation of
$\{10^n\pi\}$.  The independent checker constructs it as

\[
 W_n=\sum_{j=0}^{17}d_{n+j}10^{17-j},
\]

column by column for every $n$, rather than updating $W_n$ to
$W_{n+1}$.  The combined stream from $n=26{,}904{,}199$ through
$32{,}395{,}884$ has fixed-little-endian SHA-256

```text
95914e81d02b2d1305de733b57dd8e3e8416ba1decfccfded45be4fac7dc6a06
```

The two overlapping row streams have respective SHA-256 values

```text
47e588bc9286a5d608fa4cd75f6c99ef8318c94e4d4d0e4463f0493846f78121
3800d3180ecf0fe2f33f132e8ea4aa7f61f7a16cdbb217fa3afaad9d30ee61d7
```

The largest needed 18-digit window ends at fractional digit 32,395,902.  The
directed prefix extends through digit 32,395,907, leaving five guard digits.
For the five-digit consequence, the one-indexed starting positions on the
pre-drop row are exactly 26,904,200 through 32,395,884, as stated in the
primary report.

## 3. Directed pi-prefix certification

The independent precision is 107,617,448 bits.  This exceeds

\[
 32{,}395{,}907\cdot\frac{332193}{100000}+512,
\]

where $332193/100000>\log_2 10$.  At that precision MPFR 4.2.2 is evaluated
once with rounding downward and once with rounding upward.  Both evaluations
of

\[
 \left\lfloor\pi10^{32{,}395{,}907}\right\rfloor
\]

produce the same integer.  Its certified fractional-digit byte string has
SHA-256

```text
e5f577a403fecb0a03bf8947b3e59787731f9c9e57451ad8007b5c16c8eaa93e
```

Let $P=\lfloor\pi10^N\rfloor$, with $N=32{,}395{,}907$.  Since
$P\le\pi10^N<P+1$, exact integer division of both endpoints after
multiplication by 16 gives the same 18-digit fractional prefix

```text
265482457436691815
```

This independently verifies the shift used in every row residue.

The certification is still classified as `experiment`: it relies on the
recorded MPFR/gmpy2 computation and is not a Lean theorem or a claim about
arbitrary decimal depth.

## 4. Truncation, BBP tail, and circle transfer

Put $Q=10^{18}$.  For each exponent write

\[
 \{10^n\pi\}=\frac{W_n}{Q}+r_n,\qquad
 \{16\pi\}=\frac{C}{Q}+s,
 \qquad 0\le r_n,s<Q^{-1}.
\]

Thus the truncated translated residue
$\widetilde y_n=\{(W_n-C)/Q\}$ satisfies the strict circle estimate

\[
 d_{\mathbb T}\left(\widetilde y_n,
              \{(10^n-16)\pi\}\right)
 \le |r_n-s|<Q^{-1}.                                      \tag{A16.1}
\]

The important constant is $Q^{-1}$, not $2Q^{-1}$: both errors are in the
same one-sided interval, so their difference has absolute value below its
length.

For the BBP coefficient

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},
\]

direct expansion gives, for $k\ge1$,

\[
 (2k+1)(4k+3)(8k+1)(8k+5)
 -k^2(120k^2+151k+47)
 =392k^4+873k^3+665k^2+194k+15>0.
\]

Hence $0<a(k)<k^{-2}$.  If $M\le n\le U(M)$, then
$0<10^n-16<10^n\le16^M$, and therefore

\[
\begin{aligned}
 0<(10^n-16)(\pi-B_M)
 &<16^M\sum_{j=M+1}^{\infty}\frac1{j^2 16^j}\\
 &\le\frac1{(M+1)^2}\sum_{r=1}^{\infty}16^{-r}
 =\frac1{15(M+1)^2}.                                  \tag{A16.2}
\end{aligned}
\]

Combining (A16.1)--(A16.2) gives exactly

\[
 \eta_M=10^{-18}+\frac1{15(M+1)^2}.
\]

The independently reconstructed exact values are

```text
pre-drop:   5054287698323/54287698323000000000000000000
first-drop: 202171508094345203/2171508094345203000000000000000000
```

If two finite labeled circle sets have corresponding points within
$\eta$, their Hausdorff distance is at most $\eta$.  Their covering radii
differ by at most $\eta$; since largest gap is twice covering radius, their
largest gaps differ by at most $2\eta$.  Distance from a prescribed target
to the set differs by at most $\eta$.  These elementary facts validate all
four exact target and BBP-gap intervals retained in the primary output.

The independent directed-log calculation also places both endpoints of both
BBP-gap intervals inside

\[
 0.899<\frac{LG}{\log L}<1.084.
\]

This is only the two-row `experiment`, not a uniform-in-epoch statement.

## 5. Independent gap reconstruction

For each row, the checker subtracts the independently certified $16\pi$
prefix modulo $10^{18}$, sorts all 5,491,685 residues, rejects every zero
successive difference, and explicitly includes the wraparound difference.
Both rows have the same largest gap, between residues

```text
224581943086381218
224584679868386235
```

Their difference is exactly

\[
 \widetilde G=\frac{2736782005017}{10^{18}}.
\]

The wraparound gap is only $374051190571/10^{18}$.  The exact target
distance is $62123460130/10^{18}=6212346013/10^{17}$.

Fixed-endian SHA-256 values of the two independently sorted residue arrays
are

```text
pre-drop:   06e0ace0a02971804f3bdfdc8577c668c4795e5dd69e260dfd40965defcebee3
first-drop: 09a235b21296d40123e655ce3de78fc2598690cc649fcb32adf4c566ded38722
```

Applying (A16.1) alone to the actual pi orbit yields

\[
 G_\pi<\widetilde G+2\cdot10^{-18}
       =\frac{2736782005019}{10^{18}}<10^{-5}.             \tag{A16.3}
\]

Translation by $16\pi$ is a circle isometry, so the same gap bound applies
to the unshifted points $\{10^n\pi\}$.

The first two Fourier magnitudes also agree with the primary float values to
less than $5\cdot10^{-15}$, despite being evaluated on the unshifted phases
and in blocks of 777,777 rather than 1,000,000.  They remain ordinary float
diagnostics and imply no Fourier-decay statement.

## 6. Five-digit consequence, checked two ways

### Gap implication (`proof sketch`)

Let a finite circle set have largest gap $G<\ell$.  If a half-open arc
$[a,a+\ell)$ contained no set point, let $y$ be the first set point
clockwise after $a$, and $x$ its predecessor.  The clockwise distance
from $a$ to $y$ is at least $\ell$, while the distance from $x$ to
$a$ is strictly positive; hence the complementary gap from $x$ to $y$
would exceed $\ell$, a contradiction.

Taking $\ell=10^{-5}$ in (A16.3) shows that every interval

\[
 \left[\frac{k}{10^5},\frac{k+1}{10^5}\right),
 \qquad 0\le k<10^5,
\]

contains some $\{10^n\pi\}$ in each row.  These are precisely the
five-digit decimal cylinders, including leading zeros.

### Direct prefix enumeration (`experiment`)

Independently of the gap implication, the checker takes the leading $p$
digits of every certified 18-digit unshifted window, for every $1\le p\le5$,
and constructs the complete frequency table.  Both rows give

| word length $p$ | distinct words | minimum multiplicity |
|---:|---:|---:|
| 1 | 10 | 548,224 |
| 2 | 100 | 54,419 |
| 3 | 1,000 | 5,247 |
| 4 | 10,000 | 460 |
| 5 | 100,000 | 23 |

Thus the finite length-five assertion does not depend solely on the
largest-gap implementation: every five-digit word is directly present, and
even the least frequent one occurs 23 times in either row.  This verifies all
words of lengths at most five only.  The checker explicitly emits
`asserts_words_length_6=false` and `asserts_v1=false`.

## 7. Reproduction and integrity

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.py \
  work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813.py
.venv/bin/python \
  work/ultrapi-resume/bbp_endpoint_e16_experiment_20260813_independent_check.py
```

The independent checker ends in `status=PASS`.  Its complete stdout,
including the final newline, has SHA-256

```text
c3cb9f506f25dff49469159623661ac877c64d31c3329414ffe7a2d18a94f3ee
```

It pins all six frozen inputs, verifies all five relative links in the primary
report, and finds no forbidden C0 control byte.  The final audit also checks
the links and control bytes of this file.  No primary artifact, formal file,
verification gate, or `ultrapi.md` was edited by this audit.

## Sharp handoff

Epoch 16 provides substantially stronger finite evidence than epoch 14 and a
concrete certified consequence: every decimal word through length five occurs
in the inspected pi prefix.  It does not alter the infinite problem's logical
status.  The missing step remains a uniform Archimedean estimate for all
sufficiently large endpoint epochs—or another genuinely infinite argument.
Without that new input, the endpoint gap law and canonical V1 remain
`conjecture`s.
