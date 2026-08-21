# T16: The Decimal Thue-Morse Countermodel

Status: `proof sketch`. The Diophantine input is a source-pinned published
theorem. All deductions needed for the countermodel are given below, but they
are not machine-checked.

## Scope and immutable problem

The immutable statement is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Canonical V1 asks whether every finite decimal word occurs contiguously in the
decimal expansion of pi. It remains open.

This note constructs an artificial decimal number whose digit stream has all
of the following properties:

1. exact irrationality exponent 2;
2. factor complexity between `n + 1` and `8n` at every positive length `n`;
3. adjacent digit-change density `2/3`;
4. exactly two recurrent digits, namely 0 and 1;
5. no occurrence of the one-letter word 2.

Thus even this simultaneous strengthening of the generic information behind
T11, T13, and T14 does not imply decimal disjunctivity. This is a logical
countermodel to an implication between generic digit invariants. It establishes
nothing about the digits of pi and makes no progress on canonical V1 (or on
sibling V3 for pi).

## 1. Definitions and quantifiers

Let `sigma` be the length-two substitution

```text
sigma(0) = 01,    sigma(1) = 10.
```

For `k >= 0`, the word `sigma^k(0)` is a prefix of `sigma^(k+1)(0)`.
Their limit is the one-sided Thue-Morse word

```text
t = t_0 t_1 t_2 ... = 0110100110010110... .
```

Equivalently, and without relying on the displayed finite prefix,

```text
t_0 = 0,    t_(2j) = t_j,    t_(2j+1) = 1 - t_j    (j >= 0).       (1)
```

The decimal Thue-Morse number used here is

```text
alpha = sum_(j>=0) t_j / 10^(j+1) = 0.0110100110010110... (base 10). (2)
```

This fixes the indexing ambiguity: `t_0` is the first digit after the decimal
point. It also differs by a factor of 10 from Bugeaud's convention below.

For `n >= 1`, define the factor complexity

```text
p_t(n) = #{ (t_i,...,t_(i+n-1)) : i >= 0 }.
```

A decimal digit `a` is called recurrent in `t` when

```text
for every M >= 0 there is an i >= M with t_i = a.                  (3)
```

For `M >= 0`, let

```text
Delta_i = 1 if t_i != t_(i+1), and 0 otherwise,
S(M) = sum_(0 <= i < M) Delta_i.                                  (4)
```

Thus `S(M)` counts changes across the `M` adjacent pairs in the first `M+1`
digits. The assertion that the change density is `2/3` means the full limit

```text
lim_(M -> infinity) S(M)/M = 2/3,                                 (5)
```

not merely a limit along powers of two.

Finally, for an irrational real `x`, its irrationality exponent is

```text
mu(x) = sup {u : |x - p/q| < 1/q^u for infinitely many rationals p/q}.
```

The denominators may equivalently be required positive and the fractions
reduced.

## 2. Primary-source pin for the irrationality exponent

Yann Bugeaud, *On the rational approximation to the Thue-Morse-Mahler
numbers*, Annales de l'Institut Fourier 61 (2011), no. 5, 2065-2076.

- DOI: <https://doi.org/10.5802/aif.2666>
- Publisher article page:
  <https://aif.centre-mersenne.org/articles/10.5802/aif.2666/>
- Publisher PDF:
  <https://aif.centre-mersenne.org/item/10.5802/aif.2666.pdf>
- Retrieved 2026-07-21 as `bugeaud-2011-thue-morse-mahler.pdf`.
- PDF size: 580980 bytes; 13 pages.
- PDF SHA-256:
  `45df208f67a6fa75430631a9fc596fd1f6646b009b25ce2ea1852a2133c764ea`.
- `pdftotext -layout` output retained as
  `bugeaud-2011-thue-morse-mahler.txt`.
- Poppler version used: `pdftotext 22.12.0`.
- Extracted-text SHA-256:
  `2c7c6b99a7b2ab65c502599e00e76860e19df4db9ca6aaf96b5216ad39feffc5`.

Reproduce the retained source files from this artifact directory with:

```sh
curl -fL --retry 3 \
  -o "bugeaud-2011-thue-morse-mahler.pdf" \
  "https://aif.centre-mersenne.org/item/10.5802/aif.2666.pdf"
pdftotext -layout "bugeaud-2011-thue-morse-mahler.pdf" \
  "bugeaud-2011-thue-morse-mahler.txt"
sha256sum "bugeaud-2011-thue-morse-mahler.pdf" \
  "bugeaud-2011-thue-morse-mahler.txt"
```

The PDF is the authoritative source. The text hash can depend on the Poppler
version.

### Exact source convention and quotation

On printed p. 2067 (extracted-text lines 165-177), Bugeaud defines the same
word by `t_0 = 0`, `t_(2k) = t_k`, and `t_(2k+1) = 1 - t_k`, identifies it as
the fixed point of `sigma(0)=01, sigma(1)=10`, and defines

```text
xi_(t,b) = sum_(k>=0) t_k / b^k.                                  (6)
```

The exact theorem sentence on printed p. 2068, Section 2, physical PDF p. 5
(extracted-text lines 215-219), is:

> “Theorem. — For any integer b ⩾ 2, the irrationality exponent of the
> Thue–Morse–Mahler number \(\xi_{\mathbf t,b}\) is equal to 2.”

This preserves the words and punctuation and typesets the two mathematical
expressions as they appear in the rendered PDF. For a direct extraction check,
the retained text has `b ⩾ 2` and `ξt,b` at lines 218-219; Poppler flattens the
bold subscript on `t`. The rendered PDF is authoritative. The paper defines the
exponent on printed p. 2065 (extracted-text lines 79-86) as the supremum of real
exponents for which `|xi-p/q| < 1/q^mu` has infinitely many rational solutions.

### Transfer to the requested decimal convention

At `b=10`, equations (2) and (6) give

```text
xi_(t,10) = 10 alpha.                                              (7)
```

For completeness, multiplication by a positive integer `m` preserves the
irrationality exponent. Here is the denominator check.

Suppose first that `|x-p/q| < q^(-u)` infinitely often. For every
`0 < v < u` and all sufficiently large `q`,

```text
|mx-mp/q| < m q^(-u) < q^(-v).
```

After reducing `mp/q`, its denominator `Q` satisfies `Q <= q`, hence
`q^(-v) <= Q^(-v)`. Irrationality ensures the reduced approximants are
infinitely many and their denominators are unbounded. Therefore
`mu(mx) >= mu(x)`.

Conversely, suppose `|mx-p/q| < q^(-u)` infinitely often. Dividing by `m`
gives the rational `p/(mq)`. Its reduced denominator `Q` satisfies `Q <= mq`.
For every `0 < v < u` and all sufficiently large `q`,

```text
|x-p/(mq)| < m^(-1) q^(-u) < (mq)^(-v) <= Q^(-v).
```

Thus `mu(x) >= mu(mx)`. Consequently `mu(mx)=mu(x)`. Applying this with
`m=10`, equation (7), and Bugeaud's theorem proves

```text
mu(alpha) = 2.                                                     (8)
```

In particular `alpha` is irrational.

The series (2) really has `t` as its decimal digit stream. For each `N`, the
tail after the first `N` digits is at most

```text
sum_(j>=N) 10^(-(j+1)) = 10^(-N)/9 < 10^(-N).
```

Therefore flooring `10^N alpha` recovers the integer represented by the first
`N` digits. Also, a number with two decimal expansions has one expansion
eventually equal to 0 and the other eventually equal to 9. The present stream
is neither: it contains no 9, while recurrence (1) gives
`t_(2^k)=t_1=1` for every `k>=0`. Hence (2) is unambiguous.

## 3. Substitution proof of the linear complexity bound

Fix `n >= 1`. For `n=1`, both symbols occur (`t_0=0`, `t_1=1`), so
`p_t(1)=2 <= 8`.

Now let `n >= 2`, and choose the least `k` such that

```text
n <= L := 2^k.                                                     (9)
```

Minimality gives `2^(k-1) < n`, hence

```text
L < 2n.                                                           (10)
```

Because `sigma` has constant length 2 and `t=sigma^k(t)`, the infinite word
has the canonical level-`k` block decomposition

```text
t = sigma^k(t_0) sigma^k(t_1) sigma^k(t_2) ... ,                  (11)
```

where every block has length `L`.

Take an arbitrary length-`n` factor starting at position `i`. Divide `i` by
`L`:

```text
i = qL+r,    0 <= r < L.                                         (12)
```

Since `n <= L`, the factor lies entirely in the two-block word

```text
sigma^k(t_q) sigma^k(t_(q+1)).                                   (13)
```

Indeed its last relative position is at most
`r+n-1 <= (L-1)+L-1 < 2L`. Thus the factor is determined by:

1. the offset `r`, with `L` possibilities;
2. the ordered bit pair `(t_q,t_(q+1))`, with at most 4 possibilities.

Different choices may produce the same factor, which only improves the upper
bound. Therefore

```text
p_t(n) <= 4L < 8n.                                                (14)
```

Combining the `n=1` case with (14) gives the explicit all-length bound

```text
p_t(n) <= 8n    for every n >= 1.                                 (15)
```

There is also a matching linear lower bound. If `t` were eventually periodic,
the series (2) would be a rational number: split off its finite prefix and sum
the repeating tail as a finite numerator over `1-10^(-r)`, where `r` is the
period. This contradicts (8). The one-sided Morse-Hedlund implication used in
accepted T11 says that a non-eventually-periodic word satisfies

```text
n+1 <= p_t(n)    for every n >= 1.                                (16)
```

This reuses the program's accepted generic theorem rather than reproving it;
from this note its record-relative path is
[`../knowledge_library/t11/PiDigitFactorComplexity.lean`](../knowledge_library/t11/PiDigitFactorComplexity.lean),
especially the Morse-Hedlund application at lines 156-163. Equations
(15)-(16) show that this countermodel has genuinely linear, unbounded factor
complexity, not merely a linear upper estimate for an eventually periodic
word.

## 4. Substitution proof of change density 2/3

The substitution immediately gives recurrence (1). Apply it to each adjacent
pair. For every `j >= 0`,

```text
Delta_(2j) = 1,                                                   (17)
```

because `t_(2j)=t_j` and `t_(2j+1)=1-t_j` are opposite bits. For the
next edge,

```text
Delta_(2j+1) = 1-Delta_j.                                        (18)
```

To verify (18), its endpoints are `1-t_j` and `t_(j+1)`. These endpoints
differ exactly when `t_j=t_(j+1)`, which is exactly when `Delta_j=0`.

Pairing edges `(2j,2j+1)` in definition (4) now gives, for every `m >= 0`,

```text
S(2m)   = sum_(j<m) (1 + 1-Delta_j) = 2m-S(m),                   (19)
S(2m+1) = S(2m)+Delta_(2m) = 2m-S(m)+1.                          (20)
```

These formulas cover every prefix length. Define the integer error

```text
E(M) = 3S(M)-2M.                                                  (21)
```

Substitution of (19)-(20) into (21) gives

```text
E(2m)   = -E(m),                                                  (22)
E(2m+1) = 1-E(m).                                                 (23)
```

Repeatedly replacing `M` by `floor(M/2)` reaches zero after at most
`floor(log_2 M)+1` steps. Equation (22) does not increase absolute value and
(23) increases it by at most 1. Since `E(0)=0`, for every `M>=1`,

```text
|E(M)| <= floor(log_2 M)+1.                                      (24)
```

Divide (21) by `3M`:

```text
S(M)/M = 2/3 + E(M)/(3M).                                        (25)
```

The bound (24) makes the last term tend to zero. Hence the full, all-prefix
limit is

```text
lim_(M -> infinity) S(M)/M = 2/3.                                (26)
```

As a check derived from the same recurrences, `E(1)=1` and (22) give

```text
S(2^k) = (2^(k+1)+(-1)^k)/3.
```

This dyadic identity is not used to infer the full limit; (22)-(25) do that.
For the first `N` digits there are `N-1` adjacent pairs, so (26) equivalently
says their number of changes divided by `N-1` tends to `2/3`.

## 5. Exact recurrent digits and explicit failure of disjunctivity

Recurrence (1) proves directly that every term is in `{0,1}`. Thus none of the
decimal digits 2 through 9 occurs even once.

Both 0 and 1 occur arbitrarily late, with explicit witnesses rather than a
finite-prefix search. First `t_1=1-t_0=1` and repeated use of `t_(2j)=t_j`
gives

```text
t_(2^k) = t_1 = 1    for every k >= 0.                            (27)
```

Also `t_3=1-t_1=0`, so

```text
t_(3*2^k) = t_3 = 0    for every k >= 0.                          (28)
```

The two index families are unbounded. Equations (27)-(28), together with the
alphabet restriction, prove that the recurrent decimal digits are exactly 0
and 1 in the quantified sense (3).

A decimal stream is disjunctive only if every one-letter decimal word occurs.
The one-letter word `2` does not occur in `t`, so `alpha` is not disjunctive.
This is an explicit universal consequence of the substitution alphabet, not
an inference from examining any finite prefix.

## 6. What the countermodel separates

The same single stream simultaneously has:

- the T11-style lower complexity `p_t(n)>=n+1`, and even the upper bound
  `p_t(n)<=8n`;
- exactly two recurrent digits, strengthening the existential two-digit
  conclusion behind T13;
- positive change density `2/3`, vastly stronger than the logarithmic
  change-count lower bound behind T14;
- exact irrationality exponent 2, the smallest possible exponent for an
  irrational real;
- failure of decimal disjunctivity witnessed by the missing block `2`.

Therefore no theorem using only that package of generic invariants can imply
decimal disjunctivity. This conclusion does not transfer any property to pi.
In particular, it does not prove or disprove canonical V1 and does not resolve
sibling V3 for pi.

## 7. Bounded literature check

Search date: 2026-07-21.

1. A Crossref title search for `irrationality exponent Thue-Morse constant`
   located later work and its reference to Bugeaud's DOI
   `10.5802/aif.2666`.
2. The Centre Mersenne publisher record and PDF for that DOI were inspected.
   The PDF itself contains the sequence convention, exponent definition, and
   exact theorem quoted above.
3. Badziahin and Zorin, *Thue-Morse Constant is Not Badly Approximable*, DOI
   `10.1093/imrn/rnu238`, was excluded as the primary source for (8): it proves
   non-bad-approximability, not Bugeaud's earlier exact exponent theorem.

This was a targeted source check for the theorem used here, not an exhaustive
novelty survey. No novelty claim is made.
