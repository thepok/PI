# T14: Irrationality Measure and Decimal Digit Changes of Pi

Status: `proof sketch`. The published Diophantine input is source-pinned below,
and every deduction from it is written out. This note is not machine-checked.

## Provenance and scope

The immutable problem statement is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Its original source URL is local to this program; the exact immutable file is
the canonical source. It asks V1: whether every finite decimal string occurs
contiguously in pi. It separately records sibling V3: whether every infinite
decimal stream is a subsequence, equivalently whether every digit occurs
infinitely often.

This note proves only a lower bound on the total number of changes among the
first `N` decimal digits. It does **not** prove that every digit recurs
infinitely often, that every finite block occurs, or that any computed finite
prefix has resolution value. In particular, it proves neither canonical V1
nor sibling V3.

## Normalized statement

For `n >= 0`, put

\[
  a_n=\lfloor 10^n\pi\rfloor.
\]

For `n >= 1`, define the `n`th digit after the decimal point by

\[
  d_n=a_n-10a_{n-1}.
\]

The floor inequalities show `0 <= d_n <= 9`. For `N >= 1`, define

\[
 C_\pi(N)=\#\{i\in\mathbb Z:1\le i<N\text{ and }d_i\ne d_{i+1}\}.
\]

Thus `C_pi(N)` counts adjacent changes *within the first `N` digits*; there are
`N-1` possible change positions. We prove that there are real constants
`c > 0`, `C`, and an integer `N0` such that

\[
 C_\pi(N)\ge c\log N-C\qquad(N\ge N_0),
\]

where `log` is the natural logarithm. One admissible choice below is

\[
 c=\frac1{\log 8},\qquad N_0=1,
\]

with `C` explicitly defined from the finite-exception constant `kappa` in
Step 1.

The quantifiers are therefore: there exist constants independent of `N`, and
the bound holds for every integer `N >= N0`. No assertion is made about the
locations or identities of the changing digits.

## Published input

### Source pin

V. Kh. Salikhov, *On the irrationality measure of pi*, Russian Mathematical
Surveys 63:3 (2008), 570-572.

- DOI: <https://doi.org/10.1070/RM2008v063n03ABEH004543>
- Stable Math-Net record: <https://www.mathnet.ru/eng/rm9175>
- Math-Net English-version PDF URL:
  <https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9175&what=fullteng&option_lang=eng>
- Retrieved 2026-07-21 as `salikhov-2008-pi-irrationality.pdf`.
- Retrieved PDF SHA-256:
  `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d`.
- `pdftotext -layout` output:
  `salikhov-2008-pi-irrationality.txt`.
- Extracted with Poppler `pdftotext` version `22.12.0`; extraction hashes can
  vary across Poppler versions even when the authoritative PDF is identical.
- Extracted-text SHA-256:
  `e05fcf2c6941386ab51d0bb2705110f4e67660d7669d9f2a92d9c3e9a9466699`.

The IOP/Crossref publisher link led to an access page in this session. The
successful source is the English published version supplied by Math-Net and
linked from the stable Math-Net bibliographic record. There is no source
blocker.

Reproduce the retained files and hashes from the artifact directory with:

```sh
curl -fL -A "Mozilla/5.0" \
  -e "https://www.mathnet.ru/eng/rm9175" \
  "https://www.mathnet.ru/php/getFT.phtml?jrnid=rm&paperid=9175&what=fullteng&option_lang=eng" \
  -o "salikhov-2008-pi-irrationality.pdf"
pdftotext -layout "salikhov-2008-pi-irrationality.pdf" \
  "salikhov-2008-pi-irrationality.txt"
sha256sum "salikhov-2008-pi-irrationality.pdf" \
  "salikhov-2008-pi-irrationality.txt"
```

### Exact quotations

The following transcriptions preserve the words, punctuation, and formula
content of the rendered PDF; line wrapping is normalized and formulas are
rendered in plain Markdown.

**Q1 (Theorem 1, printed p. 570; extracted-text lines 13-17):**

> "Theorem 1. For all p, q in N with q >= q_0 the following inequality holds:
> |pi - p/q| >= q^(-nu), where nu = 7.6063...."

The four tall absolute-value strokes are visible around `pi - p/q` in the
rendered PDF. Poppler's `pdftotext -layout` drops those glyphs at extracted-text
lines 13-17, although it does preserve the same absolute-value notation in the
introductory version at extracted-text lines 7-8. The PDF, not that known text
extraction loss, is authoritative for Q1. This observation is also directly
checkable by rendering printed p. 570.

The displayed decimal in Q1 is abbreviated by ellipsis. The exact usable
comparison is supplied at the end of the proof.

**Q2 (printed p. 571; extracted-text lines 117-124):**

> "Applying Remark 2.1 in [6] to the linear form epsilon_n ≡ Q_n epsilon'_n
> (see (4)) we deduce that the inequality (1) holds for any
> nu > 1 - (chi + log |g(t_3)|)/(chi + log |g(t_1)|) = 7.60630852...,
> and the theorem follows."

Only the consequence with `nu = 8` is used below. It is valid because
`8 > 7.60630852...`; no claim at the rounded exponent `7.6063` is needed.
Consequently there exists an integer `q0 >= 1` such that

\[
 \left|\pi-\frac pq\right|\ge q^{-8}
 \tag{S}
\]

for all positive integers `p,q` with `q >= q0`.

## Proof

### Step 1: make the Diophantine bound uniform

First, (S) itself implies that pi is irrational. If `pi = p/q`, multiply both
`p` and `q` by an integer `t` for which `tq >= q0`; (S) would then say
`0 >= (tq)^(-8) > 0`, a contradiction.

We need (S) also for the finitely many small denominators that can occur in
the rational approximations below. Let

\[
 \mathcal F=\{(p,q)\in\mathbb N^2:
   1\le q<q_0,\ 1\le p\le4q\}.
\]

This set is finite. Every number
`q^8 |pi-p/q|` indexed by `F` is strictly positive because pi is irrational.
Define

\[
 \kappa=
 \min\left(\{1\}\cup
   \left\{q^8\left|\pi-\frac pq\right|:(p,q)\in\mathcal F\right\}\right).
\]

The union contains `1`, so the minimum exists even if `F` is empty. Moreover,

\[
 0<\kappa\le1.
\]

Combining its definition for `q < q0` with (S) for `q >= q0` gives

\[
 \left|\pi-\frac pq\right|\ge\kappa q^{-8}
 \tag{U}
\]

whenever `p,q` are positive integers, `q >= 1`, and `p/q <= 4`. This is the
only globalization of Salikhov's estimate used later. It introduces no
ineffective infinite choice: `kappa` is the minimum of an explicitly displayed
finite set determined by the theorem's `q0`.

### Step 2: canonical decimal expansion and its ambiguity

From

\[
 a_{n-1}\le10^{n-1}\pi<a_{n-1}+1
\]

we get

\[
 10a_{n-1}\le10^n\pi<10a_{n-1}+10.
\]

Taking floors gives

\[
 10a_{n-1}\le a_n\le10a_{n-1}+9,
\]

so `d_n=a_n-10a_(n-1)` is an integer in `{0,...,9}`.

The identity `a_n=10a_(n-1)+d_n` telescopes to

\[
 \frac{a_N}{10^N}=a_0+\sum_{i=1}^N d_i10^{-i}.
 \tag{D1}
\]

Because `3 < pi < 4`, `a_0=3`. The defining floor inequality also gives

\[
 0\le\pi-\frac{a_N}{10^N}<10^{-N}.
 \tag{D2}
\]

Letting `N` tend to infinity in (D1)-(D2) proves

\[
 \pi=3+\sum_{i=1}^{\infty}d_i10^{-i}.
 \tag{D}
\]

This floor convention chooses the terminating-with-zeroes expansion when a
number has two decimal representations. For pi there is in fact no
ambiguity: an eventually-zero or eventually-nine decimal expansion sums to a
rational number, whereas Step 1 proved pi irrational. Thus (D), rather than an
unstated choice between `0.5000...` and `0.4999...`, is the digit stream used
throughout.

### Step 3: a constant run gives a rational approximation

Suppose positions `m+1,m+2,...,n`, where `0 <= m < n`, all contain the same
digit `d`:

\[
 d_{m+1}=d_{m+2}=\cdots=d_n=d.
 \tag{R}
\]

Replace all digits after position `m` by `d` and define

\[
 r_{m,d}=\frac{a_m}{10^m}+\sum_{i=m+1}^{\infty}d10^{-i}
          =\frac{a_m}{10^m}+\frac{d}{9\,10^m}
          =\frac{9a_m+d}{9\,10^m}.
 \tag{A1}
\]

Set

\[
 P=9a_m+d,\qquad Q=9\,10^m.
\]

Both are positive integers. Reduction to lowest terms is unnecessary because
(U), like Salikhov's statement, applies to every integer presentation `P/Q`.
Also `a_m < 4*10^m`, hence `a_m <= 4*10^m-1`; therefore

\[
 0<\frac PQ
 =\frac{a_m}{10^m}+\frac d{9\,10^m}
 \le\frac{4\,10^m-1}{10^m}+\frac1{10^m}=4.
 \tag{A2}
\]

Using (D), (R), and (A1), all terms through position `n` cancel:

\[
 \pi-r_{m,d}=\sum_{i=n+1}^{\infty}(d_i-d)10^{-i}.
\]

Since both `d_i` and `d` lie in `{0,...,9}`,

\[
 \begin{aligned}
 |\pi-r_{m,d}|
 &\le\sum_{i=n+1}^{\infty}|d_i-d|10^{-i}\\
 &\le9\sum_{i=n+1}^{\infty}10^{-i}\\
 &=9\frac{10^{-(n+1)}}{1-10^{-1}}\\
 &=10^{-n}.
 \end{aligned}
 \tag{A3}
\]

This estimate includes `d=0` and `d=9`; no endpoint case or alternate decimal
representation was discarded.

### Step 4: bound every constant run

Apply (U) to the `P,Q` in (A1)-(A2), then use (A3):

\[
 \kappa(9\,10^m)^{-8}
 \le|\pi-r_{m,d}|
 \le10^{-n}.
\]

Taking base-10 logarithms, which preserve inequalities between positive
quantities, gives

\[
 \log_{10}\kappa-8\log_{10}9-8m\le-n.
\]

Equivalently,

\[
 n\le8m+A,
 \qquad
 A=8\log_{10}9-\log_{10}\kappa.
 \tag{B}
\]

Because `0 < kappa <= 1`, `A > 0`. Formula (B) is the required constant-run
bound: a run ending at `n` cannot have started after position `m` with `n`
much larger than `8m` plus the fixed constant `A`.

### Step 5: iterate over the run endpoints

Fix `N >= 1`. Partition `d_1,...,d_N` into maximal constant runs, and write
their endpoints as

\[
 0=n_0<n_1<\cdots<n_K=N.
\]

There is exactly one change between successive runs and none within a run, so

\[
 K=C_\pi(N)+1.
 \tag{C1}
\]

For each `j=1,...,K`, the digits in positions `n_(j-1)+1` through `n_j` are
constant. Applying (B) with `m=n_(j-1)` and `n=n_j` yields

\[
 n_j\le8n_{j-1}+A.
 \tag{C2}
\]

Induction on `j`, starting from `n_0=0`, now gives

\[
 n_j\le A(1+8+\cdots+8^{j-1})
       =A\frac{8^j-1}{7}.
 \tag{C3}
\]

Indeed, the assertion is immediate for `j=0`; if it holds at `j-1`, then

\[
 n_j\le8A\frac{8^{j-1}-1}{7}+A
      =A\frac{8^j-1}{7}.
\]

Taking `j=K` in (C3) and using `n_K=N` gives

\[
 N\le A\frac{8^K-1}{7},
 \qquad
 8^K\ge1+\frac{7N}{A},
\]

and hence

\[
 K\ge\frac{\log(1+7N/A)}{\log8}.
 \tag{C4}
\]

Combining (C1) and (C4) proves the sharper bound

\[
 C_\pi(N)\ge
 \frac{\log(1+7N/A)}{\log8}-1.
 \tag{C5}
\]

Finally let

\[
 \delta=\min\{1,7/A\}>0.
\]

For every `N >= 1`, `1+7N/A >= delta*N`. Therefore (C5) implies

\[
 C_\pi(N)
 \ge\frac{\log N}{\log8}
   +\frac{\log\delta}{\log8}-1
 =c\log N-C,
\]

with the promised constants

\[
 \boxed{
 c=\frac1{\log8}>0,\qquad
 C=1-\frac{\log\delta}{\log8},\qquad
 N_0=1.}
\]

All of `kappa`, `A`, `delta`, `c`, `C`, and `N0` are independent of `N`.
The coefficient `c=1/log 8` and threshold `N0=1` are numerical. Salikhov's
theorem does not print a numerical value of `q0`, so the finite minimum
defining `kappa`, and hence the admissible additive constant `C`, is explicit
as a finite definition but is not numerically evaluated here. No numerical
value for `C` is claimed.

## What this establishes, and what it does not

The argument uses no unproved conjecture. Its external mathematical input is
Salikhov's published theorem quoted above. It shows that the number of adjacent
decimal digit changes in pi is unbounded, with an explicit logarithmic rate up
to an additive constant.

This is not evidence from a computed finite prefix; no digits of pi were
computed. Unboundedly many changes do imply, by the finite alphabet
pigeonhole principle, that at least two unspecified digits recur infinitely
often. They do not imply that every digit recurs infinitely often, so the
result does not prove sibling V3. It gives vastly less than occurrence of every
finite block and therefore does not prove canonical V1. No V1 or V3 resolution
claim is made.

## Literature search log

| Date | Source/query | Result |
|---|---|---|
| 2026-07-21 | DOI `10.1070/RM2008v063n03ABEH004543` and Crossref metadata | Confirmed author, title, journal, volume, issue, pages, and DOI; Crossref supplied the IOP link. |
| 2026-07-21 | Math-Net record `rm9175` | Located and retrieved the English published PDF; exact theorem and terminal exponent comparison inspected. |

This bounded search was for the exact Diophantine input needed here. It is not
an exhaustive novelty survey, and the note makes no novelty claim.
