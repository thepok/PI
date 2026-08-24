# Sharp uniform entropy gap for one forbidden word

Status: `proof sketch`

This note records a narrowed entropy consequence for decimal streams. It
does not estimate the entropy of π and does not prove V1.

## Uniform extremizer

For a decimal word `w` of length `r >= 1`, let

\[
A_w(k)=\#\{u\in\{0,\ldots,9\}^k:u\text{ avoids }w\}.
\]

Then, uniformly in the identity and self-overlap pattern of `w`,

\[
A_w(k)\le A_{0^r}(k)\qquad(k\ge0).                 \tag{1}
\]

One direct proof couples the prefix-matching automaton for `w` to the run
length for `0^r`. At each nonabsorbing matching state there is exactly one
next digit which advances the match by one. Use the same Bernoulli event of
probability `1/10` to select that digit; on its complement choose uniformly
among the other nine digits. This still generates independent uniform decimal
digits. The matching state for `w` advances with every Bernoulli success and
can retain a nonzero prefix after a failure, whereas the `0^r` run resets to
zero. Thus the hitting time of `w` is at most the hitting time of `0^r`
pathwise, which proves (1) by comparing survival probabilities.

This sits on top of existing repository work rather than introducing the
single-word automaton route:
[`T12`](../../../TheoryLib/PiPositiveLowerBlockDensity/T12T12OverlappingForbiddenWordDimension.lean)--[`T16`](../../../TheoryLib/PiPositiveLowerBlockDensity/T16T16MatrixPowerEntropy.lean)
already formalize overlapping forbidden languages, prefix automata,
finite-prefix entropy, and matrix-power entropy.
The repository's existing
[prior-art record](ultrapi-campaign/sin_automaton_attack.md#9-literature-audit)
also records the classical string-overlap literature. This note makes no new
`literature-checked` claim. Its new retained content is the uniform
constant-word extremizer, the resulting closed threshold, and the local
selected-block consequence below.

## Closed Perron threshold and sharp boundary stream

Write `a_r(k)=A_{0^r}(k)`. Its exact recurrence is

\[
a_r(k)=10^k\quad(0\le k<r),\qquad
a_r(k)=9\sum_{j=1}^{r}a_r(k-j)\quad(k\ge r).       \tag{2}
\]

Let `rho_r` be the unique positive root in `[9,10)` of

\[
\rho_r^r=9\sum_{j=0}^{r-1}\rho_r^j,
\quad\text{equivalently}\quad
(10-\rho_r)\rho_r^r=9,                             \tag{3}
\]

and put `gamma_r=log(10/rho_r)`. Induction in (2) gives the finite sandwich

\[
\rho_r^k\le a_r(k)
 \le \left(\frac{10}{\rho_r}\right)^{r-1}\rho_r^k. \tag{4}
\]

Hence, for

\[
G_{k,r}=k\log 10-\log a_r(k),
\]

one has

\[
(k-r+1)\gamma_r\le G_{k,r}\le k\gamma_r
\qquad(k\ge r),                                    \tag{5}
\]

and omission of a length-`r` word from an infinite decimal stream `d` forces

\[
h_{10}(d)\le\frac{\log\rho_r}{\log 10}.             \tag{6}
\]

The scalar threshold in (6) is sharp. Enumerate every finite word avoiding
`0^r` as `u_1,u_2,...` and concatenate

\[
z_r=1u_1\,1u_2\,1u_3\cdots .                       \tag{7}
\]

The separator digit prevents `0^r` from crossing a join, while every avoiding
word occurs inside its listed block. Therefore the length-`k` factor language
of `z_r` is exactly the `0^r`-avoiding language, `p_{z_r}(k)=a_r(k)`, so

\[
h_{10}(z_r)=\frac{\log\rho_r}{\log10}
\quad\text{and}\quad 0^r\text{ is absent}.          \tag{8}
\]

This is an exact-stream boundary witness, including for the exact times-ten
orbit of `0.z_r`; the strict sufficient inequality reverse to (6) cannot be
weakened to equality.

For `r >= 2`, the new sufficient entropy premise is numerically weaker than
the machine-checked T1 premise:

\[
\frac{\log\rho_r}{\log10}
 <\frac{\log(10^r-1)}{r\log10}.                    \tag{9}
\]

At `r=1` they agree. At the finite boundary `k=r`,

\[
G_{r,r}=\log\frac{10^r}{10^r-1},                   \tag{10}
\]

so the old one-block omission cost is retained exactly and the gain comes
from using every overlapping start as `k` grows. Equation (9) is a strict
numerical weakening of a scalar premise, not a proved strict separator
between the corresponding π-level predicates.

## Finite selected-block certificate

Let `B=[A,A+L)` be `L >= 1` consecutive starting positions in a decimal
stream. Let `p_{B,k}` be the empirical law of the length-`k` words starting in
`B`, and define

\[
H_k(B)=-\sum_u p_{B,k}(u)\log p_{B,k}(u),\qquad
D_k(B)=k\log10-H_k(B).                              \tag{11}
\]

For `k >= r`, set

\[
\alpha=\min\left(1,\frac{k-r}{L}\right),\qquad
h_2(t)=-t\log t-(1-t)\log(1-t).                    \tag{12}
\]

If a prescribed length-`r` word is absent at every start in `B`, then

\[
D_k(B)+h_2(\alpha)\ge(1-\alpha)G_{k,r}.             \tag{13}
\]

Indeed, the `L-(k-r)` internal starts (when positive) produce length-`k`
words avoiding the target, while the final `k-r` starts may be arbitrary.
Conditioning on those two classes bounds the entropy by their binary-mixture
entropy plus the two support entropies. Thus either strict reverse inequality

\[
D_k(B)+h_2(\alpha)<(1-\alpha)G_{k,r},               \tag{14}
\]

or the stronger closed condition obtained by replacing `G_{k,r}` with
`(k-r+1)gamma_r`, forces all `10^r` words to occur at starts in `B`. The
endpoint proportion and `h_2` mixture slack are retained; no local sharpness
claim is made.

Since `H_k(B) <= log L`, one also has

\[
L\ge10^k e^{-D_k(B)}.                               \tag{15}
\]

Put

\[
\bar\alpha=\frac{(k-r)e^{D_k(B)}}{10^k}.            \tag{16}
\]

If `bar alpha <= 1/2`, then `alpha <= bar alpha`, and the entirely length-free
certificate

\[
D_k(B)+h_2(\bar\alpha)
 <(1-\bar\alpha)(k-r+1)\gamma_r                    \tag{17}
\]

forces simultaneous coverage of every length-`r` word in `B`.

## Moving depth from the existing entropy premise

For selected consecutive blocks `B_j`, suppose `k_j -> infinity` and

\[
D_j:=D_{k_j}(B_j),\qquad D_j/k_j\longrightarrow0.   \tag{18}
\]

For all sufficiently large `j`, define

\[
r_j=\left\lfloor
\log_{10}\frac{k_j}{D_j+1}
\right\rfloor-1.                                   \tag{19}
\]

Then `r_j -> infinity`, and every word of length `r_j` occurs at a start in
`B_j` for every sufficiently large `j`. The estimate follows from
`gamma_r > 9/10^(r+1)`, (15), and (17): the right side of (17) eventually
dominates `D_j+1`, while `bar alpha_j -> 0`. Appending zeros transfers the
same-stage result to every shorter word.

This makes the existing sublinear canonical-entropy premise quantitatively
stronger as a consumer: it yields simultaneous moving-depth coverage, not
only eventual coverage at each fixed depth. It still supplies no π-specific
entropy estimate, no selected blocks for π, no absolute occurrence deadline,
and no proof of V1. Occurrences are arbitrarily late only under an additional
condition such as `A_j -> infinity`.
