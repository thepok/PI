# T99: fixed-pi intermediate-rung delta audit

Status: `literature-checked` on 2026-08-09 for the bounded corpus in
`SOURCE_MANIFEST.md`; the elementary deductions and separating constructions
below are a `proof sketch`. This report proves no instance of C1, C2, C7, or
G14. Its only terminal form is the negative map in Section 10.

## 1. Provenance, normalized question, and ambiguities

The canonical question was formulated locally and has no original external
source URL. Its byte-exact copy is `pi-positive-decimal-factor-entropy.txt`,
SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

Write the unique nonterminating decimal expansion as

```text
pi = 3.d_1 d_2 d_3 ...,
```

where positions are one-based in this report. For an infinite word `x`, let
`p_x(n)` be the number of distinct contiguous length-`n` factors beginning at
arbitrary positions. The canonical question asks whether one fixed `eta>0`
and one `N>=1` satisfy

```text
p_pi(n) >= 10^(eta*n) for every integer n>=N.           (1.1)
```

The following choices are fixed throughout.

1. Every property is a property of the complete one-sided word, not of a
   finite prefix or aligned blocks.
2. `log` means the natural logarithm; `log_10` is written explicitly.
3. `liminf` is over positive integers tending to infinity.
4. Irrationality exponents apply to `xi_pi=pi-3=sum d_k/10^k`; integer
   translation leaves the exponent unchanged.
5. A comparison arrow means implication for arbitrary one-sided decimal
   words with the displayed definitions. A crossed arrow has the explicit
   separating construction given in Section 6.
6. Source search is bounded and dated. No negative statement is about all
   literature.

## 2. Literal baseline and entropy statements

### Non-eventual-periodicity baseline

```text
For every A>=1 and every p>=1, there exists j>=A
such that x_j != x_(j+p).                               (2.NR)
```

Only after fixing this formula, abbreviate it by `NR(x)`. This is the literal
negation of eventual periodicity. For `x=d(pi)`, it
follows from irrationality: an eventually periodic decimal expansion
represents a rational number. Zeilberger--Zudilin's finite irrationality
measure in Source S1 in particular implies that `pi` is irrational.

### Morse--Hedlund linear-language baseline

```text
For every integer n>=1, p_x(n)>=n+1.                    (2.LL)
```

Only after fixing this formula, abbreviate it by `LL(x)`. Bugeaud--Kim Source
S2, Theorem 1.1, PDF pp. 1--2, states
that eventual periodicity is equivalent to the existence of `n>=1` with
`p_x(n)<=n`. Since `p_x(n)` is an integer, negating that statement gives

```text
NR(x) <=> LL(x).                                         (2.1)
```

Thus NR and LL are two literal forms of the unconditional pi baseline, not
two different strength levels.

### Positive decimal factor entropy

```text
There exist eta>0 and N>=1 such that
p_x(n)>=10^(eta*n) for every n>=N.                       (2.ENT)
```

Only after fixing this formula, abbreviate it by `ENT(x)`. For `x=d(pi)`,
this is literally C1 and (1.1), copied from the immutable canonical statement.
Consequently

```text
C1 <=> ENT(d(pi)),       ENT(x) => LL(x) <=> NR(x).       (2.2)
```

For the matrix, define the generic C1 schema by `C1(x):<=>ENT(x)`. If
`f_x(w;n,M)` counts starts `1<=i<=M` whose length-`n` factor is `w`, put

```text
E_x(n,M) := sum_w f_x(w;n,M)^2,

C2(x) :<=> there exist eta>0 and n0>=1 such that, for every n>=n0,
  there exists M>=1 with E_x(n,M)<=M^2*10^(-eta*n).      (2.C2)
```

The square sum is exactly the ordered, diagonal-inclusive equality-collision
count. At `x=d(pi)`, these schemas are the program's C1 and C2. The checked T2
file, hash-pinned in this package, states those exact pi quantifiers at lines
25--41 and machine-checks `C2 => C1` at lines 120--143. The same implication
for the generic schemas is the finite Cauchy inequality
`M^2<=p_x(n)*E_x(n,M)`. No converse is used.

## 3. Retained candidate DC: logarithmically many digit changes

For `N>=2`, define

```text
Chg_x(N) := |{j: 1<=j<N and x_j != x_(j+1)}|.
```

The first retained word-property schema is

```text
DC(x) :<=> NR(x) and
  liminf Chg_x(N)/log(N) >= 1/log(888/125).              (DC)

DC_pi :<=> DC(d(pi)).
```

Numerically,

```text
1/log(888/125)    = 0.510032854836...,
1/log_10(888/125) = 1.174394048484....                   (3.1)
```

The liminf statement means literally that for every real `epsilon>0`, there
is `N_epsilon>=2` such that every `N>=N_epsilon` satisfies

```text
Chg_pi(N)/log(N) >= 1/log(888/125)-epsilon.              (3.2)
```

### 3.1 Exact pi input

Zeilberger--Zudilin define the irrationality measure on printed p. 407 and,
using Propositions 7--8 on printed pp. 417--418, obtain

```text
mu(pi) <= 7.10320533413700172750577342281... < 7.104
       = 888/125.                                        (3.3)
```

Their definition implies that (3.3) supplies an integer `Q0` such that, for
every `q>=Q0` and `z in Z`,

```text
q^(-888/125) < |(pi-3)-z/q|.                            (3.4)
```

To see strictness without an equality assumption, choose a real exponent
strictly between the printed upper bound and `888/125`; its eventual
non-strict lower bound is strictly larger than `q^(-888/125)` for `q>1`.

### 3.2 Existing T36 implication, specialized at period one

The machine-checked T36 theorem
`effectiveIrrationality_periodic_window_gap`, lines 265--305 of the retained
file, says that an exact decimal periodic window beginning at zero-based
position `a`, of period `p` and length `W`, obeys

```text
W <= (mu-1)*a + mu*p + 1                                (3.5)
```

once its displayed denominator `10^a*(10^p-1)` passes `Q0`. A constant digit
run is exactly the case `p=1`. With `mu=888/125`, every sufficiently late run
therefore has

```text
W <= (763/125)*a + 888/125 + 1.                         (3.6)
```

Let `s_k` be successive zero-based starts of runs after the onset. Then
(3.6) gives

```text
s_(k+1) <= (888/125)*s_k + 888/125 + 1.                 (3.7)
```

Put `M=888/125` and `B=(M+1)/(M-1)`. Equation (3.7) is equivalent to

```text
s_(k+1)+B <= M*(s_k+B).                                 (3.8)
```

Iteration gives `s_k+B <= M^(k-k0)*(s_k0+B)`. Inverting this bound at a
position `N` proves (3.2). This is an unconditional fixed-pi corollary of the
pinned source and existing T36 infrastructure.

### 3.3 General threshold

For a requested coefficient `c>0`, this route needs some `M>mu(pi)` with
`1/log(M)>=c`. Equivalently, its exact pi threshold is

```text
mu(pi) < exp(1/c).                                      (3.9)
```

For the retained `c=1/log(888/125)`, threshold (3.9) is exactly
`mu(pi)<888/125`, and Source S1 reaches it.

## 4. Retained candidate REP: exponent of first repetition

Bugeaud--Kim Source S2 defines `r_x(n)` on PDF p. 2 as the length of the
shortest prefix containing two, possibly overlapping, occurrences of one
length-`n` factor. Definition 3.2 on PDF p. 6 defines

```text
rep(x) := liminf r_x(n)/n.
```

The second retained word-property schema and its pi instance are

```text
REP(x) :<=> rep(x) > 888/763.

REP_pi :<=> REP(d(pi)), where 888/763 = 1.163826998689....
```

Its fully exposed eventual form is: there exist `delta>0` and `N>=1` such
that every `n>=N` satisfies

```text
r_pi(n)/n >= 888/763 + delta.                           (4.1)
```

Theorem 4.2, PDF p. 9, states for every non-eventually-periodic base-`b`
word `x` that

```text
mu(sum_(k>=1) x_k/b^k) >= rep(x)/(rep(x)-1),            (4.2)
```

with the right side infinite when `rep(x)=1`. Combining (3.3) and (4.2), and
using that `r/(r-1)` is strictly decreasing for `r>1`, gives

```text
rep(d(pi)) > 888/763,                                   (4.3)
```

because `(888/763)/(888/763-1)=888/125` exactly.

For any requested `rho>1`, the exact pi threshold for this argument is

```text
mu(pi) < rho/(rho-1).                                   (4.4)
```

At `rho=888/763`, Source S1 reaches (4.4).

This result is deliberately not promoted as an admissible T99 direction.
Its defining object is literally the first collision of two length-`n`
factors, and the proof of Source S2 constructs rational approximants by
cutting a prefix and completing periodically. It is therefore a collision and
periodic-completion reformulation excluded by the agenda.

## 5. Ordered-target matrix

Every matrix entry is justified in Section 6. `Equivalent` and `implies` are
logical relations between the displayed word properties. `Incomparable`
means both nonimplications have explicit witnesses.

| Retained schema | `NR(x)` | `LL(x)` | `ENT(x)` | `C1(x)` | `C2(x)` |
|---|---|---|---|---|---|
| `DC(x)` | **implies**, by its first conjunct | **implies**, by NR `<=>` LL | **incomparable** | **incomparable**, since `C1(x)<=>ENT(x)` | **incomparable** |
| `REP(x)` | **implies**, Source S2 Theorem 2.3 | **implies**, by NR `<=>` LL | **incomparable** | **incomparable**, since `C1(x)<=>ENT(x)` | **incomparable** |

The fixed background order is

```text
C2(x) => C1(x) <=> ENT(x) => LL(x) <=> NR(x).           (5.1)
```

The matrix compares schemas; `DC_pi` and `REP_pi` are their fixed-pi
instances established in Sections 3--4. No matrix relation is used to infer
C1, C2, C7, or G14 for pi.

## 6. Proofs of every matrix comparison

### 6.1 DC versus the baseline

`DC=>NR` is a conjunct, and `NR<=>LL` is (2.1).

For `DC` without ENT, use the Fibonacci word. Source S3, printed p. 200
(PDF p. 3), defines it by iterating `a->ab`, `b->a`; rename `a->0`, `b->1`.
Source S2, PDF p. 5, identifies this Fibonacci word as Sturmian, so
`p_f(n)=n+1` for every `n>=1` by Definition 1.2. It therefore fails ENT.
The morphism has no `11` and no `000`: images begin in `0`, every `1` is the
second symbol of `01`, and induction preserves those two exclusions. Hence
every three consecutive positions contain a change, so
`Chg_f(N)>=(N-2)/3`. It satisfies DC's logarithmic change conclusion and NR,
but not ENT, C1, or C2 (the last because C2 implies ENT).

For C2 without DC, construct a decimal word in alternating stages. At a
sabotage stage append a constant-zero run so long that at its endpoint `N_k`,

```text
Chg(N_k)/log(N_k) < 1/k.                                (6.1)
```

This is possible because the numerator remains fixed while the run grows. At
the following repair stage append sufficiently many periods of a cyclic
base-10 de Bruijn word of order `k`. In the infinite periodic de Bruijn word,
each length-`k` factor has frequency exactly `10^(-k)`. As the number of
appended periods tends to infinity, the finite earlier prefix and the two
boundaries have vanishing relative weight, so at some prefix length `M_k`,

```text
E_x(k,M_k)/M_k^2 <= 10^(-k/2).                          (6.2)
```

Here `E_x` is the ordered, diagonal-inclusive equality-collision count in
(2.C2). Equation (6.2) for every `k>=1` is `C2(x)` with `eta=1/2`. But (6.1) makes the
change-count liminf zero, so DC fails. Thus C2, and hence ENT/C1, does not
imply DC. Together with the Fibonacci witness this proves every DC
incomparability in the matrix.

The convergence used in (6.2) is finite counting, not a probabilistic claim:
over each complete de Bruijn period every length-`k` word occurs once, while
the number of starts meeting the fixed old prefix or an incomplete boundary
is independent of the number of appended periods.

### 6.2 REP versus the baseline

Source S2 Theorem 2.3, PDF p. 4, says eventual periodicity is equivalent to
bounded `r_x(n)-n`; hence every eventually periodic word has `rep(x)=1`.
Therefore `REP=>NR=>LL`.

REP does not imply ENT, C1, or C2. Source S2 states on PDF p. 7 that the
Fibonacci word has `rep(f)=phi=(1+sqrt(5))/2`; elementary arithmetic gives
`phi>888/763`. The same source says it is Sturmian, so `p_f(n)=n+1` and ENT
fails. Since C2 implies ENT, C2 fails as well.

Conversely, build a C2 word with repetition exponent one. Suppose a finite
prefix `V_k` has already been built. Repeat the entire word `V_k` exactly
`R_k` times, where `R_k` tends to infinity. With

```text
n_k=(R_k-1)*|V_k|,
```

the length-`n_k` factors beginning at positions `1` and `|V_k|+1` are equal,
so

```text
r_x(n_k)/n_k <= R_k/(R_k-1) -> 1.                       (6.3)
```

After this periodic-prefix stage, append enough periods of a cyclic de
Bruijn word of order `k` to enforce (6.2), and call the complete result
`V_(k+1)`. These prefixes are nested, so they define one infinite word.
The universal bound `r_x(n)>=n+1` and (6.3) give `rep(x)=1`, while the repair
stages give `C2(x)` with `eta=1/2`. Thus C2, ENT, and C1 do not imply REP. This and
the Fibonacci witness prove every REP incomparability in the matrix.

## 7. Source-threshold audit and bounded current search

Only three primary sources are retained, below the limit of six. The two pi
thresholds are already reached by Source S1:

| Candidate | Required pi threshold | Pinned literature | Verdict |
|---|---|---|---|
| DC coefficient `c` | `mu(pi)<exp(1/c)` | S1 gives `mu(pi)<888/125`; at `c=1/log(888/125)` the threshold is exact | reached, but duplicate of T36 period one |
| REP level `rho` | `mu(pi)<rho/(rho-1)` | S1 gives the exact threshold at `rho=888/763` | reached, but forbidden collision reformulation |

Search date: 2026-08-09 UTC.

1. The accepted local library was searched first. T5, T15, T36, T45, T60,
   T67, T79, T87, T88, and T98 were inspected before external queries.
2. arXiv API query `all:"irrationality measure" AND all:pi`, sorted newest,
   returned ten records. It included S1 and later unrefereed `math.GM` claims;
   no later item was retained because neither candidate needs an improvement
   beyond the peer-reviewed S1 threshold, and no unreviewed claim is used.
3. arXiv API queries `all:"digit changes" AND all:irrationality` and
   `all:"repetition complexity" AND all:irrationality` each returned zero
   records.
4. A Crossref title query for `irrationality measure of pi` returned the
   Salikhov and historical records plus unrelated results; it exposed no later
   peer-reviewed threshold used here.
5. OpenAlex and Semantic Scholar endpoints returned HTTP 429. These are
   recorded retrieval limitations, not silently omitted evidence.

The bounded search therefore does not identify an un-audited arithmetic
input. More importantly, a better irrationality exponent would only improve
the constants in DC and REP; it would not remove their T36 duplication or
collision status.

## 8. Explicit prior-item deduplication

| Item | Verification level used here | Deduplication decision |
|---|---|---|
| T5 | `literature-checked` bounded audit | Direct discrepancy, pair correlation, BBP, metric lacunary, and ordinary irrationality applicability are not repeated. |
| T15 | `literature-checked` bounded audit | Large-spectrum, almost-period, and additive-energy inverse routes are not repeated. |
| T36 | `machine-checked` named declarations | Its periodic-window theorem is imported as existing infrastructure. DC is explicitly rejected as its period-one corollary. |
| T45 | `proof sketch` | No claim from the note is a premise. Its primary S2/S3 sources were inspected independently; the note's Fejer argument is unused. |
| T60 | `proof sketch` with named checked imports and pinned sources | No Vaaler-grid or structured-incidence claim is promoted; ordinary irrationality-to-cancellation is not reopened. |
| T67 | `proof sketch` with named checked imports | No component aggregation premise is assumed; digit changes do not claim its missing cluster-multiplicity estimate. |
| T79 | `literature-checked` bounded audit | The family `10^j(10^r-1)` is not re-audited. REP's periodic completions and DC's `r=1` denominator are reasons for rejection, not a renewed lane. |
| T87 | `proof sketch` with named checked declarations | Start truncation and distinct late-frequency covariance are not revisited. |
| T88 | `machine-checked` conditional chain | None of its effective-irrationality, covariance, or long-sector premises is asserted here; no C7/C2/C1 conclusion is imported. |
| T98 | `experiment` plus construction-level obstruction | The Champernowne lane is not reopened and no normal-constant analogy is used. |

## 9. Why neither retained target qualifies

DC is a real unconditional fixed-pi theorem and is quantitatively stronger
than merely knowing that a constant tail cannot persist. It nevertheless
fails the agenda for two independent reasons: it is exactly T36 at period one,
and it is incomparable with ENT rather than a new language-complexity rung.

REP is also an unconditional fixed-pi theorem at the displayed threshold, but
its definition is a first repeated-factor collision and its source proof uses
periodic completion. It is expressly outside the permitted target class and
overlaps the T36/T79 mechanism. Lemma 2.2 of Source S2 gives only

```text
p_pi(n) >= r_pi(n)-n.
```

Even (4.3) therefore yields only the coefficient `125/763` by this inequality,
which is weaker than LL's coefficient one. REP cannot be presented as an
improved factor-complexity bound.

## 10. Terminal form: negative map

**Negative map.** The bounded source-pinned audit retains exactly two credible
fixed-pi consequences of the known irrationality exponent. Logarithmically
many digit changes are already the period-one specialization of T36 and sit
inside T79's denominator family. The exponent-of-repetition bound
`rep(d(pi))>888/763` is literally a first-collision statistic obtained by
periodic completion, and its induced factor-complexity estimate is below the
Morse--Hedlund baseline. Both exact pi thresholds are already met by the
2020 Zeilberger--Zudilin source, so improved constants do not open a new lane.
No retained target is simultaneously nonduplicative, above NR/LL, and outside
entropy/collision reformulations. The program is parked pending the required
three-program synthesis; no follow-up is scheduled.
