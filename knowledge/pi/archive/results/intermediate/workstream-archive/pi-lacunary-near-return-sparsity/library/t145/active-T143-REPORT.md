# T143: weighted residual quotients for finite carry transducers

Status: `proof sketch`. The finite replay is an `experiment`; it checks the
implementation and the two displayed applications but is not the proof of the
universal theorem. The proof below is independent of the unverified T141 note,
which is motivation and comparison memory only. This is an A13/A14
related-model note. It makes no fixed-pi, A1, C1, or C2 claim.

```text
RAW_STATE_CAP_PER_APPLICATION: 10000
APPLICATION_COUNT: 2
SCOPED_VERDICT_COUNT: 1
```

## 1. Canonical scope and normalization

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical problem fixes pi, base 10, strict circle distance, ordered pairs
including the diagonal, and the quantifiers

```text
for every A >= 1 there exists n0 >= 1 such that
for every n >= n0 there exists N >= 1 with A*n*Q_pi(n,N) <= N^2.
```

Nothing below supplies those quantifiers. The object here is instead a finite
deterministic weighted transducer. Fix a nonempty finite alphabet `D`, a finite
nonempty state set `Q`, a total transition map

```text
delta : Q x D -> Q,
```

integer edge weights `a(q,d)`, integer terminal weights `tau(q)`, and an
initial state `q0`. For a word `x=d_1...d_L`, let `q_i` be the state after its
first `i` letters and define

```text
F_q(x) = sum_(i=1)^L a(q_(i-1),d_i) + tau(q_L).            (1.1)
```

The empty word has total `F_q(empty)=tau(q)`. Applications read base-`p`
digits least-significant first, including declared high-zero padding.

Ambiguities fixed here are:

1. The machine is deterministic and complete; parallel edges can occur only
   through different letters.
2. The quotient is formed after restricting to states accessible from `q0`.
3. A cycle means a nonempty directed closed walk. Simple cycles are used to
   attain extremal means, but equality of the complete mean set is not claimed
   for simple cycles alone.
4. Cycle weight is the sum of edge weights; terminal weights are not charged
   on a cycle.
5. State equivalence is terminal-normalized. Thus totals from arbitrary
   members of one class can differ by a fixed terminal offset.
6. The raw-state cap counts the full Cartesian carry product before
   accessibility pruning or quotienting.

## 2. Weighted residual equivalence

Define the normalized edge and residual total by

```text
r(q,d) = a(q,d) + tau(delta(q,d)) - tau(q),                 (2.1)
R_q(x) = F_q(x) - tau(q).                                  (2.2)
```

The potential terms telescope, so

```text
R_q(d_1...d_L) = sum_(i=1)^L r(q_(i-1),d_i).               (2.3)
```

**Definition (weighted residual equivalence).** Put `q ~ q'` exactly when

```text
R_q(x)=R_q'(x) for every finite word x.                    (2.4)
```

This includes the empty word, where both residuals are zero. It deliberately
does not require `tau(q)=tau(q')`.

## 3. Terminating partition refinement

Start with the indiscrete partition `P_0={Q}`. Given `P_k`, split each existing
block by the complete signature

```text
Sig_k(q) = ((r(q,d), [delta(q,d)]_(P_k)))_(d in D).         (3.1)
```

Here the alphabet order is fixed once and for all. Stop when no block splits.

**Termination.** Every nonterminal round is a strict refinement and therefore
increases the block count. The count begins at one and is at most `|Q|`, so
there are at most `|Q|-1` strict rounds. This is a terminating finite
algorithm using only integer comparisons and block identifiers.

**Correctness.** The stable partition is exactly (2.4).

First, residual-equivalent states are never split. If `q~q'`, then one-letter
words give `r(q,d)=r(q',d)`. For every continuation `x`,

```text
R_q(dx)=r(q,d)+R_(delta(q,d))(x).                          (3.2)
```

Equality of both sides and of the first terms shows
`delta(q,d) ~ delta(q',d)`. Induction over refinement rounds now keeps `q,q'`
in one block.

Conversely, let `P_*` be stable and suppose `q,q'` share a block. Their stable
signatures give equal first residual edges and successors in a common block.
Induction on word length in (3.2) gives `R_q(x)=R_q'(x)` for every word. Thus
the final blocks are precisely the weighted residual classes.

## 4. Quotient and exact finite-word preservation

For every final block `B`, choose a representative `s(B)`, choosing
`s(B_0)=q0` for the initial block. Define

```text
bar_tau(B) = tau(s(B)),
bar_delta(B,d) = [delta(q,d)] for any q in B,
bar_r(B,d) = r(q,d) for any q in B,                         (4.1)
bar_a(B,d) = bar_r(B,d)+bar_tau(B)-bar_tau(bar_delta(B,d)). (4.2)
```

Stability makes the middle two definitions independent of `q`. Applying the
same telescoping identity in the quotient and using (2.4) gives, for every
`q in B` and every word `x`,

```text
bar_F_B(x)-bar_tau(B) = F_q(x)-tau(q),
bar_F_B(x) = F_q(x)+bar_tau(B)-tau(q).                     (4.3)
```

In particular the representative has no offset:

```text
bar_F_B(x)=F_(s(B))(x).                                    (4.4)
```

Since `s(B_0)=q0`, every finite-word total from the designated initial state
is preserved exactly. Therefore for every `L>=0` the quotient preserves the
entire multiset indexed by words, and in particular

```text
max_(|x|=L) F_q0(x),   min_(|x|=L) F_q0(x).                (4.5)
```

The terminal correction cannot be omitted. Take two states `u,v`, one letter
fixing both states, zero edge weights, and terminal weights `tau(u)=0`,
`tau(v)=5`. Their normalized residuals agree for every word, but their
unshifted totals are respectively 0 and 5. Formula (4.3), not unqualified
all-state equality, is the exact preservation statement.

## 5. Accessible cycle means

Let a closed walk have edge weight `W` and positive length `L`; its mean is
`W/L`. All states under discussion are accessible from `q0`.

**Raw to quotient.** A raw closed walk projects to a quotient closed walk of
the same length. On a closed walk, both raw and quotient terminal potentials
telescope, so both edge sums equal the sum of the normalized edges `r`.
Hence its mean is unchanged.

**Quotient to raw.** Let a quotient closed walk at block `B` have label word
`v`, length `L`, and normalized weight `C`. The word induces a self-map

```text
f : B -> B,   f(q)=delta(q,v).                             (5.1)
```

Every traversal of `v` from a member of `B` has normalized weight `C`. Choose
an accessible `q in B`. Finiteness gives `i<j` with `f^i(q)=f^j(q)`. Starting
at the accessible state `f^i(q)`, the word `v^(j-i)` is a raw closed walk.
Its length is `(j-i)L`; its edge weight is `(j-i)C`, because the residual
weights add and the raw terminal potential telescopes at the common endpoint.
Its mean is therefore `C/L`.

Thus the numerical sets of accessible nonempty closed-walk means are equal.
This does not give a length-preserving bijection: if one letter swaps two
equivalent states, the quotient has a one-edge loop while the raw lift may
first close after two letters. Taking a power is essential.

Every closed walk decomposes into simple directed cycles, and its mean is a
length-weighted average of their means. Consequently the maximum `mu_+` and
minimum `mu_-` accessible closed-walk means are attained by simple cycles and
are preserved by the quotient.

## 6. T141-style max/min asymptotics

Let `M_L` and `m_L` denote the maximum and minimum in (4.5). Delete closed
subwalks successively from an arbitrary length-`L` path. The remaining simple
path has fewer than `|Q|` edges. Every deleted closed walk has mean at most
`mu_+` and at least `mu_-`. Since there are finitely many simple paths and
terminal weights,

```text
M_L <= mu_+ L + O(1),    m_L >= mu_- L - O(1).             (6.1)
```

For the reverse inequalities, take an accessible cycle attaining the desired
mean, follow one fixed access path, repeat the cycle as often as possible, and
use the first fewer-than-one-cycle edges to fill the exact requested length.
The access path, partial cycle, and terminal weight range over finite sets, so

```text
M_L >= mu_+ L - O(1),    m_L <= mu_- L + O(1).             (6.2)
```

After enlarging constants for finitely many short lengths,

```text
M_L=mu_+ L+O(1),         m_L=mu_- L+O(1).                  (6.3)
```

Equations (4.5) and Section 5 show that the quotient preserves both the exact
finite envelopes and these slopes. No claim from the T141 note is needed.

## 7. Factorial-ratio carry construction

For a prime `p`, nonempty lists of positive multipliers
`a=(a_1,...,a_r)` and `b=(b_1,...,b_s)`, define

```text
R(n)=prod_i (a_i n)! / prod_j (b_j n)!,
Delta=sum_i a_i-sum_j b_j,
D_p(n)=(p-1)v_p(R(n))-Delta*n.                             (7.1)
```

Legendre's identity gives

```text
D_p(n)=sum_j s_p(b_j n)-sum_i s_p(a_i n).                 (7.2)
```

For multiplier `c`, the carry set is `{0,...,c-1}`. On input digit `d`,

```text
kappa'_c=floor((c*d+kappa_c)/p),
e_c=c*d+kappa_c-p*kappa'_c.                               (7.3)
```

The full raw state space is the Cartesian product of all carry sets. The edge
weight is `sum_j e_(b_j)-sum_i e_(a_i)`, and the terminal weight is the same
signed sum of base-`p` digit sums of the final carries. Digit telescoping then
proves that the finite-word total equals (7.2). Both applications below are
constructed from (7.3), not copied from a prior quotient table.

## 8. Application 1: central trinomial ratio

Take

```text
R_1(n)=(3n)!/(n!)^3,   p=2.                               (8.1)
```

The full carry product has `3*1*1*1=3` states, below the cap 10000; all three
are accessible. Partition refinement leaves three singleton residual classes.
Thus this application is an exact irreducibility check: quotienting does not
compress every small carry machine.

Writing only the multiplier-3 carry, the independently generated table is

| state | digit 0 | digit 1 | terminal |
|---|---|---|---:|
| 0 | `0 / 0` | `1 / 2` | 0 |
| 1 | `0 / -1` | `2 / 3` | -1 |
| 2 | `1 / 0` | `2 / 2` | -1 |

Entries are `next / raw edge weight`. The replay checks all residual
signatures, representative totals, the exact max/min dynamic programs through
length 64, and

```text
transducer(n)=v_2((3n)!)-3v_2(n!)                          (8.2)
```

for every `0<=n<100000`. Its accessible extremal cycle means are 0 and 2.
These are finite `experiment` checks; Sections 2--6 are the universal proof.

## 9. Application 2: hypergeometric factorial ratio

Take the independent factorial ratio

```text
R_2(n)=(6n)! n! / ((3n)!(2n)!),   p=5.                    (9.1)
```

The raw carry order is `(kappa_6,kappa_1,kappa_3,kappa_2)`. Its full product
has `6*1*3*2=36` states, below the cap 10000. Exactly six are accessible.
Running the refinement algorithm, rather than prescribing classes, gives

```text
B0={(0,0,0,0)},
B1={(1,0,0,0),(2,0,1,0),(3,0,1,1),(4,0,2,1)},
B2={(5,0,2,1)}.                                           (9.2)
```

Hence the accessible machine compresses from six states to three. With
representatives chosen lexicographically, the generated quotient is

| block | digit 0 | digit 1 | digit 2 | digit 3 | digit 4 | terminal |
|---|---|---|---|---|---|---:|
| B0 | `B0 / 0` | `B1 / 3` | `B1 / 1` | `B1 / -1` | `B1 / -3` | 0 |
| B1 | `B0 / -1` | `B1 / 2` | `B1 / 0` | `B1 / -2` | `B2 / 1` | -1 |
| B2 | `B1 / 3` | `B1 / 1` | `B1 / -1` | `B1 / -3` | `B2 / 0` | 2 |

The table uses quotient edge weights (4.2), not normalized edges. Different
representatives would change terminal potentials and edge weights but not any
representative total, residual class, cycle mean, or initial-state output.

Here `Delta=2`, so the replay checks

```text
transducer(n)=4*(v_5((6n)!)+v_5(n!)-v_5((3n)!)-v_5((2n)!))-2n             (9.3)
```

for every `0<=n<100000`. It also exhausts all words through length 8 from all
six raw states, verifies the terminal-offset formula (4.3), compares raw and
quotient extrema through length 64, and checks that both accessible extremal
cycle means are -2 and 2. This is an `experiment`, not a finite proof of the
universal theorem.

## 10. Prior-fingerprint comparison

No prior note is used as a discharged premise. Hashes identify the exact
comparison copies inspected.

| Item | Level and inspected fingerprint | T143 separator |
|---|---|---|
| T94 | unverified `proof sketch`, SHA `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10`; paperfolding symbol tensor, subset determinization, and factor-collision profile recurrence | T143 minimizes terminal-weighted scalar residual functions of multiplication-carry states. It has no factor starts, pair tensor, subset state, or collision multiplicity. |
| T112 | source statements self-labeled `literature-checked`, deductions `proof sketch`, SHA `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa`; random-input carry local limits and twisted finite operators | T143 is deterministic exact quotienting for every input word. It proves no random-input law, spectral gap, local limit, or Fourier cancellation. |
| T119 | recovered incomplete report used as unverified comparison memory, SHA `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a`; collision concentration versus predictive, ordinary Hankel, and moment rank | T143's equivalence is equality of all future weighted residuals, not low matrix rank inferred from one collision statistic. It makes no rank inversion. |
| T133 | unverified `proof sketch` with source components self-labeled `literature-checked`, SHA `53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40`; one hand-derived three-class base-5 valuation transducer and arithmetic orbit audit | T143 independently rebuilds that raw carry model only as one test, then supplies the general terminating equivalence algorithm and preservation theorem. It imports no T133 arithmetic conclusion. |
| T141 | unverified `proof sketch`, SHA `e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356`; factorial-ratio carry totals, tropical extrema, and accessible-cycle asymptotics | T143 treats it only as motivation, reproves the graph facts, corrects the terminal-offset issue, and adds canonical residual quotienting with cycle lifting. |
| active T140 | unavailable in the supplied snapshot: no readable report, result, source pin, or agenda fingerprint was found | Availability boundary only. No T140 content, premise, or novelty assertion is inferred. |
| active T142 | unavailable in the supplied snapshot: no readable report, result, source pin, or agenda fingerprint was found | Availability boundary only. No T142 content, premise, or novelty assertion is inferred. |

The duplication boundary is explicit: Application 1 reconstructs the same
central-trinomial model displayed in T141, and Application 2 reconstructs the
same six raw carry states underlying T133. Those models are validation targets,
not claimed as new. T143's scoped new proof-sketch content is the general
terminal-normalized equivalence, terminating refinement, exact quotient
reweighting, and closed-walk lifting theorem.

## 11. Separate unproved transfer hypothesis

Transfer toward the machine-checked T7 finite-cylinder interface or the
machine-checked T107 triangular Fejer interface would require an additional
pi-specific construction not supplied here:

**PI-DECIMAL-COEFFICIENT-T143 (`conjecture`, unproved).** There exists an exact
decimal-compatible coefficient transducer attached to a proved representation
of pi, together with a residual quotient for which equivalence preserves not
only a scalar valuation output but all data needed to recover, after complete
reduction:

1. the coefficient numerator and every cancellation affecting it;
2. the complete reduced modulus, including its powers of 2 and 5;
3. the multiplicative order of 10 modulo the coprime tail modulus and the
   decimal transient;
4. ordered, diagonal-inclusive orbit occupancy at the metric or cylinder scales
   required by T7, or both the boundary and Fourier budgets required by T107.

The transducer would also need a proved truncation-error map from its rational
coefficients to `(10^i-10^j)pi` uniformly over the prescribed prefix. Scalar
weighted residual equivalence alone preserves none of numerator, modulus,
multiplicative order, occupancy, or approximation error. Neither application
is a representation of pi. This hypothesis is not asserted to exist or to be
plausible, and no fixed-pi, A1, C1, or C2 conclusion follows.

## 12. Self-contained replay

In a directory containing only the delivered files, run

```bash
python3 verify_t143.py
sha256sum -c SHA256SUMS
```

The verifier hash-checks the canonical statement, enforces both raw-state caps,
generates raw carry graphs, runs refinement to stability, checks every stable
signature, checks representative and terminal-offset totals on bounded word
sets, validates cycle-mean extrema and exact finite-length max/min preservation,
and compares transducer totals with Legendre-floor arithmetic. `raw_output.txt`
is the captured output. All bounded checks are labeled `experiment`; the
universal proof is Sections 2--6.

hold as model
