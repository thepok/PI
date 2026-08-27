# T24: effective irrationality measures versus T23

Status: `literature-checked` on 2026-07-23 for exactly the five-source,
six-row corpus frozen in `CORPUS.json`. This is a bounded applicability audit,
not a proof or disproof of C1.

## 1. Immutable target and exact T23 quantifiers

The canonical statement is
`knowledge/pi/statements/pi-positive-lower-block-density.txt`, SHA-256
`11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`.
It asks whether every nonempty decimal word, including leading-zero words,
has strictly positive lower asymptotic frequency in the fixed nonterminating
decimal expansion of pi. First occurrence, positive upper density, normality,
other bases, and almost-everywhere statements are not substituted for it.

Accepted T23 is pinned inside `EVIDENCE.tar` at
`evidence/knowledge_library/t23/T23FiniteCylinderEnergyCriterion.lean`, SHA-256
`8e8f560806f13a8e56bd4432aef2b689309837c8a1adb2bab72cf7c9349e6aa6`.
Its hypothesis is literally

```text
for every real s with 0 < s < 1,
  there exist C >= 1 and N0 in Nat such that
  for every N >= N0 and every m >= 1,
    E_pi(m,N) <= C*(10^(-s*m) + 1/N).                 (T23)
```

`C,N0` may depend on `s`, but not on `N,m`. T23 machine-checks only
`(T23) -> C1`; it does not establish `(T23)` for pi.

### Quantifier ambiguities fixed

1. `m` is the positive decimal-cylinder length. `N` is the number of starts.
2. In the lag formula, `r` is positive and `n` is the lower start:
   `1<=r<N` and `0<=n<N-r`. This `n` is not the cylinder length.
3. An eventual rational-approximation theorem may have a denominator onset;
   it does not thereby become a numerical all-denominator estimate.
4. Excluding one pair, or all pairs in a scale region, is not an aggregate
   energy estimate in the complementary region.
5. T23's `s` is an energy-decay parameter, not a rational-approximation
   exponent. No identification between those unrelated parameters is made.

## 2. Exact accepted collision interface

T23 lines 467-475 identify its real-valued `E_pi` with T7's normalized
collision energy. Accepted T7 then gives, for `N>=1`,

```text
E_pi(m,N) <= Q_pi(m,N)/N^2 <= 3*E_pi(m,N).            (1)
```

The factor `3` is real: a circle near return may be in the same decimal
cylinder or either cyclically adjacent cylinder. Equality must not be claimed.

Accepted lag decomposition gives, for `m,N>=1`,

```text
Q_pi(m,N)
 = N + 2*sum_(r=1)^(N-1)
       #{0 <= n < N-r :
         ||10^n*(10^r-1)*pi|| < 10^(-m)}.             (2)
```

The `N` term is the diagonal. Equations (1)-(2), their theorem locators, and
their hashes are recorded in `CORPUS.json` and `LOCKED_EVIDENCE.md`; exact
source copies are retained in `EVIDENCE.tar` under
`evidence/TheoryLib/PiLacunaryNearReturnSparsity/`.

## 3. Algebraic translation checked once

Put

```text
Q = 10^n*(10^r-1),   n>=0, r>=1.
```

Then `Q>=9`. Let `P` be a nearest integer to `Q*pi`; it is positive. A source
bound

```text
|pi-p/q| >= q^(-mu)
```

at denominator `Q` gives

```text
||Q*pi|| = |Q*pi-P|
          = Q*|pi-P/Q|
         >= Q^(1-mu)
          = 10^(-(mu-1)*n)*(10^r-1)^(-(mu-1)).        (3)
```

Write `a=mu-1`. The strict near return in (2) is impossible whenever

```text
m >= a*(n + log10(10^r-1)).                            (4)
```

The simpler condition `m>=a*(n+r)` is sufficient because
`log10(10^r-1)<r`.

If (3) holds for every `Q>=9`, define

```text
L = min(N-1, floor(m/a)).
```

Every unordered pair whose upper index is `n+r<=L` is excluded. There are
`1+2+...+L=L*(L+1)/2` such pairs, so (2) gives

```text
Q_pi(m,N) <= N^2-L*(L+1),
E_pi(m,N) <= 1-L*(L+1)/N^2.                            (5)
```

When `m>=a*(N-1)`, `L=N-1`, hence only diagonal near-return pairs remain.
T7's diagonal lower bound for the collision energy, together with
`E_pi<=Q_pi/N^2`, gives both inequalities needed for

```text
Q_pi(m,N)=N,  E_pi(m,N)=1/N.                           (6)
```

This is useful unconditional collision-free information, but it is in the
very fine region `m` linear in `N`. If `m=o(N)`, (5) tends to `1`; for example
`m=floor(sqrt(N))` leaves order `N^2` pairs unresolved. T23's right side tends
to zero along that example for every fixed `0<s<1` and fixed `C`. Thus the
direct irrationality-measure bound has a quantified scale mismatch, not a
minor loss of constants.

## 4. Frozen source pins

| ID | Primary source | PDF SHA-256 | Exact locator |
|---|---|---|---|
| MAH1953 | Mahler, *On the Approximation of pi* | `de3831e81b20706a1b241a01e36306e9676f233372d6197ee3eb038ed54f2db5` | Theorem 1, reprint p. 561 / original p. 33 |
| MIG1974 | Mignotte, *Approximations rationnelles de pi...* | `55411f22110bae877483c5e8a8e0cda033874a7ff86cca5b8ae07178ca179eed` | Theoreme 1, printed p. 125, both clauses |
| HATA1993 | Hata, *Rational approximations to pi...* | `c3294d1987dfd013ec4d13f93737233177817d50c9c102ea95033e986cd9e3df` | Theorem 1.1 and corollary, printed p. 336 |
| SAL2008 | Salikhov, *On the irrationality measure of pi* | `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d` | Theorem 1, p. 570; final calculation, p. 571 |
| ZZ2020 | Zeilberger--Zudilin, *The irrationality measure of pi...* | `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5` | definition p. 407; Propositions 7-8 and final calculation pp. 417-418 |

DOIs, URLs, byte counts, extraction hashes, and exact extraction line ranges
are in `CORPUS.json`. Mignotte's p. 125 formulas were checked visually because
the scan's extracted superscripts are garbled. The retained PDF is
authoritative.

## 5. Row-by-row applicability

The normative details are in `CORPUS.json`.

| Row | Exact rational bound | Substituted norm bound | Controlled `(n,r,m,N)` region | Unresolved region | T23 |
|---|---|---|---|---|---|
| MAH-42 | `|pi-p/q|>q^-42`, all positive `p,q>=2` | `||Q*pi||>Q^-41` | pair excluded at `m>=41 log10 Q`; whole prefix collision-free at `m>=41(N-1)` | all smaller `m`, especially `m=o(N)` | **PARTIAL** |
| MIG-20.6 | `|pi-p/q|>q^-20.6`, all positive rationals, `q>=2` | `||Q*pi||>Q^-19.6` | pair excluded at `m>=19.6 log10 Q`; whole prefix collision-free at `m>=19.6(N-1)` | all smaller `m`; (5) tends to 1 for `m=o(N)` | **PARTIAL** |
| MIG-20 | `|pi-p/q|>q^-20`, `q>=exp(e^110)` | `||Q*pi||>Q^-19` | with the global companion clause, whole prefix collision-free at `m>=max(19(N-1),19.6 e^110/log(10))` | all scales below this explicit linear frontier | **PARTIAL** |
| HATA-8.0161 | `|pi-p/q|>=q^-8.0161`, `q>=q0` | `||Q*pi||>=Q^-7.0161` | `Q>=q0` and `m>=7.0161 log10 Q` | numerical `q0` absent; complementary scales unresolved | **PARTIAL** |
| SAL-7.60630853 | for fixed `nu=7.60630853`, `|pi-p/q|>=q^-nu`, `q>=q0(nu)` | `||Q*pi||>=Q^-6.60630853` | `Q>=q0` and `m>=6.60630853 log10 Q` | numerical onset absent; `m=o(N)` unresolved | **PARTIAL** |
| ZZ-7.104 | source proves `mu(pi)<=7.103205...`; fix `7.104` and sufficiently large `q` | `||Q*pi||>Q^-6.104` | `Q>=Q0(7.104)` and `m>=6.104 log10 Q` | numerical onset absent; order `N^2` pairs unresolved for `m=o(N)` | **PARTIAL** |

For Mignotte, reducing `P/Q` cannot weaken the bound: the reduced denominator
`q'<=Q` gives `q'^(-mu)>=Q^(-mu)`. No coprimality assumption blocks the
substitution.

For Hata, Salikhov, and Zeilberger--Zudilin, the eventual threshold is enough
for a qualitative mathematical finite patch because pi is irrational, but the
sources do not print the finite minimum. This audit therefore records the
direct replayable region `Q>=q0` rather than inventing a numerical onset.

There is no `FULL` row. There is no `NONE` row because every retained theorem
does give a genuine unconditional fixed-pi separation region. `PARTIAL` means
only that region; it is not positive evidence for the unresolved energy bound.

## 6. Exact failure against every T23 quantifier

The best retained exponent changes the boundary from `41N` to approximately
`6.104N`. It does not change the direction of the boundary. T23 must hold:

- for every `0<s<1`, with no rational-approximation row supplying the energy
  estimate for any such `s` in the unresolved region;
- with `C,N0` chosen before `N,m`;
- for every `N>=N0`, not selected prefixes;
- for every `m>=1`, not only `m>=aN+O(1)`.

At `m=floor(sqrt(N))`, every retained irrationality theorem directly excludes
only an initial triangle of `O(m^2)=O(N)` off-diagonal pairs. It leaves
`N^2-O(N)` candidate ordered pairs. The resulting bound from (5) is
`1-O(1/N)`, while

```text
C*(10^(-s*floor(sqrt(N)))+1/N) -> 0.
```

This comparison does not prove that the remaining pairs are collisions. It
proves that irrationality-measure separation alone does not deliver T23's
required upper bound there. A new aggregate sparsity, discrepancy,
pair-correlation, or cancellation input at fixed pi would be needed.

## 7. Locked T5 evidence and conclusion

`LOCKED_EVIDENCE.md` imports T5 and its accepted source pins by hash. The
complete hash-identical T5 package and every content-addressed object named by
its locked-evidence file are retained inside `EVIDENCE.tar`; T24 does not
rerun or rewrite those audits. The new contribution is the exact substitution
into (2), the triangular count (5), and the literal comparison with T23.

Within this five-source, six-row corpus, effective rational approximation
gives an unconditional pi-specific collision-free region and a precise future
formalization target. It does not establish any all-`m` cylinder-energy decay.

**Partial scale control neither proves nor supports C1.** C1 remains open.
No unconditional C1 claim is made anywhere in this package.

## 8. Replay

From this directory run:

```sh
./reproduce.sh verify
```

The command first checks the delivered manifest and archive, extracts the
archive to a temporary directory, and then checks every bundled path without
reading the surrounding record or workspace. It regenerates all five text
extractions, verifies the immutable statement and accepted bridge hashes,
checks the imported T5 package and all content-addressed evidence named by T5
or T24, and validates corpus caps, populated locator fields, algebraic
exponents, verdicts, and C1 labels. The retained PDFs remain authoritative for
checking locators.
