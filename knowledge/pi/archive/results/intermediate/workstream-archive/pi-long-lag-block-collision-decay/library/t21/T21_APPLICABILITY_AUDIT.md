# T21 source-pinned applicability audit

Audit date: 2026-08-01 UTC

Claim label: `literature-checked` applies only to the retained source
statements, locators, and applicability comparisons below. No estimate for the
decimal orbit of `pi` is proved here. This audit makes no C1 verdict.

## 1. Scope and immutable statement

The byte-exact canonical statement is `CANONICAL_STATEMENT.txt`, SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

Its lines 1-10 define the canonical ordered long-lag collision question and
its `forall s, exists C_s, forall m,N` order. T21 does not attempt to answer
that question. The candidate audited here is the distinct conditional
spectral premise restored in the kernel-gated T12 module.

T11 is used only as motivation. The T11 note is a `proof sketch`, not a
machine-checked premise, and no T21 conclusion depends on a claim unique to
that note.

## 2. Exact comparator

### 2.1 T8 ordered domain

The retained source `T8_SPECTRAL_SOURCE.lean` has SHA-256

```text
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9
```

Exact locators are lines 37-42 for `decimalFrequency m = 10^m`, lines 44-68
for the oriented `(lag,start)` representation and domain, lines 71-94 for the
membership theorem, lines 96-123 for the fixed-`pi` phase and spectral sum,
and lines 154-159 for the inclusive positive-frequency range.

Fix real `mu,c` and natural `Q0` before every variable below. A domain element
is

```text
q = (orientation, (r,n))
```

and T8's machine-checked membership theorem says exactly

```text
0 < r,
m <= r,
r < N,
n < N-r,
not ArithmeticExcluded(mu,c,Q0,m,n,r).
```

Both Boolean orientations are retained. They represent `(n,n+r)` and
`(n+r,n)`, so the domain is ordered. There is no diagonal, and the weak lag
cutoff is exactly `r >= m`. The domain is restricted by
`ArithmeticExcluded`; it is not the unrestricted set of all long pairs.

For `q` in this domain, set `(a,b)` to its represented ordered coordinates.
T8 defines

```text
S_h(mu,c,Q0,m,N)
  = sum_q exp(2*pi*i*h*((10^a-10^b)*pi)).
```

The first `pi` in the exponential convention is the circle constant; the
second is the prescribed orbit point. T21 never replaces the orbit point by
`pi` in a metric theorem. When a variable `alpha` is used below to explain a
source comparison, it denotes a sibling polynomial obtained by replacing
only the second `pi` by `alpha`.

### 2.2 T12 candidate and quantifiers

The retained source `T12_SCALE_MATCHED_SOURCE.lean` has SHA-256

```text
a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf
```

Exact locators are lines 29-41 for `scaleMatchedTarget` and
`ScaleMatchedL1Bound`, lines 53-62 for the quantifier audit, lines 151-161 for
the pointwise residual implication, and lines 230-244 for the fully
quantified residual conclusion with constants.

For fixed `(mu,c,Q0)`, T12's exact candidate is

```text
for every real s with 0 < s < 1,
  there exists a real B_s >= 0, chosen here,
  such that for every positive integer m and N,
    sum_{1 <= h <= 10^m} |S_h(mu,c,Q0,m,N)|
      <= B_s * 10^m * (N + N^2 * 10^(-s*m)).
```

Thus the order is literally

```text
fixed (mu,c,Q0); forall s; exists B_s; forall positive m,N.
```

The frequency endpoints are inclusive. There is no maximum over `N` in the
candidate. A maximal theorem is therefore stronger in that coordinate, but
still useful only if all its other dependencies match.

No ambiguity is silently repaired:

- `B_s` may depend on `s`, but not on `m` or `N`.
- The phase is the fixed real `pi`, not an almost-everywhere phase.
- The T8 arithmetic restriction remains present.
- `mu,c,Q0` are parameters fixed outside the displayed quantifiers; T21 does
  not assert that any arithmetic premise about them holds.
- The candidate is a conditional interface, not a metric sibling and not a
  conclusion about decimal collisions.

T12's established conditional arithmetic is quoted without strengthening it:
at one positive scale, an L1 bound with constant `B` gives the residual count
constant `pi^2*(1+B)` (lines 151-161), and the quantified version retains the
same witness order (lines 230-244). T21 does not assert the L1 premise.

## 3. T5 non-duplication boundary

The unchanged T5 matrix is referenced, not copied:

```text
knowledge_library/t5/APPLICABILITY_MATRIX.md
SHA-256 ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406
```

Its rows M1-M7 already audit Bailey--Crandall, Philipp, Fukuyama,
Rudnick--Zaharescu, Chernov--Kleinbock, and Rousseau against the older T2
residual frontier. None of those rows or PDFs is duplicated here. T21 asks a
new question about T12's growing-frequency L1 candidate, so the matrix below
contains only newly retained theorem families.

## 4. Applicability convention

- `APPLIES`: the cited theorem supplies the exact fixed-`pi` candidate with
  all hypotheses discharged.
- `CONDITIONAL`: after one named additional premise, the cited theorem gives
  the exact candidate, and the resulting `B_s` dependence is explicit.
- `DOES NOT APPLY`: a point, frequency, scale, maximality, exceptional-set,
  model, or constant mismatch remains even after legal substitutions.

Every verdict is about the theorem as stated in its pinned source. Norm or
almost-everywhere conclusions are never evaluated at `pi`.

## 5. Applicability matrix

| ID | Retained theorem | Verdict | Point and exceptional set | Frequency and scale | Maximal in `N` | Constants | Exact obstruction |
|---|---|---|---|---|---|---|---|
| V1 | Demeter--Silva, Theorem 7.1, vector-valued Carleson | **DOES NOT APPLY** | `L^p(R)` norm in the phase variable. The norm inequality has no exceptional set, but its pointwise consequence is only a.e.; evaluation at `pi` is not a bounded functional on `L^p`. | The channel index can be the exact finite range `1 <= h <= 10^m`, but the source is on `R` and does not provide the periodic transference or T8 coefficient encoding. | The operator is maximal in a Fourier cutoff. Exact identification of that cutoff with T8's `N`-filtration is not a theorem in the retained source. | Implicit constant depends on `p`, not on the number of channels. Converting `ell^2_h` to the requested `ell^1_h` costs exactly `(10^m)^(1/2)`. | No fixed-point value at `alpha=pi`; periodic transference and exact T8 truncation are also unstated. |
| V2 | Aistleitner--Berkes--Seip, Lemma 4 and (30), maximal dilated-function inequality | **DOES NOT APPLY** | Integral over `x in [0,1]`; later pointwise consequences are a.e. with data-dependent exceptional sets. No specialization to `x=pi` is licensed. | Allows every strictly increasing integer dilation sequence. For fixed `h`, positive numbers `h(10^a-10^b)` can be sorted and T8 survivors can be selected by coefficients, but the source has no simultaneous vector theorem over `h <= 10^m`. | Maximal over the first `M` of `K` sorted dilations, not literally over T8's orbit parameter `N`; a separate shell-alignment argument would be required. | `c` may depend on the fixed periodic function `f`, but not on `K`, the dilations, or coefficients; the loss is `(log log K)^4`. Combining all `h` requires an additional finite-family inequality and does not remove the point gap. | Metric integral only, plus no source-level simultaneous growing-frequency or exact T8-filtration conclusion. |
| D1 | Chang--Kerr--Shparlinski, Theorem 2.2, exponential large sieve for sparse powers | **DOES NOT APPLY** | Averages maxima over reduced residues `a mod p` and sums over primes `p <= X`; the point is a finite-field residue, not the prescribed real `pi`. | Treats sparse powers `lambda^(s_n) mod p` and is digital-adjacent (the paper applies it to prescribed binary digits). It does not treat real phases `h(10^a-10^b)pi`, the T8 pair-difference support, or `h <= 10^m`. | The maximum is over residues, not over orbit length `N`. | An absolute `rho>0` appears, with asymptotic `X^(o(1))`; the bound depends on `X,T,S` as displayed in Theorem 2.2. These are finite-field parameters, not one `B_s` before all `m,N`. | Wrong ambient model and averaging variables; no fixed-real or T8-domain implication. |
| D2 | Chang--Kerr--Shparlinski, Lemma 3.1, classical large sieve for an increasing sparse sequence | **DOES NOT APPLY** | Sum over every reduced residue modulo every `k <= K`; no estimate at one prescribed real point. | Arbitrary increasing integer sequence `s_n`, but the bound is `(K^2+S)T`, where `S=max s_n`. For decimal pair frequencies the ambient maximum grows exponentially with the largest orbit exponent. | No maximal partial-sum conclusion in `N`. | Absolute implied constant, with explicit dependence on modulus cutoff `K`, maximum frequency `S`, and number of terms `T`. | Averaging over moduli/residues and the ambient-frequency term `S` do not yield the scale `10^m(N+N^2*10^(-sm))`. |

No retained theorem is `APPLIES` or `CONDITIONAL`.

## 6. Source-by-source checks

### V1: vector-valued Carleson

Retained PDF: `demeter-silva-1311.4092v1.pdf`, SHA-256
`eaf4081ebc9796efa80ddb6c81349846263b9900b56a7e78d881f39117ad7348`.
The bibliographic and retrieval data are in `SOURCE_MANIFEST.md`.

Exact locators: physical/article PDF page 3, equation (7), defines the Carleson operator with
an arbitrary measurable cutoff; PDF page 15, Section 7, Theorem 7.1 states

```text
||(sum_j |C f_j|^2)^(1/2)||_p
  <= C_p ||(sum_j |f_j|^2)^(1/2)||_p,  1<p<infinity.
```

The theorem is genuinely vector-valued and its channel constant is
dimension-free. It is adjacent to the simultaneous `h` range, but the retained
source neither states periodic transference nor identifies its Fourier cutoff
with T8's restricted `N`-filtration. Even after separately supplying those
steps, it would remain an integrated norm statement. A null-set-free norm
inequality is not a pointwise theorem at every phase, so it provides no value
at `pi`.

### V2: maximal arbitrary dilations

Retained PDF: `aistleitner-berkes-seip-1210.0741v5.pdf`, SHA-256
`b89868f1563d382525608059b45a338feb4e18a52ac6470c99baf077e122375b`.

Exact locator: PDF/article page 17, Section 5, Lemma 4 and equation (30),
continuing onto page 18. Lines immediately after (30) state that `c` may
depend on `f` but not on `N` or anything else. For a mean-zero, one-periodic
`f` in `BV` or `Lip_(1/2)`, every increasing positive integer sequence `n_k`,
and real coefficients `c_k`, the source states

```text
integral_0^1 max_{1<=M<=N} |sum_{k<=M} c_k f(n_k x)|^2 dx
  <= c * (log log N)^4 * sum_{k<=N} c_k^2.
```

Pairing the two T8 orientations suggests a cosine encoding. For unrestricted
positive frequencies, a shell with largest endpoint `A` comes after every
older shell because

```text
10^A - 10^(A-m) > 10^(A-1) - 1.
```

Restriction preserves this order, but turning the source's first-`M`
dilation maximum into the exact T8 `N`-filtration still requires a separate
encoding, including zero coefficients and the distinction between the number
of dilations `K` and orbit length `N`. No such reduction is claimed here. In
any event the integration variable remains `x`: applying the theorem for each
`h` does not certify `x=pi`, and the source has no uniform `ell^1` conclusion
over the growing channel set.

### D1-D2: sparse exponential large sieve

Retained PDF: `chang-kerr-shparlinski-1706.04776v2.pdf`, SHA-256
`561ffe68b4a1730d7cbd460f83f815c88b06e55579880fd440934ffe2c42634d`.

Exact locators: PDF page 2 defines `V_lambda` as a sum over primes of maxima
over reduced residues; PDF pages 4-5, Theorems 2.1-2.2, give the sparse-power
large-sieve bounds; physical/article PDF page 6, Lemma 3.1, states the auxiliary classical
large sieve

```text
sum_{k<=K} sum^*_{c mod k} |sum_{n<=T} gamma_n e_k(c s_n)|^2
  << (K^2 + S) T,
```

where `S=max s_n`. Theorems 2.1-2.2 replace the phases by powers
`lambda^(s_n)` modulo primes. These results are digital-adjacent but not a
real fixed-point theorem. Their residue, prime, and ambient-support averages
cannot be rewritten as T8's value at `pi`.

## 7. Search coverage and retrieval blockers

The dated search covered the requested categories with queries for
`fixed-point lacunary maximal`, `vector-valued lacunary`, `digital large
sieve`, `large sieve lacunary`, and `growing frequency Carleson`. It also
checked the staged T9-T19 notes for existing leads.

The closest deterministic fixed-point/maximal source located was Hugh L.
Montgomery, *The analytic principle of the large sieve*, Bulletin AMS 84
(1978), Section 9. The official AMS PDF URL returned HTTP 403 in this sandbox;
the Project Euclid PDF route returned an HTML denial rather than a PDF. It is
therefore recorded as a retrieval blocker in `SOURCE_MANIFEST.md`, not retained
as a theorem row and not used for any claim. The accessible sources above are
sufficient to audit the vector-valued, maximal-dilation, sparse-sieve, and
digital-adjacent branches honestly.

No source with the literal phrase `digital large sieve` was found in the
arXiv title/abstract search. Chang--Kerr--Shparlinski is retained as the
closest primary sparse-exponential theorem with an explicit prescribed-digit
application, not mislabeled as a theorem about decimal real orbits.

## 8. Terminal gap

The metric/vector sources offer adjacent finite-channel and maximal-cutoff
mechanisms, but the retained theorems do not themselves supply every
transference and T8-filtration step. The finite-field sieve sources exploit
sparse powers in a different model. None controls evaluation at the
prescribed real `alpha=pi`.

The candidate itself has no maximal quantifier, so no maximal theorem is
required to state the terminal issue. The narrowest exact unmet input is the
following fixed-point estimate on T8's already restricted domain:

```text
for every real s with 0 < s < 1,
  there exists B_s >= 0, selected before all scales,
  such that for every positive integer m,N,
    sum_{h=1}^{10^m} |S_h(mu,c,Q0,m,N; alpha=pi)|
      <= B_s * 10^m * (N + N^2 * 10^(-s*m)).
```

This is a precisely stated terminal gap, not an asserted premise. An
almost-everywhere or `L^p(d alpha)` theorem cannot fill it unless an additional
source proves that this prescribed `pi` belongs to the relevant good set with
one constant uniform in all `m,N`. No retained source proves such membership.

The T12 residual constant `pi^2*(1+B_s)` remains conditional on this unmet
input. No metric theorem has been specialized to `pi`, and no C1 verdict is
asserted.

## 9. Replay

From the directory containing only these artifacts, run

```sh
sh verify_sources.sh
```

The script checks all retained source hashes and confirms the named physical
PDF pages and source-snapshot locators. When the sibling `knowledge_library`
directory is present, it also checks the two externally referenced T5 hashes;
it never copies T5 material into T21.
