# T147: a shared-prefix counterfamily to additive multiscale collision census

Date: 2026-08-12 UTC.

Claim label: `proof sketch`.  The universal argument below is an elementary,
constant-explicit construction, but this note has no kernel-checked
formalization.  The finite replay is an `experiment`: it checks exact counts,
endpoints, comparator hashes, and numerical instances, not the universal
argument.  No claim from the unverified T144 note is used as a premise.

```text
BASE: 10
KAPPA: 1/4
RHO: 1/2
FIRST_K: 8000
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
CONJECTURE_CLAIM: none
```

## 1. Provenance, normalized scope, and ambiguities

The canonical statement has no external Erdos Problems URL.  Its recorded
provenance says that this program formulated it on 2026-07-22.  The byte-exact
`canonical_statement.txt` delivered here has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical A1 question concerns ordered, diagonal-inclusive *metric* near
returns of the fixed decimal orbit of pi, with `N` allowed to depend on `A` and
the depth.  T147 neither changes nor answers it.  T147 treats a finite-word
equal-block sibling under recorded ambiguities A10, A13, and A14.  In
particular, no finite-word count is silently transferred to pi.

The agenda leaves the precise coherent logarithmic schedule and high-energy
constant to be defined.  They are fixed in Section 2.  All logarithms are
natural except `log_10`.  Square roots are positive real square roots.  Every
word coordinate and block start is zero-indexed.

## 2. One coherent overlapping-block process

Fix an integer `k>=8000` and put

```text
N=10^(4k),                 L=N+k-1,
a=ceil(k/2),               S_k={a,a+1,...,k},
s=#S_k=k-a+1=floor(k/2)+1.                              (2.1)
```

Thus `k=(1/4)log_10 N` exactly and `s>=k/2`; the selected-depth density is
`rho=1/2`.  Let `D={0,...,9}` and let
`x=(x_0,...,x_(L-1)) in D^L`.  For every `1<=m<=k`, define

```text
W_i^m(x)=(x_i,...,x_(i+m-1)),             0<=i<N,
c_x(w;m)=#{0<=i<N:W_i^m(x)=w},            w in D^m,
E_x(m)=sum_(w in D^m)c_x(w;m)^2.                          (2.2)
```

There are exactly `N` starts at every depth.  There is no wrapping or padding.
The last depth-`k` block ends at
`(N-1)+(k-1)=N+k-2=L-1`, so every displayed block exists.  Expanding the
squares gives the exact ordered, diagonal-inclusive identity

```text
E_x(m)=#{(i,j) in {0,...,N-1}^2:W_i^m(x)=W_j^m(x)}.       (2.3)
```

In particular, (2.3) includes exactly the `N` diagonal pairs.  Define

```text
B_k={x in D^L:E_x(m)>=N^2/m for every m in S_k}.           (2.4)
```

Every member of `B_k` is high-energy at `s>=rho*k` selected depths.  Requiring
all depths in `S_k` is stronger than merely requiring at least `rho*k` depths,
so a counterfamily inside (2.4) also applies to the latter event.

## 3. Conditional Renyi-2 quantities and exact telescoping

For fixed `x`, choose a start `I` uniformly from `{0,...,N-1}` and set
`Y_m=W_I^m(x)`.  Its empirical law is

```text
p_m(w)=c_x(w;m)/N,
C_m=sum_(w in D^m)p_m(w)^2=E_x(m)/N^2,
H_2(m)=-log C_m,
D_2(m)=m*log 10-H_2(m).                                  (3.1)
```

These definitions retain the ordered diagonal because `C_m` is the
probability that two independent uniform starts have equal blocks.  Since all
depths use the same starts and look-ahead word, for every `u in D^(m-1)`,

```text
p_(m-1)(u)=sum_(d in D)p_m(ud).                            (3.2)
```

For nonnegative `q_d`,
`sum_d q_d^2 <= (sum_d q_d)^2 <= 10*sum_d q_d^2`.
Applying this in every fiber of (3.2) gives

```text
C_m<=C_(m-1)<=10*C_m.                                     (3.3)
```

The schedule-relative conditional Renyi-2 increment and its uniform deficit
are defined, without invoking any disputed Renyi chain rule, by

```text
h_2(m|m-1)=H_2(m)-H_2(m-1)=log(C_(m-1)/C_m),
delta_2(m|m-1)=log 10-h_2(m|m-1).                         (3.4)
```

Equation (3.3) says exactly
`0<=h_2(m|m-1)<=log 10` and `0<=delta_2(m|m-1)<=log 10`.
The only unconditional accumulation identity available from these definitions
is the telescope

```text
sum_(m=a+1)^k delta_2(m|m-1)
 =D_2(k)-D_2(a)
 =(k-a)*log 10-(H_2(k)-H_2(a)).                           (3.5)
```

If depth `m` is high in the sense of (2.4), then `C_m>=1/m`, hence

```text
H_2(m)<=log m,                 D_2(m)>=m*log 10-log m.     (3.6)
```

The quantities in (3.6) are cumulative depth deficits, not fresh conditional
costs.  Summing (3.6) over `m` would count the same early digits repeatedly.
Section 4 makes this obstruction exact.

## 4. Exact infinite counterfamily

Put

```text
R=ceil(N/sqrt(a)),
F_k={x in D^L:x_q=0 for every 0<=q<R+k-1}.                 (4.1)
```

For `k>=8000`, one has `2<=a<N`, and therefore `1<=R<=N`.
There are `R+k-1` fixed coordinates.  The remaining coordinate interval is
`{R+k-1,...,N+k-2}`, which has exactly

```text
L-(R+k-1)=N-R                                             (4.2)
```

coordinates.  Consequently

```text
#F_k=10^(N-R).                                             (4.3)
```

Now fix `x in F_k`, `m in S_k`, and `0<=i<R`.  Its block endpoint obeys

```text
i+m-1 <= (R-1)+(k-1)=R+k-2,                               (4.4)
```

so `W_i^m(x)=0^m`.  Thus `c_x(0^m;m)>=R`, and the one ordered,
diagonal-inclusive summand for `0^m` gives

```text
E_x(m)>=R^2>=N^2/a>=N^2/m.                                (4.5)
```

The last inequality uses `m>=a`.  Equations (2.4) and (4.5) prove

```text
F_k subset B_k for every integer k>=8000.                  (4.6)
```

This is genuinely multiscale: the single construction simultaneously
witnesses every one of the `s=floor(k/2)+1` nested depths, rather than choosing
one bad depth or taking a union over depths.

For an entropy check, let `X` be uniform on `F_k`.  Its first `R+k-1` digits
are deterministic and its final `N-R` digits are independent uniform decimal
digits.  The ordinary Shannon chain rule therefore gives exactly

```text
H(X)=(N-R)*log 10,
N*log 10-H(X)=R*log 10.                                   (4.7)
```

The second line uses the agenda's `N log 10` census baseline; the extra `k-1`
look-ahead digits are among the fixed coordinates.  Every collision witness in
(4.5) reuses this same fixed prefix.  A valid coordinate martingale charges it
once, as (4.7) does.

## 5. Explicit failure of T144-scale additive accumulation

The unverified T144 note argues for a one-depth upper bound with saving
`N/(400*sqrt(m))` and type cost `10^m*log(N+1)+m`, under a different endpoint
convention.  T147 does not import that claim.  To test exactly the proposed
multiscale strengthening in the coherent convention (2.2), define the
T144-scale additive ansatz

```text
Phi_k=sum_(m=a)^k
      (N/(400*sqrt(m))-10^m*log(N+1)-m),                  (5.1)
#B_k <= 10^N*exp(-Phi_k).                                 (ADD-144)
```

We now disprove `(ADD-144)` for every `k>=8000`, with all constants explicit.
First, `s>=k/2` and `m<=k` on `S_k`, so

```text
sum_(m=a)^k 1/sqrt(m) >= s/sqrt(k) >= sqrt(k)/2.           (5.2)
```

Also `s<=k`, `10^m<=10^k`, and, because
`N=10^(4k)`, `k>=2`, `log 2<1`, and `4 log 10<10`,

```text
log(N+1)<=log(2N)=log 2+4k*log 10<10k.
```

Therefore

```text
sum_(m=a)^k 10^m*log(N+1) < 10*k^2*10^k,
sum_(m=a)^k m <= k^2,                                    (5.3)
Phi_k > N*sqrt(k)/800-10*k^2*10^k-k^2.                   (5.4)
```

On the other hand `a>=k/2`, `ceil(t)<=t+1`, `log 10<3`, and
`3*sqrt(2)<5`, whence

```text
R*log 10 <=(N/sqrt(a)+1)*log 10
           <5*N/sqrt(k)+3.                                (5.5)
```

For `k>=8000`,

```text
N*sqrt(k)/800-5*N/sqrt(k) >= N*sqrt(k)/1600.              (5.6)
```

For integers `k>=1`, `k<=10^k`, and hence

```text
10*k^2*10^k+k^2+3 <=12*10^(3k).                           (5.7)
```

Finally `k>=8000` implies `10^k>19200`, so, using `sqrt(k)>=1`,

```text
N*sqrt(k)/1600
 >=10^(4k)/1600
 >12*10^(3k).                                             (5.8)
```

Combining (5.4)--(5.8) proves

```text
Phi_k>R*log 10.                                            (5.9)
```

But (4.3), (4.6), and (5.9) give

```text
#B_k>=#F_k=10^N*exp(-R*log 10)
             >10^N*exp(-Phi_k),                           (5.10)
```

which is the strict negation of `(ADD-144)`.  The family `{F_k:k>=8000}` is an
exact infinite counterfamily, not finite evidence.

More generally, (4.3) has census deficit only
`R log 10=O(N/sqrt(k))`, while
`N*sum_(m=a)^k m^(-1/2)>=N*sqrt(k)/2`.  Hence no estimate with a fixed positive
multiple of the latter saving and an `o(N*sqrt(k))` total error can hold for
the event (2.4).  This asymptotic statement follows directly by dividing by
`N*sqrt(k)`; the counterfamily cost has ratio `O(1/k)`.

## 6. What fails in an entropy-martingale proof

The block process itself is coherent, and (3.5) is a valid conditional
Renyi-2 telescope.  The false step would be to convert each high cumulative
deficit (3.6) into a fresh disjoint-block Shannon saving of order
`N/sqrt(m)`, then add those savings over `m`.  In `F_k`, all depth events are
caused by the same `R` starts and the same `R+k-1` zero coordinates.  Refining
`0^m` to `0^(m+1)` costs only one additional fixed coordinate globally, not a
new set of about `N/m` disjoint blocks.

Thus high collision at `rho*k` coherent depths does **not** force the proposed
additive T144-scale entropy deficit.  The correct obstruction is shared-prefix
reuse across nested depths.  The only automatic Renyi accumulation is (3.5),
and the ordinary word-entropy chain rule (4.7) prevents charging a coordinate
more than once.  This is a terminal counterfamily, so the report does not end
`OPEN WITH ONE NAMED CHAIN-RULE GAP`.

## 7. Fingerprint comparison

The exact comparator reports are delivered as `prior-T140-REPORT.md` and
`prior-T144-REPORT.md`; their hashes and verification levels are recorded in
`PRIOR_INDEX.md`.  They are comparison evidence only, not premises of Sections
2--6.

| item | supplied level and fingerprint | T147 boundary |
|---|---|---|
| T140 | source theorems are `literature-checked`; local encodings and deductions are `proof sketch` | The T140 report audits edge-sparse/independent hypergraph-container conclusions and finds them inapplicable to edge-rich collision transversals. T147 invokes no container theorem, codegree, or supersaturation premise; it gives an edge-rich word family and counts it exactly. |
| T144 | unverified `proof sketch` note plus finite `experiment` | The T144 note argues a one-depth method-of-types bound, then handles positive-density depths only by selecting one bad depth and taking a union. T147 neither assumes that bound nor repeats its union: one family is simultaneously heavy at every depth in `S_k` and refutes adding the displayed one-depth savings. |

T147 does not contradict the one-depth estimate argued in T144.  At the
shallowest selected depth, T147 pays `R log 10` of order `N/sqrt(k)`, the same
scale as one T144-style saving.  It contradicts only repeated charging at
`Theta(k)` nested depths.  This distinction is why the result is not T144's
one-depth union bound in different notation.  It also does not reverse T140:
T140's audited sufficient container certificates remain a separate
inapplicability result.

## 8. Separate unproved pi-transfer premise

**PI-MULTISCALE-MEMBERSHIP-EXCLUSION-T147 (UNPROVED PI-SPECIFIC PREMISE; NOT
ASSERTED).**  For an unbounded sequence of integers `k`, with
`N=10^(4k)` and `L=N+k-1`, the exact length-`L` decimal segment generating the
first `N` base-10 orbit starts of pi lies outside `B_k`; equivalently, at least
one `m in {ceil(k/2),...,k}` has ordered diagonal-inclusive equal-block energy
strictly below `N^2/m`.

Nothing in the counterfamily, the census lower bound, or the replay proves this
arithmetic-membership exclusion.  A description-length route would need an
independent pi-specific lower bound strong enough to exclude the relevant
multiscale exceptional census; a T107 route would additionally need its
separate checked conversion from symbolic rows to the required Fourier/metric
condition.  The premise is stated only to expose the transfer obligation.  It
is not adopted as a conjecture and yields no conclusion here.

Accordingly this report makes no fixed-pi, A1, C1, or C2 claim.

## 9. Replay and endpoint

From a directory containing only the delivered artifacts, run

```text
python3 verify_t147.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and comparator hashes; exact finite block
counts, endpoints, marginal identities, and conditional Renyi bounds; the
counterfamily cardinality and all selected depths at small parameters; and the
explicit inequalities (5.2)--(5.9) at `k=8000` and larger sample values.  Those
checks guard transcription and can falsify intermediate formulas.  The proof
for every integer `k>=8000` is Sections 2--6, not the finite replay.

SCOPED_VERDICT (1/1): **close**.

The scoped object being closed is the proposed additive successor to T144:
positive-density high collision across nested logarithmic depths does not
permit the one-depth description saving to be charged independently at every
depth.  The exact infinite shared-prefix family settles that question without
weakening it to one-depth selection.  It does not close another multiscale
statistic that explicitly discounts reuse, and it supplies no pi transfer.
