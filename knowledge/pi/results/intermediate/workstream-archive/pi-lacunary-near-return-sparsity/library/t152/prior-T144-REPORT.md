# T144: an explicit overlapping-block method-of-types census

Date: 2026-08-12 UTC.

Claim label: `proof sketch`.  The argument is elementary and constant-explicit,
but this note has no kernel-checked formalization.  The replay is an
`experiment`: it checks exact finite identities and the numerical inequalities
used below; it is not evidence for the universal theorem.  No literature
theorem is a premise.

```text
KAPPA: 1/4
A: 1
c_A: 1/400
C_A: 1
SCOPED_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Provenance, normalized statement, and ambiguities

The canonical problem has no external Erdős Problems URL.  It was formulated
by this program on 2026-07-22.  The byte-exact delivered
`canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks an open question about ordered, diagonal-inclusive metric near returns
of the fixed decimal orbit of pi.  T144 does not answer it.  This report proves
a finite-word sibling census, falling under recorded ambiguities A10 and A14.

All logarithms below are natural except `log_10`.  Let
`D={0,...,9}`.  For integers `N>=1` and `1<=m<=N`, let

```text
x=(x_0,...,x_(N-1)) in D^N,       M=N-m+1,
W_i^m(x)=(x_i,...,x_(i+m-1)),     0<=i<M,
c_m(x,w)=#{0<=i<M:W_i^m(x)=w},
E_m(x)=sum_(w in D^m)c_m(x,w)^2.                         (1.1)
```

Thus `E_m` counts ordered equal-block pairs and includes all `M` diagonal
pairs.  Starts do not wrap or pad.  The word has exactly `N` digits, so its last
legal block ends at `M-1+m-1=N-1`.

The agenda leaves `A` to be fixed explicitly; this note takes `A=1`.  It also
fixes the rational `kappa=1/4`.  The strict bad event is

```text
B_(N,m)={x in D^N:E_m(x)>M^2/m}.                          (1.2)
```

At `m=1` the event is empty because `E_1<=M^2`.  This endpoint will not be
hidden in an asymptotic qualifier.

## 2. The theorem

**Theorem 2.1 (explicit T144 census).**  For every pair of integers `N,m` with

```text
1<=m<=(1/4)*log_10 N,                                    (2.1)
```

one has

```text
#B_(N,m)
 <= 10^N exp(-N/(400*sqrt(m))+10^m*log(N+1)+m).           (2.2)
```

This has exactly the requested shape with

```text
A=1, kappa=1/4, c_A=1/400, C_A=1.
```

Notice that (2.1) itself implies `N>=10^(4m)`, so in particular `N>=100` and
`m<=N`; no separate sufficiently-large qualifier is needed.

The proof occupies Sections 3--6.  It deliberately uses a weaker explicit
entropy certificate rather than claiming the exact Renyi-2 constrained
optimizer.

## 3. Residue classes and retained collision

Split all starts, not a selected subset, by their residue modulo `m`:

```text
I_r={i:0<=i<M and i=r mod m},             0<=r<m,
q_r=#I_r,
c_(r,w)=#{i in I_r:W_i^m(x)=w},
E_r=sum_w c_(r,w)^2.                                      (3.1)
```

Some `I_r` may be empty in a general endpoint calculation.  They are harmless:
`q_r=E_r=0`.  The classes partition the `M` starts, so

```text
sum_r q_r=M,       c_m(x,w)=sum_r c_(r,w).                (3.2)
```

For each `w`, Cauchy--Schwarz gives

```text
(sum_r c_(r,w))^2 <= m*sum_r c_(r,w)^2.
```

Summing over `w` yields the exact convexity loss

```text
E_m(x)<=m*sum_r E_r.                                      (3.3)
```

If `x` is bad, (3.3) implies `sum_r E_r>M^2/m^2`.  Under (2.1) one has
`M>=m`.  Since the `q_r` differ by at most one,

```text
sum_r q_r^2 <= max_r(q_r)*sum_r q_r
              =ceil(M/m)*M
              <=(2M/m)*M=2M^2/m.                         (3.4)
```

If every `E_r<=q_r^2/(2m)`, then

```text
sum_r E_r <= (1/(2m))*sum_r q_r^2 <=M^2/m^2,             (3.5)
```

contradicting the strict lower bound.  Hence a bad word has at least one residue
`r` satisfying

```text
E_r>q_r^2/(2m).                                           (3.6)
```

The implication intentionally loses a factor two; it avoids optimizing the
near-equal class sizes.

Starts in one `I_r` differ by multiples of `m`.  Their length-`m` coordinate
intervals are therefore pairwise disjoint.  If `q=q_r`, their union uses
exactly `qm` digits and the complement has exactly `N-qm` unrestricted digits.
Writing `M=am+b`, `0<=b<m`, gives `q_r` equal to `a+1` for `r<b` and `a`
otherwise.  In particular every nonempty class satisfies

```text
q>=floor(M/m)>=(M-m+1)/m=(N-2m+2)/m.                     (3.7)
```

Under (2.1), `N>=10^(4m)>=4m`, so (3.7) gives

```text
qm>=N-2m+2>=N/2.                                         (3.8)
```

These are all endpoint losses.

## 4. A constant-explicit Renyi-2 entropy certificate

Let `K=10^m`.  For a probability vector `p=(p_1,...,p_K)`, write

```text
H(p)=-sum_j p_j log p_j,       C_2(p)=sum_j p_j^2,
D(p)=log K-H(p)=sum_j p_j log(K*p_j).                     (4.1)
```

`D` is the Shannon deficit from the uniform law.  The row condition (3.6), for
the empirical law `p_j=n_j/q`, is `C_2(p)>1/(2m)`.

**Lemma 4.1.**  If `m>=2`, `K=10^m`, and
`C_2(p)>1/(2m)`, then

```text
D(p)>sqrt(m)/100.                                         (4.2)
```

**Proof.**  Put `t=1/(2m)` and

```text
S={j:p_j>t/2},       alpha=sum_(j in S)p_j.               (4.3)
```

For `j notin S`, `p_j^2<=(t/2)p_j`, while
`sum_(j in S)p_j^2<=alpha^2`.  Therefore

```text
t<C_2(p)<=alpha^2+t/2,
alpha>sqrt(t/2)=1/(2*sqrt(m)).                            (4.4)
```

The log-sum inequality on `S` and its complement says

```text
D(p)>=alpha log(alpha*K/|S|)
       +(1-alpha)log((1-alpha)*K/(K-|S|)).                (4.5)
```

The second term is at least `(1-alpha)log(1-alpha)>=-alpha`.
Also `|S|<2/t=4m` and (4.4) gives

```text
D(p)> alpha*(log(alpha*K/(4m))-1).                        (4.6)
```

There are two cases.

1. If `alpha<=1/2`, the function
   `a -> a(log(a*K/(4m))-1)` has derivative `log(a*K/(4m))`, positive for
   `a>=1/(2sqrt(m))` and `m>=2`.  Thus (4.4)--(4.6) imply

```text
D(p)>(m*log(10)-log(8*m*sqrt(m))-1)/(2*sqrt(m)).           (4.7)
```

For `m>=2`, the right side is greater than `sqrt(m)/100`.  It is enough to
prove the slightly stronger inequality

```text
0.98*m*log(10)>log(8*m*sqrt(m))+1.                        (4.8)
```

At `m=2`, (4.8) follows by direct decimal bounds
`1.96 log 10>4.51` and `log(16sqrt(2))+1<4.13`.  Its left-minus-right
derivative, as a real function of `m>=2`, is
`0.98 log 10-3/(2m)>0`, so it remains true.

2. If `alpha>1/2`, apply (4.5) only with the coarse bounds
   `|S|<4m` and `(1-alpha)log((1-alpha)K/(K-|S|))>=-log 2`.
   Since `alpha log(alpha*K/(4m))` is increasing for
   `alpha>=1/2`, this gives

```text
D(p)>(m*log(10)-log(8m))/2-log 2.                         (4.9)
```

For `m>=2`, (4.9) is greater than `sqrt(m)/100`: at `m=2` the
left side exceeds `0.20`, and its derivative is
`log(10)/2-1/(2m)-1/(200sqrt(m))>0`.

Both cases prove (4.2). QED.

The argument solves the needed Renyi-2 constrained entropy problem by a valid,
explicit lower bound on its Shannon deficit.  It does not assert that (4.2) is
the optimum; the exact optimizer and best constant are irrelevant to (2.2).

## 5. Counting empirical block types

Fix `m>=2` and one residue class of size `q`.  Its disjoint blocks form a word
of length `q` over an alphabet of exactly `K=10^m` blocks.  A type is a vector

```text
(n_1,...,n_K),       n_j>=0,       sum_j n_j=q.            (5.1)
```

There are exactly `binom(q+K-1,K-1)` types and hence at most

```text
(q+1)^K<=(N+1)^K.                                        (5.2)
```

For one type, the number of block sequences is the multinomial coefficient
`q!/product_j n_j!`.  The multinomial theorem applied to
`p_j=n_j/q` gives the standard bound

```text
q!/product_j n_j! <= exp(q*H(p)).                         (5.3)
```

Indeed the type term in `(sum_j p_j)^q=1` is precisely the left side times
`product_j p_j^(n_j)`, and rearranging gives (5.3), with the convention
`0^0=1`.

If (3.6) holds, Lemma 4.1 and `K=10^m` give

```text
exp(qH(p)) <= K^q*exp(-q*sqrt(m)/100).                    (5.4)
```

The selected blocks use `qm` digits, so `K^q=10^(qm)`; the remaining
`N-qm` digits have exactly `10^(N-qm)` assignments.  Multiplying (5.2)--(5.4),
the number of words for which this particular residue is heavy is at most

```text
10^N exp(-q*sqrt(m)/100+K*log(N+1)).                      (5.5)
```

By (3.8), `q*sqrt(m)=(qm)/sqrt(m)>=N/(2sqrt(m))`.  A union over the `m`
residue classes and `log m<=m` gives

```text
#B_(N,m)
 <=10^N exp(-N/(200sqrt(m))+10^m*log(N+1)+m).             (5.6)
```

This is stronger than (2.2).  For `m=1`, `B_(N,1)` is empty.  Theorem 2.1
follows for every endpoint in (2.1). QED.

## 6. Why the displayed exponent is genuinely negative

The positive type term in (2.2) is not harmless by notation alone.  Under
`m<=(1/4)log_10 N`,

```text
10^m<=N^(1/4),             m<=N^(1/4).                    (6.1)
```

The second inequality follows from `N>=10^(4m)>=m^4`.  Also
`sqrt(m)<=sqrt(N)`.  Therefore the non-baseline exponent in (2.2) is at most

```text
-sqrt(N)/400+N^(1/4)*(log(N+1)+1).                        (6.2)
```

For every `N>=10^16`, `log(N+1)+1<=N^(1/8)`: at the endpoint the two sides are
less than `38` and equal to `100`, respectively, and the power thereafter
grows faster (differentiate, or use monotonicity of
`N^(1/8)/(log(N+1)+1)`).  Hence (6.2) is at most

```text
-sqrt(N)/400+N^(3/8).                                    (6.3)
```

For every `N>=400^8`, `N^(3/8)<=sqrt(N)/400`, so (6.3) is nonpositive.
More usefully, for every

```text
N>=800^8,                                                 (6.4)
```

it is at most `-sqrt(N)/800`.

## 7. Logarithmic-depth union bound

Let

```text
L_N=floor((1/4)log_10 N),
Bad_N(x)={m in {1,...,L_N}:E_m(x)>M_m^2/m}.               (7.1)
```

For `N>=800^8`, summing (2.2) and using Section 6 gives

```text
#{x:Bad_N(x) is nonempty}
 <=10^N*L_N*exp(-sqrt(N)/800).                            (7.2)
```

Since `L_N<=N`, this is at most

```text
10^N exp(-sqrt(N)/800+log N).                             (7.3)
```

Fix any rational density `rho` with `0<rho<=1`.  The event

```text
#Bad_N(x)>=ceil(rho*L_N)                                  (7.4)
```

is a subset of the nonempty event in (7.2).  Thus the same bound (7.3)
controls words bad at a fixed positive density of logarithmic depths.  No
independence among depths is assumed.  This union bound is deliberately
stronger than needed but does not multiply single-depth savings: it uses only
the fact that positive density implies at least one bad depth.

Finally `-sqrt(N)/800+log N -> -infinity`; for example, retaining the inherited
condition `N>=800^8` (which is larger than `1600^4`), one has
`log N<=N^(1/4)<=sqrt(N)/1600`, so (7.3) is at most
`10^N exp(-sqrt(N)/1600)`.  Therefore the bad-density proportion tends to
zero with an explicit stretched-exponential bound.

## 8. Named fingerprint comparison and novelty boundary

The following prior notes are comparison memory only.  Their prose deductions
are not used as established premises of Theorem 2.1.

| item | supplied level and fingerprint | T144 boundary |
|---|---|---|
| T119 | recovered report; source claims self-labeled literature-checked, deductions `proof sketch`, package incomplete; SHA `72b10e921761874158893bb9cbb7454094bcbc59bbdfc787f33bbf355b63f23a` | asks whether collision concentration forces predictive, Hankel, or Prony rank. T144 infers no rank: it counts disjoint-block empirical types directly. |
| T121 | literature report with `proof sketch` deductions; SHA `01b97953941608b41b0fcd12cc5be0047f447be28d7cd26f8bae6506717e6cf2` | expands collision by forward Parseval/global L2 and applies arithmetic cancellation in models. T144 is an inverse census over all finite words and uses no Fourier estimate. |
| T135 | literature audit with `proof sketch` deductions; SHA `4439850a49ee2fa7351d85daf366eba4b2b4a55e756a15bf7c431d92fb195e21` | rejects unconditional projection-to-full Renyi-2 tensorization. T144 never infers full collision from coordinate projections; it extracts one class by (3.3), then counts that class. |
| T137 | unverified `proof sketch` note/experiment; SHA `84cbe349ea52137d2bd8bbf90e1eab389a599271f9d404b2e12255d3188d29f5` | argues about Lorenz meets and tensor powers. T144 uses neither majorization meets nor tensorization; no T144 conclusion depends on T137. |
| T140 | source statements literature-checked, encodings and deductions `proof sketch`; SHA `ff05177ccaaebfd56d41467f2f74dce085aae3b855be95f6d1c458526541f35c` | closes two hypergraph-container certificates for edge-rich overlapping collisions. T144 uses no container, supersaturation theorem, or codegree; residue classes make the counted blocks disjoint. |

The refreshed orchestrator input, SHA
`bdd7a60c7eec68cb9d47382e968698df3f1e2864d4528a03b9e4b275365718e1`,
lists T142 only as a `revise` result at `pinned` verification: its skeptic found
three source-label inconsistencies.  The metadata lists paths from that earlier
run, but no T142 artifact is present in the supplied T144 knowledge library and
T142 is not an accepted result in this snapshot.  Therefore there is no
**accepted T142 fingerprint** to compare as established.  T144 makes no novelty
claim from that status, and no proof step depends on it.  A later accepted
readable T142 artifact must be compared before any novelty claim.

The theorem's mathematical distinction is scoped: it is a direct
overlap-to-disjoint-class method-of-types census, not any of the five excluded
mechanisms.  This is not a literature novelty assertion.

## 9. Separate unproved pi transfer premise

**PI-INCOMPRESSIBILITY-T144 (`conjecture`; UNPROVED PI-SPECIFIC PREMISE; not
asserted).**  For every sufficiently large depth `m`, there is a prefix length
`N` with `m<=(1/4)log_10 N` such that the first `N` relevant decimal digits of
the fixed pi expansion lie outside `B_(N,m)` (or outside the corresponding
all-orbit-start version after its endpoint is separately proved).

Theorem 2.1 says only that `B_(N,m)` is a small subset of all `10^N` words.  A
fixed deterministic word can lie in every small exceptional set.  No counting
argument, source, or computation here proves the displayed incompressibility
property for pi.  Moreover T7 uses `N` orbit starts with look-ahead through
`N+m-2`, whereas (1.1) uses `N-m+1` starts in a length-`N` word; this endpoint
must not be silently identified.

Thus transfer toward T7 requires a new pi-specific incompressibility theorem
excluding the resulting bad-prefix census and a checked endpoint conversion.
No fixed-pi result, canonical A1 result, C1 result, or C2 result is claimed.

## 10. Replay and endpoint

From a directory containing only the delivered artifacts, run

```text
python3 verify_t144.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum canonical_statement.txt
```

The verifier uses Python integers and `Fraction` for combinatorial identities.
Floating-point evaluations only test the explicit real inequalities and finite
small-word instances; they do not prove Theorem 2.1.  The universal arguments
are Sections 3--7.

SCOPED_VERDICT (1/1): **develop**.

Develop the explicit inverse finite-word census as a symbolic related-model
mechanism.  The result survives the required logarithmic-depth union bound and
is structurally distinct from the named excluded fingerprints.  Development
does not include a pi transfer: PI-INCOMPRESSIBILITY-T144 is unproved, and no
fixed-pi, A1, C1, or C2 claim is made.
