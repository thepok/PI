# T99: the exceptional-prime Stoneham family

Date: 2026-08-09 UTC.

Result label: `proof sketch`. The bounded primary-source audit in
`SOURCE_PINS.md` is `literature-checked` as of the displayed date. The family
argument below is proved independently from first principles, but it has not
been formalized in Lean. Finite replay checks are `sanity checks` only.

This is an A13 sibling of the immutable fixed-pi question. It changes the
named point and the scale and uses an off-diagonal pair-correlation statistic.
It is not evidence for, and makes no claim about, pi, C1, or C2.

## 1. Provenance, normalized statement, and ambiguities

The byte-exact canonical statement is `canonical_statement.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

The canonical question concerns the ordered, diagonal-inclusive, strict
circle-distance count for the base-10 orbit of pi, with quantifiers

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1.
```

The sibling studied here has the following literal quantifiers. For every
integer `b>=2` satisfying `ord_9(b)=6`, define

```text
alpha_(b,3) = sum_(q>=1) 1/(3^q*b^(3^q)),
x_n = {b^n*alpha_(b,3)}, n>=1.
```

For every real `s>=0` and integer `N>=1`, define

```text
F_N(s) = (1/N) * #{(i,j): 1<=i!=j<=N,
                            ||x_i-x_j||_(R/Z) <= s/N}.       (1.1)
```

Pairs are ordered, the diagonal is excluded, distance is circular, and the
threshold is non-strict, matching the pinned pair-correlation source. PPC
means that, for every real `s>=0`, `F_N(s)` tends to `2*s` as `N` tends to
infinity.

The potentially ambiguous choices are fixed as follows.

1. `ord_9(b)=6` is a hypothesis for each fixed integer base, not a claim
   uniform in a varying base. It is equivalent to `b=2 or 5 (mod 9)`.
2. The theorem is universal in admissible `b`; its subsequence `N=b^w` and
   all constants are then allowed to depend on that fixed base as displayed.
3. Equality is asserted only for rational skeleton values, never for the
   irrational orbit points.
4. The proof is a lower-bound proof. It need not classify pairs with unequal
   skeleton values.
5. Auxiliary indices are `0,...,N-1`, but all retained pairs have indices in
   `3,...,N-1`, hence already lie in the source window `1,...,N`.

## 2. Bounded primary-source coverage

Stoneham, journal p. 372, equation (1.0), defines

```text
w(g,p) = sum_(q>=1) 1/(p^q*g^(p^q))
```

for an odd prime `p` and primitive root `g modulo p^2`; the following sentence
states normality and stronger arithmetic properties. Thus `p=3`, `g=b`, and
`ord_9(b)=6` identify every number in this note with Stoneham's family.
Normality is not used here, and Stoneham states no pair-correlation theorem.

Larcher--Stockinger define (1.1) on preprint pp. 1--2, equation (1), and state
on preprint p. 4, Theorem 3, only

```text
({2^n*alpha_(2,3)})_(n in N) does not have PPC.             (2.1)
```

Their proof on pp. 14--16 chooses `s=1`, `N=2^w`, and uses threefold
rational-skeleton repetition together with an upper-deficiency route. The
theorem does not quantify over `b`. Their general Theorem 1 is a gap criterion,
but the paper gives no displayed verification of that criterion for every
`alpha_(b,3)`.

The dated searches and blockers are recorded in `SOURCE_PINS.md`. No inspected
source states the every-base theorem below. That is a bounded coverage verdict,
not an exhaustive novelty claim.

The T93 and T96 notes are unverified proof sketches. They were used only as
locator and mechanism maps; no mathematical claim from either note is a
premise below.

## 3. Terminal family theorem

### Theorem 3.1 (quantified A13 sibling)

For every integer `b>=2` with `ord_9(b)=6`, let `alpha_(b,3)`, `x_n`, and
`F_N` be as in Section 1. Then

```text
liminf_(w->infinity) F_(b^w)(1/6) >= 6/5.                  (3.1)
```

The Poisson value at `s=1/6` is `2*s=1/3`, so (3.1) has the explicit
normalized excess

```text
6/5 - 1/3 = 13/15.                                        (3.2)
```

Consequently `({b^n*alpha_(b,3)})_(n>=1)` does not have Poissonian pair
correlation. Sections 4--9 prove the theorem.

## 4. Every order-lifting step

### Lemma 4.1

For every admissible `b` and every integer `q>=1`,

```text
ord_(3^q)(b) = 2*3^(q-1),                                 (4.1)
v_3(b^(2*3^(q-1))-1) = q.                                 (4.2)
```

### Proof

Reduction of `ord_9(b)=6` modulo 3 gives `ord_3(b)=2`: the order modulo 3
divides 2, and order 1 would make the order modulo 9 divide 3. Write

```text
b^2 = 1+3*c.
```

Here `3` does not divide `c`, since otherwise `b^2=1 (mod 9)`, contradicting
the order-six hypothesis.

We now prove the valuation lift rather than cite it. If
`V=1+3^(r+1)*d`, where `r>=0` and `3` does not divide `d`, then

```text
V^3-1 = 3^(r+2)*d + 3^(2*r+3)*d^2 + 3^(3*r+3)*d^3.        (4.3)
```

The first term has valuation `r+2`; both later terms have strictly greater
valuation, including when `r=0`. Induction starting at `b^2=1+3*c` gives

```text
v_3((b^2)^(3^r)-1) = r+1.                                 (4.4)
```

If `u>=1` is prime to 3 and `W=1+3^k*e` with `3` not dividing `e`, the
linear term of `W^u-1` has valuation `k` and all later terms have greater
valuation. Hence raising to `u` does not change the valuation. Writing any
`m>=1` as `m=3^r*u` now yields

```text
v_3(b^(2*m)-1) = 1+v_3(m).                                (4.5)
```

If `b^d=1 (mod 3^q)`, reduction modulo 3 gives `2|d`; write `d=2*m`.
Equation (4.5) forces `3^(q-1)|m`. Conversely, (4.5) says that
`d=2*3^(q-1)` works and has exact valuation `q`. This proves (4.1)--(4.2)
for every `q`.

## 5. Truncation and no hidden wrap

For `n>=0`, put `q(n)=0` if `n<3`; otherwise let `q(n)>=1` be the unique
integer with

```text
3^q(n) <= n < 3^(q(n)+1).
```

Define

```text
z_n   = {sum_(1<=k<=q(n)) b^(n-3^k)/3^k},
tau_n =  sum_(k>q(n))     b^(n-3^k)/3^k.                  (5.1)
```

For `q=q(n)>=1`, `z_n` is a multiple of `1/3^q`. Section 6 shows its
numerator is a unit, so `z_n<=1-1/3^q`. Since `n<=3^(q+1)-1`,

```text
0 < tau_n <= (1/b)*sum_(k=q+1)^infinity 1/3^k
          = 1/(2*b*3^q) < 1/3^q.                         (5.2)
```

For `q=0`, `z_n=0` and the same direct geometric bound is below one.
Therefore there is no wrap after adding the tail:

```text
x_n = z_n+tau_n.                                          (5.3)
```

The active terms also give the exact recurrence

```text
z_0=0,
z_n={b*z_(n-1)+r_n},
r_n=1/n if n=3^q for an integer q>=1, and r_n=0 otherwise. (5.4)
```

## 6. Complete triple-skeleton multiplicities

At an injection time, write `z_(3^q-1)=c/3^(q-1)`, with `c=0` when
`q=1`. Then

```text
z_(3^q) = {(3*b*c+1)/3^q} = u_q/3^q,
u_q=1 (mod 3).                                             (6.1)
```

Thus the numerator is a unit. There is no injection inside

```text
B_q={3^q,...,3^(q+1)-1}.
```

Put `P_q=2*3^(q-1)`. By (4.1), for `0<=j<3*P_q`,

```text
z_(3^q+j)=(u_q*b^j mod 3^q)/3^q.                          (6.2)
```

Every `P_q` consecutive powers visit all units modulo `3^q` exactly once.
The block length is `2*3^q=3*P_q`. Hence every reduced residue of exact
denominator `3^q` occurs exactly three times, at exponents separated by
`P_q`:

```text
z_(3^q+j)=z_(3^q+j+P_q)=z_(3^q+j+2*P_q), 0<=j<P_q.       (6.3)
```

Also `z_0=z_1=z_2=0`, exactly three copies. Values from different blocks
cannot coincide because their reduced denominators differ. This is a complete
multiplicity classification, not an equidistribution approximation.

## 7. Exact ordered pair count at N=b^w

Fix an integer `w>=1` sufficiently large that `N=b^w>3`. Since `3` does not
divide `b`, `N` is not a power of 3. Let `ell>=1` be unique with

```text
A:=3^ell < N < 3^(ell+1).                                 (7.1)
```

Put

```text
P=2*3^(ell-1)=2*A/3,
H=N-A=a*P+r, 0<=r<P.                                      (7.2)
```

Since `0<H<3*P`, the quotient satisfies `a in {0,1,2}`.

Among `z_0,...,z_(A-1)`, Section 6 gives exactly `A/3` values, each with
multiplicity three. Their complete ordered off-diagonal count is

```text
(A/3)*3*2 = 2*A.                                          (7.3)
```

The first `H=a*P+r` entries of the current block comprise `a` complete
periods followed by `r` distinct residues. Exactly `r` residues have
multiplicity `a+1`; the other `P-r` have multiplicity `a`. Their complete
ordered count is

```text
(P-r)*a*(a-1)+r*(a+1)*a = P*a*(a-1)+2*a*r.                (7.4)
```

Different levels have different reduced denominators, so there are no omitted
cross-level equalities. The exact skeleton collision count is therefore

```text
C_z(N)=2*A+P*a*(a-1)+2*a*r.                               (7.5)
```

## 8. Every tail and endpoint-loss inequality

Suppose `n<m` lie in one block `B_q` and `z_n=z_m`. Their tails begin with
the same summand index, so

```text
tau_m=b^(m-n)*tau_n,
0<x_m-x_n=tau_m-tau_n<tau_m.                              (8.1)
```

If the later index satisfies

```text
m<=3^(q+1)-w,                                             (8.2)
```

then each exponent in `tau_m` is at most `-w`. Since `N=b^w`,

```text
tau_m <= b^(-w)*sum_(k=q+1)^infinity 1/3^k
      = 1/(2*3^q*N) <= 1/(6*N).                           (8.3)
```

The strict inequality in (8.1) therefore certifies circular distance strictly
below `1/(6N)`.

Only the final at most `w` possible later indices in a block can fail (8.2).
Each has at most two earlier partners with the same skeleton value. Restoring
both orders costs a factor two. There are `ell` noninitial blocks intersecting
`0,...,N-1`. Discarding all six ordered pairs from the initial zero triple as
well gives the explicit loss

```text
E_w=4*ell*w+6.                                             (8.4)
```

Every retained index is between 3 and `N-1`, so every retained pair lies in
the source window `1,...,N`. Thus

```text
F_N(1/6) >= (C_z(N)-E_w)/N, N=b^w.                        (8.5)
```

Finally, `3^ell<N=b^w` gives `ell<w*log_3(b)`, and hence

```text
E_w/N < (4*w^2*log_3(b)+6)/b^w -> 0.                      (8.6)
```

This accounts explicitly for every pair discarded from the skeleton count.

## 9. Uniform normalized excess

Put `t=r/P`, so `0<=t<1`. Dividing (7.2) and (7.5) by `A` gives

```text
N/A   = 1+(2/3)*(a+t),
C_z/A = 2+(2/3)*(a*(a-1)+2*a*t).                          (9.1)
```

The complete three-case calculation is

```text
a=0: C_z/N = 6/(3+2*t)       >= 6/5,
a=1: C_z/N = (6+4*t)/(5+2*t) >= 6/5,
a=2: C_z/N = (10+8*t)/(7+2*t)>= 10/7 > 6/5.              (9.2)
```

For `a=0`, cross multiplication gives `30>=18+12*t`; for `a=1`, it gives
`30+20*t>=30+12*t`; for `a=2`, the displayed ratio is increasing and its
left endpoint is `10/7`. These inequalities hold for every real `0<=t<1`,
not merely the finite values replayed by the verifier. Therefore

```text
C_z(N)/N >= 6/5.                                          (9.3)
```

Combining (8.5), (8.6), and (9.3) proves (3.1). If PPC held, its defining
limit at `s=1/6` would force every subsequence to tend to `1/3`, contradicting
the lower limit `6/5`. This proves Theorem 3.1.

## 10. T93/T96 fingerprints and the killed s=1 route

The comparison is mechanism-level only; T93 and T96 remain unverified notes.

| Note or source | Repetition | Scale | Fingerprint |
|---|---:|---:|---|
| T93 note, `(10,7)` | Sevenfold | `s=1` | Argues for a uniform lower excess above 2 |
| T96 note, `p>=5` | `p`-fold | `s=1` | Argues for a uniform lower excess above 2 |
| Larcher--Stockinger Theorem 3, `(2,3)` | Threefold | `s=1` | Published upper-deficiency argument |
| T99 family proof sketch | Threefold | `s=1/6` | Uniform lower count `6/5`, versus Poisson value `1/3` |

The literal T96-style `s=1` lower-excess calculation fails for `p=3`.
Subtracting twice the first line of (9.1) from the second gives

```text
C_z/A-2*N/A = (2/3)*(a*(a-3)+2*(a-1)*t).                 (10.1)
```

Its values are

```text
a=0: -(4/3)*t,
a=1: -4/3,
a=2: -(4/3)*(1-t).                                        (10.2)
```

Thus every strict prefix with `0<t<1` in the endpoint cases, and every prefix
with `a=1`, has `C_z/N<2`; no positive uniform lower excess over the Poisson
value at `s=1` is available from these equal-skeleton pairs. This is an exact
failure of that proposed extension, not a failure of Theorem 3.1.

The smallest admissible base is `b=2`, since

```text
2,4,8,7,5,1 (mod 9)
```

gives `ord_9(2)=6`. The smallest two-level check is `N=2^4=16`:
`A=9`, `P=6`, `a=1`, `r=1`, and

```text
C_z(16)=20, C_z(16)/16=5/4<2.                            (10.3)
```

Equation (10.3) is a finite `sanity check`; the universal kill is the symbolic
identity (10.1)--(10.2). The repair is to use the smaller scale `s=1/6`, where
additional close pairs only strengthen the lower bound.

## 11. Fixed-pi transfer hypothesis and cheap kill test

The exact transfer hypothesis toward the fixed-pi T7 frontier is the existence
of rational approximants whose first `N` decimal-orbit points have `o(1/N)`
uniform phase error while retaining a quantified repeated-residue multiplicity
excess. One explicit version is:

```text
There exist integers N_k->infinity, rationals rho_k, real eps_k->0,
and fixed real s>0 and eta>0 such that

max_(0<=n<N_k) ||10^n*(pi-rho_k)||_(R/Z) <= eps_k/N_k,     (H1)

#{(i,j): 0<=i!=j<N_k,
          {10^i*rho_k}={10^j*rho_k}}
    >= (2*s+eta)*N_k.                                     (H2)
```

For sufficiently large `k`, `2*eps_k<=s`; every pair in (H2) would then be a
metric pair for the decimal orbit at radius `s/N_k`. Decimal-cylinder transfer
to T7 additionally requires boundary control. Neither (H1), (H2), nor that
boundary control is asserted for pi.

There are two cheap exact kill tests for a proposed approximant `rho=a/q` in
lowest terms. Write

```text
q=2^u*5^v*m, gcd(m,10)=1, e=max(u,v),
P=1 if m=1 and P=ord_m(10) otherwise.
```

For `i<j`, equality of the two rational residues is equivalent to

```text
q | a*10^i*(10^(j-i)-1).                                  (11.1)
```

Since `gcd(a,q)=1` and `10^(j-i)-1` is coprime to 10, (11.1) forces `i>=e`.
After that preperiod it is equivalent to `P|(j-i)` (vacuously so with `P=1`
when `m=1`). Thus there are no collisions involving a preperiod index. For a
prefix `0,...,N-1`, put `L=max(N-e,0)`. If `L=c*P+r`, `0<=r<P`, the complete
ordered off-diagonal collision count is

```text
P*c*(c-1)+2*c*r.                                          (11.2)
```

In particular, `L<=P` kills (H2) because there are no repeated tail residues.
Independently, the endpoint coordinate alone kills (H1) if, along the proposed
sequence,

```text
N_k*||10^(N_k-1)*(pi-rho_k)||_(R/Z)
```

does not tend to zero. Then the required uniform `o(1/N_k)` phase error is
absent.
These are tests of a conditional transfer proposal, not computations or claims
about pi.

## 12. Replay boundary and terminal classification

From a directory containing only the delivered files, run

```text
python3 verify_t99.py
sha256sum --check SHA256SUMS
```

The verifier checks the canonical and source hashes and locators, then performs
finite exact checks of orders, lifted valuations, triple multiplicities, exact
prefix counts, endpoint inequalities, tail bounds, the `b=2,N=16` mechanism
kill, and rational-period collision counts. Those computations are `sanity
checks` only. The universal proof sketch is Sections 4--9.

No source-coverage promotion or novelty claim is made. No statement about pi,
C1, or C2 follows.

Terminal outcome: rigorous family `proof sketch` for every admissible base.

Disposition: `hold as model`.
