# T164: effective return-separation certificate for primitive substitutions

Date: 2026-08-12 UTC.

Source statements in `SOURCE_PINS.md` are **literature-checked**. Sections
4-8 below are a **proof sketch**, not machine-checked. Section 9 and
`verify_t164.py` are an **experiment** using exact finite computation only.
Section 10 states an **unproved pi transfer** separately. No fixed-pi, A1, C1,
or C2 claim is made.

## 1. Canonical statement and sibling status

Original source URL: none; the local canonical question was formulated on
2026-07-22. `canonical_statement.txt` is byte-exact and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question counts ordered, diagonal-inclusive metric near returns
of `(10^i*pi) mod 1`. T164 instead studies exact equality of factors in a
named substitution fixed point. This is an A13/A14 sibling model. There is no
proved transfer in either direction.

## 2. Normalized input and ambiguities

The finite input is `(A,sigma,a)` where:

1. `A` is a nonempty finite alphabet.
2. `sigma:A* -> A*` is non-erasing and primitive: some `e>=1` has every
   letter of `A` in every `sigma^e(b)`.
3. `sigma(a)=a v` with `v` nonempty. The named one-sided fixed point is
   `u=sigma^omega(a)=u_0u_1...`.

All of these conditions are decidable by finite string and matrix operations.
Primitivity makes `sigma` growing and `u` uniformly recurrent (S1,
Definitions 1-3, displayed pp. 3-4).

Ambiguities fixed here:

1. Factors are indexed from zero and overlap is allowed.
2. The certificate is uniform over every `m>=1` and every two distinct starts
   in the infinite fixed point, not merely a tested prefix.
3. Distance means the difference of start indices, not disjoint-factor gap.
4. A counterexample includes `m`, both starts, and the common factor.
5. The finite procedure may have enormous runtime; "effective" means
   terminating on every normalized finite input.
6. Collision pairs are ordered and include all `M` diagonal pairs.
7. A periodic control is primitive as a substitution even though its fixed
   point is periodic; primitivity is not being confused with aperiodicity.

## 3. Exact return-separation definition

For `m>=1`, put

```text
B_m(i) = u_i u_(i+1) ... u_(i+m-1),
g_u(m) = min {j-i : 0<=i<j and B_m(i)=B_m(j)}.             (3.1)
```

Uniform recurrence ensures the set is nonempty. Equation (3.1) includes
overlaps: `j-i` may be smaller than `m`. For `c>0`, define

```text
SEP(u,c) : for every m>=1 and 0<=i<j,
           B_m(i)=B_m(j) implies j-i >= c*m.              (3.2)
```

Thus `SEP(u,c)` is exactly `g_u(m)>=c*m` for every `m>=1`.
S1 Section 2.3 defines a return word as the word between successive starts of
a prefix and S1 Proposition 6 proves the unique return-word coding. S2
Definition 2 and Proposition 5(4) put a lower bound on return lengths. T164's
definition covers all factors, not only prefixes, and the proof below handles
any equal pair directly.

## 4. Finite constants from the substitution

Everything in this section is computed by finite iteration.

1. Compute the least primitive exponent `e`.
2. For `n>=0`, set
   `S_n=max_b |sigma^n(b)|` and `I_n=min_b |sigma^n(b)|`.
3. Set

```text
Q = max(S_e, ceil(S_0/I_0),...,ceil(S_(e-1)/I_(e-1))).    (4.1)
```

For `n<e`, (4.1) gives `S_n<=Q I_n`. For `n=e+k`, every
`sigma^e(b)` contains every letter, so

```text
|sigma^(e+k)(b)| <= S_e max_x |sigma^k(x)|,
|sigma^(e+k)(d)| >= sum_x |sigma^k(x)| >= max_x |sigma^k(x)|.
```

Hence `S_n<=Q I_n` for every `n`. This makes S1 Lemma 13's `Q` explicit.

4. Compute the exact finite language `L_2(u)` by starting with all internal
   length-two factors of the images `sigma(b)` and repeatedly adding all
   length-two factors of `sigma(xy)` until the finite subset of `A^2`
   stabilizes.
5. Search for the least `t` such that every member of `L_2(u)` occurs in
   every `sigma^t(b)`. Primitivity and uniform recurrence guarantee such a
   `t`; direct iteration therefore terminates.
6. Put

```text
r = 2*S_t,       S = S_1,       N = 4*r*S*Q.              (4.2)
```

Every length-`r` factor contains a complete `sigma^t(b)` block and therefore
every member of `L_2(u)`. Thus successive starts of each length-two factor
are at distance at most `r`. In S1 Theorem 17's notation, this is a valid
choice of its recurrence constant `r`. The displayed proof of that theorem
then gives exactly `N=4 r S Q` and proves, when `u` is nonperiodic,

```text
x^N is a factor of u  iff  x is empty.                    (4.3)
```

## 5. Terminating certificate-or-counterexample procedure

The procedure uses S3 Section 6.4, Note 1: whether the D0L fixed point has
finite critical exponent is decidable.

**Input:** normalized `(A,sigma,a)` and a proposed positive rational `c=p/q`
in lowest terms. The finite branch may certify a different explicit `c_0`;
the infinite branch refutes the input proposal.

1. Run the bounded-critical-exponent decision procedure.
2. If it answers **finite**, compute (4.1)-(4.2) and return

```text
CERTIFICATE: c_0 = 1/(N-1).                               (5.1)
```

3. If it answers **infinite**, enumerate `k=0,1,2,...`; construct
   `sigma^k(a)`; enumerate every `m>=1` and pair of starts contained in that
   finite word; return the first exact equality with `q*(j-i)<p*m`.

Termination:

1. The decision in step 1 terminates by S3.
2. Every computation in step 2 ranges over finite alphabets and finite words;
   searches for `e` and `t` terminate by primitivity and uniform recurrence.
3. Infinite critical exponent means that for every integer `K` there is a
   nonempty word `x` with `x^K` a factor. Choose `K` with
   `1/(K-1)<p/q`. The two equal length-`(K-1)|x|` factors at consecutive
   starts of copies of `x` have distance `|x|`, so they violate the proposal.
   That finite witness occurs in some `sigma^k(a)`, hence exhaustive search
   finds it.

This is a total finite procedure. There is no remaining effectivity gap.
S3 warns that computing the exact critical exponent has extra difficulties;
the procedure deliberately does not require that stronger task.

## 6. Correctness of the certificate

Assume the finite branch. A uniformly recurrent periodic word has arbitrarily
large powers, so finite critical exponent implies `u` is nonperiodic and (4.3)
applies.

Suppose `B_m(i)=B_m(j)` and put `d=j-i>0`.

1. If `d>=m`, then `d>m/(N-1)`: (4.2) has `r>=2`, `S>=1`, `Q>=1`, hence
   `N>=8` and `N-1>1`.
2. If `d<m`, equality of the overlapping blocks says that the factor from
   start `i` through position `j+m-1`, of length `m+d`, has period `d`.
3. If `d<=m/(N-1)`, then `m+d>=Nd`. Its first `Nd` letters are `x^N`, where
   `x` is its first `d` letters, contradicting (4.3).

Consequently

```text
d > m/(N-1),
d >= Delta_N(m) := floor(m/(N-1))+1,                      (6.1)
g_u(m) >= Delta_N(m) > m/(N-1).
```

Thus (5.1) satisfies `SEP(u,c_0)`. This proof includes overlapping and
nonoverlapping equal factors and displays the only constant substitution,
`N=4 r S Q`.

## 7. Occupancy and ordered collision energy

For `M>=1`, consider starts `0,...,M-1`. Let

```text
C_w(m,M) = #{0<=i<M : B_m(i)=w},
Cmax(m,M) = max_w C_w(m,M),
E(m,M) = sum_w C_w(m,M)^2.                                (7.1)
```

`E` counts ordered equal-factor pairs and includes every diagonal. If the
starts carrying one `w` are `p_1<...<p_k`, (6.1) gives consecutive spacing at
least `Delta_N(m)`. Since `p_k<=M-1`,

```text
Cmax(m,M) <= floor((M-1)/Delta_N(m))+1,                   (7.2)
E(m,M) <= M*(floor((M-1)/Delta_N(m))+1).                  (7.3)
```

Indeed, `sum_w C_w=M` and `sum_w C_w^2<=Cmax sum_w C_w`.
The weaker real-constant display requested by the agenda is

```text
Cmax <= floor((M-1)/(c_0*m))+1,
E <= M*(floor((M-1)/(c_0*m))+1),                          (7.4)
```

while (7.2)-(7.3) are sharper because they retain integer strictness.

## 8. Explicit certified substitutions

### 8.1 Fibonacci fixed point

```text
sigma_F: 0->01, 1->0;       f=sigma_F^omega(0).
e=2; Q=3; L_2={00,01,10}; t=4; S_t=8; r=16; S=2.
N=4*16*2*3=384; c_F=1/383.
Delta_F(m)=floor(m/383)+1.
```

S3 Section 6.5.1 records `E(f)=2+tau<infinity`, so this is on the certificate
branch. For every `M,m>=1`,

```text
Cmax_F <= floor((M-1)/(floor(m/383)+1))+1,
E_F <= M*(floor((M-1)/(floor(m/383)+1))+1).                (8.1)
```

### 8.2 Thue-Morse fixed point

```text
sigma_T: 0->01, 1->10;      t=sigma_T^omega(0).
e=1; Q=2; L_2={00,01,10,11}; t=3; S_t=8; r=16; S=2.
N=4*16*2*2=256; c_T=1/255.
Delta_T(m)=floor(m/255)+1.
```

S3 Example 5.4 records `E(t)=2`, so this is on the certificate branch. For
every `M,m>=1`,

```text
Cmax_T <= floor((M-1)/(floor(m/255)+1))+1,
E_T <= M*(floor((M-1)/(floor(m/255)+1))+1).                (8.2)
```

These constants are intentionally conservative. Exact critical exponents give
better constants, but their computation is not needed for the general total
procedure.

## 9. Three declared finite checks

Label: **experiment**, exact finite validation only. Run from a directory
containing only the delivered artifacts:

```text
python3 verify_t164.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The script verifies the vendored canonical hash, recomputes `e,Q,L_2,t,r,S,N`,
and makes these three checks:

1. **Fibonacci:** on `M=4096` starts it searches `1<=m<=64`; the smallest
   observed ratio is `21/53`, witnessed at starts `34,55`. At `m=768`, the
   certificate gives `Delta=3`, occupancy at most `1366`, and energy at most
   `5,595,136`; exact observed occupancy is `8` and ordered diagonal-inclusive
   energy is `24,418`.
2. **Thue-Morse:** on the same starts and depths the smallest observed ratio
   is `1`; at `m=512`, `Delta=3`, occupancy at most `1366`, and energy at most
   `5,595,136`; exact observed occupancy is `6` and energy is `11,294`.
3. **Periodic control:** `sigma_P:0->01,1->01` is primitive and has fixed point
   `(01)^omega`. The proposed `c=1/10` fails exactly at `m=21`, starts `0,2`:
   both factors are `010101010101010101010`, while
   `2 < (1/10)*21=21/10`.

The first two computations validate arithmetic and examples only; their
universal certificates come from Sections 4-8. The third is an exact finite
counterexample to that proposed certificate.

## 10. Additional unproved pi-specific premise

To move this mechanism toward T7, one would additionally need the following
pi-specific symbolic-model premise, which is **unproved**:

> There exist a certified aperiodic primitive-substitution fixed point `u`, a
> constant `L>=1`, and maps from every length-`n` decimal factor occurring
> among starts `0,...,N-1` of the fixed decimal digit stream of `pi` to factors
> of `u` of length at least `n/L`, such that equality of decimal factors maps
> to equality of symbolic factors, while the distance between the two symbolic
> starts is at most `L` times the distance between their decimal starts,
> uniformly for the unbounded `(n,N)` family required by T7.

Under that premise, `c*(n/L) <= symbolic distance <= L*decimal distance`, so
equal decimal factors would start at distance at least `c*n/L^2`, and
(7.2)-(7.3) could bound T7's
ordered diagonal-inclusive cylinder collision energy. Nothing in S1-S3 or the
finite examples supplies this coding for pi. T107 would require still more:
an unproved quantitative bridge from this exact-equality coding to its
triangular Fourier/boundary premise. Therefore T164 makes no T7 or T107
conclusion and no fixed-pi, A1, C1, or C2 claim.

## 11. Classification

**VERDICT: DEVELOP.** The T162 order-sensitive discriminator becomes an
effective related-model certificate with explicit constants and a total
counterexample branch. Development should remain in symbolic models until a
genuinely pi-specific coding premise is found; finite resemblance is not such
a premise.
