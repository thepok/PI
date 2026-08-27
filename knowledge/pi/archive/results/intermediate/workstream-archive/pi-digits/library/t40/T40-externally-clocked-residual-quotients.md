# T40: Congruence-and-suffix quotients fail in the externally clocked residual system

Status: `proof sketch`. This is a rigorous prose argument, not a Lean
formalization. It uses the named machine-checked T37 and T39 interfaces, but
the new all-`M,r` theorem in this note has not itself been machine-checked.

## 1. Provenance, normalized target, and scope

- Canonical source: `knowledge/pi/statements/pi-digits.txt`.
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The canonical source is a human-authored
  local root recording Marcel's request of 2026-07-21.
- Machine-checked T37 interface:
  `TheoryLib.PiDigits.T37CrossBaseCarry`, staged as `CrossBaseCarry.lean`,
  SHA-256
  `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6`.
- Machine-checked T39 interface:
  `TheoryLib.PiDigits.T39BalancedCarryMyhillNerode`, staged as
  `BalancedCarryMyhillNerode.lean`, SHA-256
  `ca4a062d143829622001d92864c686d7c5a6fbaae1dd3997b33054753e806a35`.

The canonical question V1 asks whether every finite decimal word, including
words with leading zeroes, occurs contiguously in the decimal expansion of pi.
This note does not answer V1. It studies only one family of finite observation
codes for the balanced cross-base carry system underlying T37 and T39.

### Normalized quantifiers and ambiguities

1. `M` and `r` are arbitrary positive integers. The modulus is never zero,
   and the suffix has at least one digit.
2. The forbidden decimal word is the one-digit word `[2]`. Thus an already
   avoiding prefix remains avoiding exactly when every newly supplied decimal
   digit differs from `2`; no boundary matching longer than zero is needed.
3. Decimal words have fixed lengths and retain leading zeroes. The last `r`
   digits of a prefix with value `D` mean `D mod 10^r`, represented as an
   `r`-digit word padded on the left by zeroes.
4. The reduced carry means the signed T37 carry divided by
   `gcd(10^m,16^n)`. At a balanced level this gcd is proved below to be `2^m`.
   Congruence of signed carries is equality in `Z/MZ`, not a language-specific
   signed-remainder convention.
5. The external clock owns the current scale context and supplies each
   one-or-two-digit balanced schedule increment. The absolute level is not a
   component of persistent controller state. Clock inputs are not rejected by
   comparing them to a hidden level tag.
6. Reachability is not weakened: source states must be reachable in T39's
   exact balanced system. The distinguishing pair below is at one common
   level, so both runs receive literally the same actual balanced clock tail.
7. A "quotient candidate" below is an observation code. It is not assumed in
   advance that its transition is well-defined independently of omitted clock
   scales; language preservation is precisely what is tested.

## 2. Exact reduced coordinates from T37 and T39

Write

\[
 m_n=\operatorname{T39.decimalLevel}(n),\qquad
 \delta_n=m_{n+1}-m_n
     =\operatorname{T39.scheduleIncrement}(n).              \tag{1}
\]

The machine-checked T39 theorems `decimalLevel_lower`,
`decimalLevel_upper`, and `scheduleIncrement_one_or_two` give

\[
 10^{m_n}\le 16^n<10^{m_n+1},\qquad \delta_n\in\{1,2\}.     \tag{2}
\]

T39's theorem `decimalLevel_succ` says
`m_(n+1)=m_n+delta_n`, and `decimalLevel_add_eq` gives its finite
telescoping version.

Fix a T39 balanced state at hexadecimal length `n` and decimal length
`m=m_n`, with numeric prefix values `A,D`. T37 defines

\[
 \kappa=10^mA-16^nD.                                       \tag{3}
\]

Because `10^m <= 16^n=2^(4n)`, necessarily `m<=4n`. Factoring the two
powers gives

\[
 \gcd(10^m,16^n)
 =\gcd(2^m5^m,2^{4n})=2^m.                                 \tag{4}
\]

Define the external scale context and the persistent reduced carry by

\[
 a=5^m,\qquad b=2^{4n-m},\qquad
 K=\frac{\kappa}{2^m}=aA-bD.                               \tag{5}
\]

Dividing (2) by `2^m` also gives

\[
                         a\le b<10a.                        \tag{6}
\]

The machine-checked theorem `T37.cylinders_overlap_iff_carry_bounds`
states that the two half-open prefix cylinders intersect exactly when

\[
                       -10^m<\kappa<16^n.
\]

After division by `2^m`, its exact residual form is

\[
                         \boxed{-a<K<b}.                    \tag{7}
\]

No approximation has entered (3)-(7).

## 3. The externally clocked residual transducer

The persistent residual state is

\[
                         p=(K,z),                            \tag{8}
\]

where `K in Z` is the reduced carry and `z in {0,...,10^r-1}` is the
last-`r`-digit residue. The pair `(a,b)` is external clock context, not
persistent controller memory. Initially it is obtained from the source
state by (5).

At one step the clock supplies `s in {1,2}`. The payload supplies one
hexadecimal digit `h in {0,...,15}` and a fixed-length `s`-digit decimal
block `E`, with numeric value `e`. Leading zeroes in `E` are retained. The
clock and persistent coordinates update by

\[
\begin{aligned}
 a'&=5^s a,\\
 b'&=2^{4-s}b,\\
 K'&=16\,5^sK+a'h-b'e,\\
 z'&=(10^s z+e)\bmod 10^r.                                 \tag{9}
\end{aligned}
\]

The step is retained exactly when every digit of `E` differs from `2` and

\[
                         -a'<K'<b'.                         \tag{10}
\]

### Match with T37's append transition

Appending one hexadecimal digit and `s` decimal digits changes prefix values
to

\[
 A'=16A+h,\qquad D'=10^sD+e.                               \tag{11}
\]

Specializing the machine-checked `T37.carry_append` to one hexadecimal
digit gives

\[
 \kappa'=16\,10^s\kappa+10^{m+s}h-16^{n+1}e.               \tag{12}
\]

Since the new common power of two is `2^(m+s)`, division of (12) by that
power is exactly the third equation of (9):

\[
 \frac{\kappa'}{2^{m+s}}
 =16\,5^sK+5^{m+s}h-2^{4(n+1)-(m+s)}e
 =16\,5^sK+a'h-b'e.                                        \tag{13}
\]

This is again the full gcd reduction: from `m<=4n` and `s<=2` one has
`m+s<=4n+2<=4(n+1)`, hence

\[
 \gcd(10^{m+s},16^{n+1})
 =\gcd(2^{m+s}5^{m+s},2^{4(n+1)})=2^{m+s}.
\]

Dividing T37's new carry bounds by `2^(m+s)` gives (10). Equation (11)
gives the suffix update in (9). Thus (9)-(10) are not a new approximate
model: they are the exact T37 transition and compatibility test in gcd-reduced
coordinates.

### Match with T39 and removal of its separator

For a run beginning at T39 level `n`, the actual external clock supplies

\[
                         s_i=\delta_{n+i}.                  \tag{14}
\]

T39's `decimalLevel_succ` shows that these are exactly the block lengths in
its `RetainedStep`. The difference is architectural: T39 stores `level` and
rejects a symbol when its decimal length differs from
`scheduleIncrement level`; here the clock supplies `s_i`, the residual
transition uses it, and no hidden level-comparison test occurs. In particular,
an all-zero payload has `K'=0` from every zero-carry state for every supplied
`s`; T39's different-schedule-tail separator is unavailable.

A finite clocked continuation is a sequence of packets

\[
 ((s_0,h_0,E_0),\ldots,(s_{t-1},h_{t-1},E_{t-1}))           \tag{15}
\]

with `|E_i|=s_i`. It is accepted from an external context `(a,b)` and
persistent state `(K,z)` when every iterated step (9) satisfies (10) and every
`E_i` avoids `2`. The externally clocked continuation language is the set of
accepted packets; denote it by `L_(a,b)(K,z)`. For actual balanced
continuations one uses (14). If `q` is a concrete T39 state, write `a(q),b(q),
K(q),z_r(q)` for its induced coordinates and abbreviate

\[
 L_{\mathrm{ext}}(q)=L_{(a(q),b(q))}(K(q),z_r(q)).
\]

The quotient candidate tested in this note is

\[
 Q_{M,r}(K,z)=\bigl(K\bmod M,z\bigr).                       \tag{16}
\]

For a concrete T39 state, the notation `Q_(M,r)(q)` means
`Q_(M,r)(K(q),z_r(q))`; the external context is not part of this code.

The clock context `(a,b)` is deliberately absent from (16). Formula (9)
already warns that this omission need not be a transition congruence: the
terms `a'h-b'e` depend on the external scales. The theorem below proves the
stronger behavioral failure directly.

## 4. A reachable same-code family for every positive `M,r`

Fix arbitrary positive `M,r`, put

\[
 N=M+r,\qquad n=2N,\qquad m=m_n,\qquad
 a=5^m,\qquad b=2^{4n-m}.                                  \tag{17}
\]

Since `10^n<=16^n`, (2) implies `m>=n=2N`. Therefore

\[
                     a=5^m\ge 5^{2N}=25^N>10^N.             \tag{18}
\]

Let `U_M` be the set of all fixed-length `M`-digit words over `{0,1}`.
For `u in U_M`, let `[u]_10` be its decimal numeric value and define

\[
                         D_u=10^r[u]_{10}.                  \tag{19}
\]

As a fixed-length `m`-digit decimal word, `D_u` is

\[
                      0^{m-N}\,u\,0^r.                     \tag{20}
\]

It avoids `2`, ends in the common suffix `0^r`, and (18) gives

\[
                         0\le D_u<10^N<a.                   \tag{21}
\]

Define

\[
 A_u=\left\lfloor\frac{bD_u}{a}\right\rfloor,
 \qquad K_u=aA_u-bD_u.                                     \tag{22}
\]

The floor inequalities and (21) give

\[
                         -a<K_u\le0<b.                      \tag{23}
\]

Also `A_u<b<=16^n`, so `A_u` is a valid `n`-digit hexadecimal prefix.
By (7), (23) proves exact cylinder compatibility. Let `q_u` denote the
corresponding T39 state, using the fixed-length hexadecimal representation of
`A_u` and the decimal word (20).

### Lemma 1: every `q_u` is T39-reachable

Put

\[
                         x_u=\frac{D_u}{10^m}.              \tag{24}
\]

For every `0<=i<=n`, take the fixed-length prefixes with values

\[
 A_i=\lfloor16^i x_u\rfloor,
 \qquad D_i=\lfloor10^{m_i}x_u\rfloor.                     \tag{25}
\]

Let `H_i` be the unique length-`i` hexadecimal word (left-padded by zeroes)
with value `A_i`, and let `V_i` be the unique length-`m_i` decimal word with
value `D_i`. These words are valid because `0<=x_u<1` gives
`A_i<16^i` and `D_i<10^(m_i)`. At `i=0`, both words are empty, so their state
is exactly T39's `initialState` (in particular `m_0=0`, from (2)).

Both associated half-open cylinders contain `x_u`. The terminating decimal
expansion of `x_u` is the word (20) followed by zeroes, so every decimal
prefix in (25) uses only `0` and `1` and avoids `2`. Consecutive hexadecimal
prefixes satisfy `A_(i+1)=16A_i+h_i` for the unique next digit `h_i<16`.
Consecutive decimal prefixes satisfy
`D_(i+1)=10^(delta_i)D_i+e_i`, where `e_i` is the value of the next
fixed-length `delta_i`-digit block; T39's `decimalLevel_succ` supplies that
length. Package `h_i` and this block as T39's `Symbol`. The target words are
exactly `H_(i+1),V_(i+1)`, and their cylinders contain `x_u`, so each target
is `Balanced` and every step is a T39 `RetainedStep`. Induction on `i` shows
that T39's `run` on this symbol list ends at the state represented by
`H_i,V_i`.

At `i=n`,

\[
 \lfloor16^n x_u\rfloor
 =\left\lfloor\frac{2^{4n}D_u}{2^m5^m}\right\rfloor
 =\left\lfloor\frac{bD_u}{a}\right\rfloor=A_u,             \tag{26}
\]

and `floor(10^m x_u)=D_u`. Thus the path ends at `q_u`, proving
reachability. Endpoint conventions cause no gap: a half-open cylinder
contains its left endpoint, and the floor-selected cylinder contains `x_u`.

### Lemma 2: two distinct candidates have the same `Q_(M,r)` code

There are `2^M` words in `U_M`, and `2^M>M` for every positive `M`.
There are only `M` residues modulo `M`, so two distinct words `u,v` satisfy

\[
                         K_u\equiv K_v\pmod M.              \tag{27}
\]

For a fully determined symbolic choice, take the lexicographically first pair
`u<v` satisfying (27). This is a finite definition, not an empirical search
claim. Equations (19)-(20) give

\[
                     D_u\equiv D_v\equiv0\pmod{10^r}.       \tag{28}
\]

Thus (27)-(28) say exactly

\[
                         Q_{M,r}(q_u)=Q_{M,r}(q_v).          \tag{29}
\]

Their exact reduced carries are nevertheless different. If `K_u=K_v`, then
(22) gives

\[
                         a(A_u-A_v)=b(D_u-D_v).              \tag{30}
\]

Here `a` is odd and `b` is a power of two, so `gcd(a,b)=1`. Equation (30)
would imply `a | (D_u-D_v)`. But both values lie in `[0,a)` by (21), so this
would force `D_u=D_v`, and then the injectivity of fixed-length decimal
encoding would force `u=v`, a contradiction. Therefore

\[
                              K_u\ne K_v.                   \tag{31}
\]

## 5. An explicit common continuation accepted from exactly one

Retain the lexicographically selected pair from Lemma 2 and orient it so that
the continuation is built from `q_u`. Put

\[
                              t=a=5^m.                      \tag{32}
\]

For `0<=i<t`, let the external clock supply the actual common balanced
increment

\[
                              s_i=\delta_{n+i},              \tag{33}
\]

let the decimal payload be the all-zero block

\[
                              E_i=0^{s_i},                   \tag{34}
\]

and let the hexadecimal payload be the next base-16 digit of `x_u`:

\[
 h_i=\lfloor16^{n+i+1}x_u\rfloor
       -16\lfloor16^{n+i}x_u\rfloor.                        \tag{35}
\]

The floor inequalities show `0<=h_i<16`, so (35) is a hexadecimal digit.
Equations (32)-(35) define a finite continuation `W_(M,r)` explicitly from
`M,r` and the lexicographically chosen collision.

### Lemma 3: `W_(M,r)` is accepted from `q_u`

After any number `j<=t` of these steps, the hexadecimal prefix is
`floor(16^(n+j)x_u)`. If

\[
 S_j=\sum_{i=0}^{j-1}s_i=m_{n+j}-m,                         \tag{36}
\]

where the equality is T39's `decimalLevel_add_eq`, then the decimal prefix is
`D_u 10^(S_j)`. Hence its cylinder has left endpoint

\[
 \frac{D_u10^{S_j}}{10^{m+S_j}}=\frac{D_u}{10^m}=x_u.       \tag{37}
\]

Both refined cylinders therefore contain `x_u` at every step. Every appended
decimal digit is zero, so avoidance also persists. By (7), equivalently by
the exact residual test (10), every transition is retained. Thus

\[
                         W_{M,r}\in L_{\mathrm{ext}}(q_u).  \tag{38}
\]

### Lemma 4: `W_(M,r)` is rejected from `q_v`

Both source states are at the same level `n` with the same external context
`(a,b)`. They receive the same clock inputs and the same payloads. Consequently
the affine input terms in (9) cancel when their reduced carries are
subtracted. If `Delta_j` is their reduced-carry difference after `j` formal
updates, then

\[
 \Delta_{j+1}=16\,5^{s_j}\Delta_j.
\]

At the final step, with `S=S_t`, this gives the exact identity

\[
              |\Delta_t|=16^t5^S|K_u-K_v|.                 \tag{39}
\]

The final external scales are

\[
 a_t=5^{m+S}=a5^S,
 \qquad b_t=2^{4(n+t)-(m+S)}.                               \tag{40}
\]

Suppose for contradiction that `W_(M,r)` were accepted from `q_v` as well.
Then both final carries would lie in the interval `(-a_t,b_t)`, so

\[
                         |\Delta_t|<a_t+b_t.                \tag{41}
\]

The clock inputs are the actual balanced increments, so
`m+S=m_(n+t)`. The upper balanced bound in (2), divided by `2^(m+S)`, gives

\[
                         b_t<10a_t.                         \tag{42}
\]

Equations (41)-(42) imply `|Delta_t|<11a_t`. But (31), (39), and (40)
give

\[
 \frac{|\Delta_t|}{a_t}
 =\frac{16^t|K_u-K_v|}{a}
 \ge\frac{16^t}{a}
 =\frac{16^a}{a}>11.                                       \tag{43}
\]

The last inequality is elementary for every positive integer `a`. The base
case is `16>11`. If `16^a>11a` and `a>=1`, then

\[
 16^{a+1}>176a\ge 11(a+1),
\]

which proves `16^a>11a` by induction. Equations (41)-(43) contradict one
another. Therefore the
continuation must fail the compatibility test from `q_v` at or before its
last step. Its decimal payload contains no `2`, and the two runs share the
same balanced clock, so the failure is a genuine carry/cylinder separation,
not a suffix or schedule-tail mismatch. Hence

\[
                         W_{M,r}\notin L_{\mathrm{ext}}(q_v).\tag{44}
\]

Equations (38) and (44) provide the requested explicit distinguishing
continuation.

## 6. Theorem and exact conclusion

**Theorem (all-`M,r` failure of the congruence-plus-suffix architecture).**
For every pair of positive integers `M,r`, the construction in Sections 4-5
gives two T39-reachable digit-`2`-avoiding states `q_u,q_v` at the same
balanced level and with the same external clock context such that

\[
 Q_{M,r}(q_u)=Q_{M,r}(q_v)
 \quad\text{but}\quad
 L_{\mathrm{ext}}(q_u)\ne L_{\mathrm{ext}}(q_v).
\]

The explicit word `W_(M,r)` is accepted from `q_u` and rejected from `q_v`.
Therefore no positive `M,r` makes the code consisting only of reduced carry
modulo `M` and the last `r` decimal digits exactly language-preserving for this
externally clocked residual system.

This theorem is stronger than merely observing that the quotient update is
not syntactically autonomous: it exhibits reachable equal-code states with
different behavior. It is also independent of T39's schedule-tail argument,
because each pair occurs at one common level and receives one common clock
sequence.

## 7. Evidence and scope exclusions

No finite minimization table, bounded state enumeration, or decimal/hexadecimal
search was used as evidence for the universal theorem. The finite
lexicographic choice in Lemma 2 is part of an exact pigeonhole construction;
it is not an experimentally observed collision. No computation is presented
in this artifact.

The result concerns only the quotient family `Q_(M,r)` in (16). In particular:

1. It does not rule out arbitrary finite quotients, including quotients that
   retain residues of the external scales or use a different invariant.
2. It proves nothing about the hexadecimal or decimal digits of pi and does
   not assert that pi follows any branch of this residual transducer.
3. It neither proves nor supplies evidence for `T37.JMix Real.pi`; that
   hypothesis remains unproved.
4. It proves neither canonical V1 nor sibling V3 from the immutable source.
5. It makes no claim about literature novelty. T38 is an unverified note and
   is not used as a discharged premise; all dependencies used here are the
   displayed definitions or the named machine-checked T37/T39 declarations.

The honest status of the new universal conclusion is `proof sketch` pending
independent mathematical review or formalization.
