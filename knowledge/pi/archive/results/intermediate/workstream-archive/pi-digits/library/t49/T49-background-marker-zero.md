# T49: a nonzero background-marker family for forbidden digit 0

Claim status: `proof sketch` (rigorous prose, not machine-checked).

## 1. Provenance

- Canonical statement: `knowledge/pi/statements/pi-digits.txt`.
- Canonical statement SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The source is a human-authored local
  root recording Marcel's request of 2026-07-21.
- Hash checked: 2026-08-03.

The canonical question asks whether every finite decimal word occurs
contiguously in the decimal expansion of `Real.pi`. That question is open.
This note does not address it. It studies only the abstract externally
clocked residual carry system in the kernel-checked T37/T43/T46 interfaces,
with the one-letter decimal word `[0]` forbidden.

## 2. Exact and normalized target

For distinct digits `a,b` in `{1,...,9}`, a length `L >= 1`, and
`0 <= j < L`, define

\[
 B(b,L)=b\frac{10^L-1}{9},\qquad
 D(a,b,L,j)=B(b,L)+(a-b)10^j.                 \tag{2.1}
\]

The position `j` is counted from the right, starting at `0`. Thus (2.1) is
the value of the length-`L` decimal word having digit `b` everywhere except
for digit `a` in position `j`. The displayed expression is interpreted as an
integer identity if `a<b`; its value is nevertheless a natural number. This
note uses `a=2>b=1`, so no signed-subtraction convention is needed in the
construction.

The outcome proved below is the constructive alternative with the fixed pair

\[
                         \boxed{(a,b)=(2,1)}. \tag{2.2}
\]

Precisely, for every `K : Nat`, including `K=0`, the note defines:

1. one external hexadecimal level `N_K` and its decimal length `L_K`;
2. `K+1` concrete states `q_(K,j)`, indexed by `j : Fin (K+1)`, whose
   decimal prefixes have values `D(2,1,L_K,j)`;
3. their T46 persistent residuals `rho_(K,j)` at scale `r=1`; and
4. for every oriented index `u`, one explicit finite continuation `W_(K,u)`.

It proves that every `rho_(K,j)` is induced by a digit-0 reachable concrete
state at the same level, that the residual map is injective, and that for
every `u != v`, the same continuation `W_(K,u)` follows the shared external
schedule, is accepted from `rho_(K,u)`, and is rejected from `rho_(K,v)`.
Consequently the common level contains exactly `K+1>K` pairwise
right-language-inequivalent reachable residuals.

### Quantifier and scope ambiguities resolved

1. The pair `(a,b)=(2,1)` is chosen once and is independent of `K`, `j`, and
   the continuation.
2. `K` ranges over all natural numbers. For `K=0`, reachability is
   nonvacuous and pairwise separation is vacuous.
3. The class condition applies to source decimal prefixes. The separating
   continuations need only be legal for forbidden digit `0`; here their
   appended decimal digits are explicitly all `1`.
4. At external hexadecimal level `N`, the class length is not arbitrary: it
   is `L=decimalLevel(N)`, as required by T46's balanced-state definition.
5. Reachability means `T46.ReachableAtFor (0 : Fin 10) N q`.
6. Persistent reachability means `T46.PersistentReachableAt
   (0 : Fin 10) N rho`, with `rho=T41.residualOf 1 q` as it occurs in T46.
7. Right languages are literal T46 finite-continuation languages at one
   shared level and one shared future schedule. The external level and
   schedule are not persistent-state fields.
8. A separator is oriented: `W_(K,u)` is accepted from `u` and rejected from
   every distinct `v`. This is stronger than merely asserting unequal sets.

## 3. Imported kernel-checked interfaces

Only the following kernel-checked interfaces are used as imported premises.
Their hashes were checked in the supplied knowledge library.

| Item | Role used here | SHA-256 |
|---|---|---|
| T37 | numeric words, prefix cylinders, exact carry, and overlap bounds | `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6` |
| T43 | common-level external-clock continuation-language semantics | `b3658d1fb1f63e58f76d968658f57a9cc380fa3a830a4cbab9e8e7b0293298be` |
| T46 | digit-parameterized balance, reachability, residual acceptance, and final carry bounds | `b39e36c975ca9631531222da58d5d448e5a4641820e3d35428ebf2a8c22aad05` |

T43 and T46 publicly name the underlying clock context, concrete state,
packet, and residual types. This note uses those names only through the
displayed T43/T46 definitions. No claim from an unverified T45, T47, or other
prose note is a premise. No theorem from T48 is imported. Algebraic facts not
already stated by T37/T43/T46 are proved below.

## 4. Exact interface crosswalk

Put

\[
 m_n=\operatorname{decimalLevel}(n),\qquad
 \delta_n=m_{n+1}-m_n\in\{1,2\}.             \tag{4.1}
\]

The balanced context at level `n` has scales

\[
 \alpha_n=5^{m_n},\qquad
 \beta_n=2^{4n-m_n}.                          \tag{4.2}
\]

For hexadecimal and decimal prefix values `A,D`, its reduced carry is

\[
 c_n(A,D)=\alpha_n A-\beta_n D.               \tag{4.3}
\]

T37's carry is `2^(m_n) c_n(A,D)`. Its overlap criterion, in the reduced
coordinates used by T46, is

\[
 \operatorname{prefixCylinder}(16,n,A)\cap
 \operatorname{prefixCylinder}(10,m_n,D)\ne\varnothing
 \quad\Longleftrightarrow\quad
 -\alpha_n<c_n(A,D)<\beta_n.                  \tag{4.4}
\]

For forbidden digit `0`, the exact T46 definitions used here are:

\[
 \operatorname{AvoidsDigit}(0,w)\iff 0\notin w,               \tag{4.5}
\]

`BalancedFor 0 q`, consisting of the two exact length conditions, two valid
prefix conditions, (4.5), and the cylinder overlap in (4.4), and

\[
\begin{aligned}
 \operatorname{ReachableAtFor}(0,N,q)
   &\iff \operatorname{ReachableFor}(0,q)\ \wedge\ q.level=N,\\
 \operatorname{PersistentReachableAt}(0,N,\rho)
   &\iff \exists q,\ \operatorname{ReachableAtFor}(0,N,q)\ \wedge
      \operatorname{residualOf}(1,q)=\rho.                    \tag{4.6}
\end{aligned}
\]

For a packet `p` of width `s`, hexadecimal value `h`, and decimal-block
value `e`, T46 retains it exactly when `s` is `1` or `2`, its decimal list
avoids `0`, and the next carry lies strictly between the next context bounds.
The carry component changes by

\[
 c'=(16\,5^s)c+\alpha' h-\beta'e.              \tag{4.7}
\]

The T46 predicates relevant to right languages are

\[
\begin{aligned}
 \operatorname{TailLegal}(N,[])&:=\mathrm{True},\\
 \operatorname{TailLegal}(N,p::w)&:=
   (p.width=\delta_N)\ \wedge\operatorname{TailLegal}(N+1,w), \tag{4.8}\\
 \mathcal L_{0,N}(\rho)&=
 \{w:\operatorname{TailLegal}(N,w)\ \wedge
   \operatorname{AcceptedFor}(0,\operatorname{balancedContext}(N),1,\rho,w)\}.
                                                               \tag{4.9}
\end{aligned}
\]

T46's `RightLanguageEquivalentAt` is equality of the two sets in (4.9).
These are the definitions against which every assertion below is checked.

## 5. The source family

Fix `K : Nat` and define

\[
 N=N_K=K+1,\qquad L=L_K=m_N.                  \tag{5.1}
\]

Because `10^N <= 16^N`, the definition of `m_N` gives

\[
                         L\ge N=K+1.           \tag{5.2}
\]

For `j : Fin (K+1)`, set

\[
 D_j=B(1,L)+10^j=\frac{10^L-1}{9}+10^j.       \tag{5.3}
\]

By `j<=K<L`, the length-`L` decimal word of `D_j` is

\[
             1^{L-j-1}\,2\,1^j.              \tag{5.4}
\]

In particular `0<D_j<10^L`, the word has exactly length `L`, and it and all
its prefixes avoid `0`.

The hexadecimal prefix is selected using the nonterminating all-ones tail,
not the lower decimal endpoint. Define

\[
 P_j=9D_j+1,\quad Q=9\,10^L,\quad
 x_j=\frac{P_j}{Q}=\frac{D_j+1/9}{10^L},\quad
 A_j=\left\lfloor16^N x_j\right\rfloor.       \tag{5.5}
\]

Thus the decimal expansion represented by `x_j` begins with (5.4) and then
has only digits `1`. Since

\[
 \frac{D_j}{10^L}<x_j<\frac{D_j+1}{10^L}<1,   \tag{5.6}
\]

we have `0<=A_j<16^N` and `x_j` is in the decimal prefix cylinder of `D_j`.
It is also strictly inside its hexadecimal prefix cylinder. Indeed,
`P_j=9D_j+1` is congruent to `1` modulo `3`, whereas `Q` is divisible by
`3`; hence `Q` cannot divide `16^N P_j`. Therefore `16^N x_j` is not an
integer, and

\[
       \frac{A_j}{16^N}<x_j<\frac{A_j+1}{16^N}.                \tag{5.7}
\]

In the exact concrete-state type occurring in T46, define

\[
\begin{aligned}
 q_j.level&=N,\\
 q_j.hexPrefix&=\operatorname{fixedWord}(16,N,A_j),\\
 q_j.decimalPrefix&=\operatorname{fixedWord}(10,L,D_j).
                                                               \tag{5.8}
\end{aligned}
\]

Here `fixedWord` is the fixed-width constructor named by T46's public
rational-state and reachability lemmas. Define

\[
             \rho_j=\operatorname{residualOf}(1,q_j).         \tag{5.9}
\]

By (4.3), the reduced-carry component of `rho_j` is

\[
                         c_j=\alpha_NA_j-\beta_ND_j.           \tag{5.10}
\]

## 6. Common-level reachability

**Lemma 6.1.** For every `j : Fin (K+1)`,

\[
 \operatorname{ReachableAtFor}(0,N,q_j)
 \quad\text{and}\quad
 \operatorname{PersistentReachableAt}(0,N,\rho_j).            \tag{6.1}
\]

**Proof.** We verify the public T46 criterion
`reachableFor_of_all_prefixes_balanced`.

1. The fixed-width words have lengths `N` and `m_N=L`, and their values are
   below `16^N` and `10^L`, by (5.3)-(5.7). Hence both exact length and valid
   prefix conditions hold.
2. At every scheduled level `i<=N`, take the first `i` hexadecimal digits and
   first `m_i` decimal digits. A prefix of a valid fixed-width word is valid.
3. Every such decimal prefix is a prefix of (5.4), so it avoids digit `0`.
4. The same point `x_j` lies in both prefix cylinders at every `i<=N`.
   This follows from (5.6)-(5.7): membership in a fixed-base cylinder implies
   membership in every ancestor cylinder obtained by deleting trailing
   digits. Thus the final overlap and every scheduled-prefix overlap hold.

Every scheduled prefix is therefore `T46.BalancedFor 0`. The cited T46
criterion slices the endpoint into `N` retained steps from the empty state,
proving `ReachableFor 0 q_j`. Its level is definitionally `N`, which gives
the first assertion in (6.1). The second follows from (5.9) and the exact
existential definition (4.6). `QED`

This is a symbolic all-`K` reachability proof. No finite state search is used.

## 7. Carry and residual injectivity

**Lemma 7.1.** The map `j |-> c_j` is injective on `Fin (K+1)`.

**Proof.** The two context scales in (4.2) are coprime because one is a power
of `5` and the other is a power of `2`. Suppose `c_u=c_v`. Reducing (5.10)
modulo `alpha_N=5^L` gives

\[
 \beta_ND_u\equiv\beta_ND_v\pmod {5^L}.
\]

The power of `2` is invertible modulo `5^L`, so

\[
                         5^L\mid(D_u-D_v).     \tag{7.1}
\]

Assume without loss of generality that `u>v`. The background cancels, giving

\[
 D_u-D_v=10^u-10^v=10^v(10^{u-v}-1).          \tag{7.2}
\]

After removing `5^v`, the right side is
`2^v(10^(u-v)-1)`, which is not divisible by `5` because the second factor is
`-1` modulo `5`. Its exact `5`-adic valuation is therefore `v`. But
`v<=K<L`, so (7.1) is impossible. Hence `u=v`. `QED`

Since reduced carry is a field of the persistent residual, Lemma 7.1 also
proves that `j |-> rho_j` is injective. This explicitly discharges the second
possible failure point, carry injectivity.

## 8. Explicit zero-free endpoint continuations

The standard rational extension `D_j*10^S` appends zeroes. It is therefore
illegal for forbidden digit `0` and cannot be used here. We replace it by an
all-ones extension and prove that, after an explicit number of clock steps,
it has the required source prefix.

Put

\[
 t=\alpha_N=5^L>0,\qquad
 S=m_{N+t}-m_N=\sum_{i=0}^{t-1}\delta_{N+i}.    \tag{8.1}
\]

Every schedule increment is at least `1`, so `S>=t`. Also `L>=N>=1` and
`5^L>=5^N>=2N`. The last inequality follows by induction from `5>=2`:
if `5^n>=2n` for `n>=1`, then `5^(n+1)>=10n>=2(n+1)`. Hence

\[
 10^S\ge10^t\ge10^{2N}=100^N>16^N.            \tag{8.2}
\]

For an oriented index `u`, define the extended decimal value

\[
 E_u=D_u10^S+B(1,S)
    =D_u10^S+\frac{10^S-1}{9}.                 \tag{8.3}
\]

Its length-`m_(N+t)=L+S` decimal word is exactly (5.4) followed by `S`
copies of digit `1`. In particular it contains no zero. Let

\[
 y_u=\frac{E_u}{10^{L+S}}.
\]

Equations (5.5) and (8.3) give the exact approximation

\[
 x_u-y_u=\frac{1}{9\,10^{L+S}}.                \tag{8.4}
\]

To prove that `y_u` has hexadecimal prefix `A_u`, let

\[
 r_u=16^NP_u-A_uQ.
\]

The nonintegrality argument before (5.7) gives `r_u>=1`, and therefore

\[
 x_u-\frac{A_u}{16^N}
   =\frac{r_u}{Q16^N}
   \ge\frac1{9\,10^L16^N}.                    \tag{8.5}
\]

By (8.2), the error in (8.4) is strictly smaller than the last expression in
(8.5). Thus

\[
 \frac{A_u}{16^N}<y_u<x_u<\frac{A_u+1}{16^N}. \tag{8.6}
\]

Define the level-`N+t` endpoint explicitly by

\[
\begin{aligned}
 A'_u&=\left\lfloor16^{N+t}y_u\right\rfloor,\\
 q'_u.level&=N+t,\\
 q'_u.hexPrefix&=\operatorname{fixedWord}(16,N+t,A'_u),\\
 q'_u.decimalPrefix&=
   \operatorname{fixedWord}(10,L+S,E_u).
                                                               \tag{8.7}
\end{aligned}
\]

The first `N` hexadecimal digits of `A'_u` have value

\[
 \left\lfloor\frac{A'_u}{16^t}\right\rfloor
 =\left\lfloor16^Ny_u\right\rfloor=A_u,       \tag{8.8}
\]

where the first equality is the elementary floor-of-a-floor identity and the
second is (8.6). The first `L` decimal digits of `E_u` have value
`floor(E_u/10^S)=D_u`. Consequently

\[
              \operatorname{prefixState}(q'_u,N)=q_u.         \tag{8.9}
\]

Now define the separator completely explicitly:

\[
 W_{K,u}=\operatorname{packetsOfSymbols}
   (\operatorname{endpointContinuation}(q'_u,N,t)).            \tag{8.10}
\]

Here `endpointContinuation` and `packetsOfSymbols` are the underlying names
appearing in T46's public `legal_endpointContinuationFor` and
`tailLegal_packetsOfSymbols_of_legalFor` interfaces. The call in (8.10)
includes the exact word-length proofs and the equality `N+t=q'_u.level`.
Equivalently, its
`k`th symbol, for `0<=k<t`, consists of:

1. hexadecimal digit number `N+k` of the fixed-width word for `A'_u`; and
2. the next `delta_(N+k)` decimal digits of (8.3), all equal to `1`.

Thus (8.10) is a finite, explicit list determined by `K` and `u`; it is not an
existentially selected continuation.

**Lemma 8.1.** `W_(K,u)` is tail-legal and accepted from `rho_u` in the
digit-0 system.

**Proof.** Every scheduled prefix of `q'_u` has the represented rational
point `y_u` in both parent cylinders, has valid fixed-width prefixes, and has
a decimal prefix containing only `1` and `2`. Hence every such prefix is
`T46.BalancedFor 0`, by the same direct six-conjunct check as in Lemma 6.1.
T46's `legal_endpointContinuationFor`, applied from level `N` and using
(8.9), proves that the concrete symbols in (8.10) form a digit-0 legal path
from `q_u`. T46's
`tailLegal_packetsOfSymbols_of_legalFor` gives

\[
                 \operatorname{TailLegal}(N,W_{K,u}).          \tag{8.11}
\]

T46's `acceptedFor_packetsOfSymbols_of_legalFor` gives

\[
 \operatorname{AcceptedFor}
   (0,\operatorname{balancedContext}(N),1,\rho_u,W_{K,u}).     \tag{8.12}
\]

The continuation has length `t>0`, and every appended decimal digit is the
legal nonzero digit `1`. `QED`

## 9. Pairwise continuation separation

**Lemma 9.1.** If `u!=v`, then `W_(K,u)` is rejected from `rho_v`.

**Proof.** Suppose instead that it were accepted. Write `w=W_(K,u)`, let
`c_u^f,c_v^f` be the two final reduced carries after running the same `w`,
and let `alpha_f,beta_f` be the final context scales.

Tail legality and `|w|=t` imply by induction on (4.8) that the final context
is `balancedContext(N+t)`. At every balanced level,

\[
                         \beta_f<10\alpha_f,                   \tag{9.1}
\]

because `16^(N+t)<10^(m_(N+t)+1)` and cancellation of the common factor
`2^(m_(N+t))` gives exactly (9.1).

By (8.10), `|w|=t>0`, so `w` is nonempty. The oriented acceptance (8.12),
the assumed acceptance from `v`, and T46's `acceptedFor_final_bounds` give

\[
 -\alpha_f<c_u^f,c_v^f<\beta_f.
\]

Together with (9.1), this implies

\[
                         |c_u^f-c_v^f|<11\alpha_f.             \tag{9.2}
\]

Subtracting two copies of the recurrence (4.7) cancels every packet-dependent
additive term. Induction over `w` therefore gives

\[
 c_u^f-c_v^f=M_w(c_u-c_v),\qquad
 M_w=16^{|w|}F_w,\qquad
 F_w=\prod_{p\in w}5^{p.width}>0.              \tag{9.3}
\]

Lemma 7.1 gives `c_u!=c_v`; since the difference is a nonzero integer,
(9.3) gives

\[
                         16^tF_w\le|c_u^f-c_v^f|.              \tag{9.4}
\]

The context update in (4.7), again by induction, gives

\[
                         \alpha_f=F_w\alpha_N=F_wt.            \tag{9.5}
\]

Combining (9.2), (9.4), and (9.5), then cancelling positive `F_w`, yields

\[
                              16^t<11t.                        \tag{9.6}
\]

But `11t<16^t` for every positive natural `t`: the case `t=1` is `11<16`,
and multiplication by `16` carries the inequality from `t` to `t+1` since
`11(t+1)<=16(11t)` for `t>=1`. This contradicts (9.6). Therefore the assumed
acceptance from `rho_v` is impossible. `QED`

Combining Lemmas 8.1 and 9.1, for every `u!=v`,

\[
\begin{aligned}
 &\operatorname{TailLegal}(N,W_{K,u}),\\
 &\operatorname{AcceptedFor}
    (0,\operatorname{balancedContext}(N),1,\rho_u,W_{K,u}),\\
 &\neg\operatorname{AcceptedFor}
    (0,\operatorname{balancedContext}(N),1,\rho_v,W_{K,u}).    \tag{9.7}
\end{aligned}
\]

Thus `W_(K,u)` belongs to `L_(0,N)(rho_u)` and not to
`L_(0,N)(rho_v)`. Their T46 right languages are unequal.

## 10. The all-K conclusion

**Proposition 10.1 (background-marker construction for forbidden zero).**
For the fixed distinct nonzero digits `(a,b)=(2,1)` and every `K : Nat`, let
`N,L,q_j,rho_j,W_(K,j)` be (5.1), (5.3)-(5.10), and (8.1)-(8.10). Then

\[
\begin{aligned}
 &K<\operatorname{card}(\operatorname{Fin}(K+1)),\\
 &j\mapsto\rho_j\text{ is injective},\\
 &\forall j,\ \operatorname{PersistentReachableAt}(0,N,\rho_j),\\
 &\forall u\ne v,\
   \neg\operatorname{RightLanguageEquivalentAt}(0,N,1,\rho_u,\rho_v),
                                                               \tag{10.1}
\end{aligned}
\]

and the final line is witnessed by the explicit oriented continuation
`W_(K,u)` in (9.7).

**Proof.** The cardinality identity is `card(Fin(K+1))=K+1`. Lemma 6.1 gives
common-level persistent reachability, Lemma 7.1 gives injectivity, and (9.7)
gives pairwise right-language inequivalence. `QED`

The three possible failure points requested in the agenda item are therefore
resolved as follows for this fixed pair:

| Check | Outcome | Exact reason |
|---|---|---|
| Reachability | succeeds | the zero-free point `x_j=D_j.111...` witnesses every scheduled overlap |
| Carry injectivity | succeeds | `v_5(D_u-D_v)=min(u,v)<L` |
| Continuation separation | succeeds | all-ones endpoint continuation plus exact carry amplification |

There is no failed property in the final construction. The first naive
separator attempt, appending zeroes to preserve the represented rational
point, fails immediately at T46's packet digit-avoidance conjunct. Equations
(8.1)-(8.8) are the explicit repair; this failure is not hidden or inferred
from finite testing.

## 11. Diagnostics, literature, and scope exclusions

### Diagnostics

No finite calculation, program, bounded search, random test, or empirical
digit sample is used. There is therefore no experimental evidence to promote
to a universal claim. All displayed bounds are symbolic and quantified as
stated.

### Literature search

No novelty or literature claim is made. This agenda item is an internal
structural analysis of the pinned T37/T43/T46 machine-checked interfaces, so
no external mathematical source is used beyond the canonical local root,
whose original external URL is `none`.

### Explicit exclusions

1. This is a `proof sketch`, not a machine-checked T49 theorem.
2. It concerns only the single forbidden digit `0` and the fixed
   background-marker class with `(a,b)=(2,1)`.
3. It proves nothing about arbitrary forbidden words or arbitrary forbidden
   digit sets.
4. It proves nothing about the decimal or hexadecimal digits of `Real.pi`.
5. It neither proves nor assumes `T37.JMix Real.pi` or any `JMix(pi)` claim.
6. It proves nothing about canonical V1 and must not be presented as a
   canonical V1 construction or resolution.
7. It proves nothing about sibling V3.
8. It does not concern schedule-aware controllers that retain the external
   level or schedule position as persistent state.
9. It does not claim a uniform theorem for all choices of distinct nonzero
   `a,b`; one fixed pair is enough for, and is the exact scope of, the
   constructive alternative.
10. It makes no statement about normality, disjunctivity, digit frequencies,
    or any actual digit stream.

## 12. Formalization map

- Existing imported definitions: T37 `wordValue`, `prefixCylinder`, `carry`;
  T43/T46 external-clock right-language semantics; T46 `BalancedFor`,
  `ReachableFor`, `ReachableAtFor`, `AcceptedFor`, `PersistentReachableAt`,
  and `RightLanguageEquivalentAt`.
- Reusable new lemmas suggested by the note: background-marker word value;
  nonboundary of `(9D+1)/(9*10^L)` against dyadic cylinders; all-ones
  extension prefix preservation; background-marker reduced-carry
  injectivity; and the explicit all-ones separator theorem.
- No Lean declaration is claimed here, so no axiom-audit registration is
  asserted.

## 13. Independent review

- Statement checked by: pending independent skeptic session.
- Proof checked by: pending independent skeptic session.
- Novelty/attribution checked by: not claimed; no novelty assertion is made.
