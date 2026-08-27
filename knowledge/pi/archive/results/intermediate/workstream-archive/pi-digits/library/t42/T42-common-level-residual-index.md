# T42: Infinite common-level index for the externally clocked residual system

Status: `proof sketch`. The imported T37, T39, and T41 declarations named
below are machine-checked. The common-tail restriction and the final
arbitrary-finite-code conclusion are proved here in prose and have not been
separately formalized as T42 Lean declarations.

## 1. Provenance, target, and imported interfaces

- Canonical source: `knowledge/pi/statements/pi-digits.txt`.
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The source is a human-authored local
  root recording Marcel's request of 2026-07-21.
- Machine-checked T37 interface:
  `TheoryLib.PiDigits.T37CrossBaseCarry`, staged as `CrossBaseCarry.lean`,
  SHA-256
  `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6`.
- Machine-checked T39 interface:
  `TheoryLib.PiDigits.T39BalancedCarryMyhillNerode`, staged as
  `BalancedCarryMyhillNerode.lean`, SHA-256
  `ca4a062d143829622001d92864c686d7c5a6fbaae1dd3997b33054753e806a35`.
- Machine-checked T41 interface:
  `TheoryLib.PiDigits.T41ExternallyClockedResidualQuotients`, staged as
  `ExternallyClockedResidualQuotients.lean`, SHA-256
  `28c5e8dd241b04df6a59f36943bdc7fcebc13f987e509273161c66b02b19e5c3`.

The canonical question V1 asks whether every finite decimal word occurs
contiguously in the decimal expansion of pi. T42 does not answer or advance
that question. Its only target is the continuation-language index of T41's
exact externally clocked residual carry system under avoidance of the one
decimal digit `2`.

### Normalized quantifiers and possible ambiguities

1. The family size `K` is an arbitrary positive natural number. For `K=1`,
   pairwise separation is vacuous, but the single state still has to be
   reachable.
2. The suffix width is fixed to `r=1`. This is enough to rule out an arbitrary
   finite behavior-preserving code because such a code would have to work for
   this fixed residual system as well.
3. A common-level comparison means that all states in one family occur at one
   identical external hexadecimal level `N_K`. They therefore receive the
   same actual future balanced-schedule tail.
4. Persistent state means exactly T41's `ResidualState`: a signed reduced
   carry and a decimal suffix. Absolute level, decimal length, and scale
   factors are external clock context and are not persistent controller data.
5. A legal continuation is narrower than arbitrary T41 `Accepted` input: its
   packet widths must equal the actual T39 balanced-schedule increments from
   the common level. This prevents the proof from using an artificial width
   sequence.
6. Right-language equivalence is equality of all finite legal continuation
   languages, not agreement up to a bounded continuation length.
7. "Infinite index" means there is no finite uniform bound on the number of
   right-language classes at a common external level. Equivalently, no finite
   code of persistent residual states preserves all such languages when the
   clock context is supplied externally.

No claim below depends on the unverified T38 or T40 notes.

## 2. Exact externally clocked residual system

This section fixes notation by directly matching T41. No replacement system
is introduced.

T39 defines

\[
 m_n=\operatorname{decimalLevel}(n)=\lfloor\log_{10}(16^n)\rfloor,
 \qquad
 \delta_n=\operatorname{scheduleIncrement}(n)=m_{n+1}-m_n.
 \tag{1}
\]

The machine-checked declarations `T39.decimalLevel_lower`,
`T39.decimalLevel_upper`, `T39.scheduleIncrement_one_or_two`, and
`T39.decimalLevel_succ` give

\[
 10^{m_n}\le 16^n<10^{m_n+1},\qquad
 \delta_n\in\{1,2\},\qquad m_{n+1}=m_n+\delta_n.
 \tag{2}
\]

For a hexadecimal prefix value `A` and decimal prefix value `D` at level `n`,
T41 defines

\[
 a_n=5^{m_n},\qquad b_n=2^{4n-m_n},\qquad
 c_n=a_nA-b_nD.
 \tag{3}
\]

These are exactly `T41.balancedContext n` and
`T41.reducedCarryAt n A D`. The theorem `T41.balanced_gcd` identifies the
removed factor as the full gcd

\[
 \gcd(10^{m_n},16^n)=2^{m_n},
 \tag{4}
\]

while `T41.carry_eq_pow_two_mul_reducedCarryAt` identifies T37's signed carry
with `2^(m_n) c_n`. Consequently `T41.overlap_iff_reducedCarry_bounds`, derived
from the machine-checked `T37.cylinders_overlap_iff_carry_bounds`, says that
the two prefix cylinders overlap exactly when

\[
                         -a_n<c_n<b_n.                       \tag{5}
\]

### Persistent state and external context

The persistent state is T41's structure

\[
                 \rho=(c,z)\in\mathbb Z\times\mathbb N,     \tag{6}
\]

where `c = ResidualState.reducedCarry` and
`z = ResidualState.suffix`. For this note `z` is reduced modulo `10` because
`r=1`. There is no level field in `ResidualState`.

The external context is `T41.balancedContext n`, whose fields are

\[
                     (n,m_n,a_n,b_n).                        \tag{7}
\]

The occurrence of `n` in (7) is external clock information, not persistent
state. A packet `p` consists of a width `s`, one hexadecimal digit `h`, and a
fixed-length `s`-digit decimal block of value `e`. T41's `nextContext` and
`nextResidual` are exactly

\[
\begin{aligned}
 n'&=n+1, &m'&=m+s, &a'&=5^s a, &b'&=2^{4-s}b,\\
 c'&=16\,5^s c+a'h-b'e,
 &z'&=(10^s z+e)\bmod 10.                                  \tag{8}
\end{aligned}
\]

The machine-checked `T41.nextContext_balanced` says that when
`s=delta_n`, the new context is exactly `balancedContext (n+1)`.
The machine-checked `T41.nextResidual_residualOf_appendSymbol` identifies (8)
with appending the corresponding T39 symbol. Its carry component is the
gcd-reduced specialization of `T37.carry_append`, not an approximation.

T41's predicate `RetainedPacket 1 C rho p` requires:

1. `s` is `1` or `2`;
2. every decimal digit in the packet avoids `2`;
3. the updated carry satisfies `-a' < c' < b'`.

Its recursive predicate `Accepted C 1 rho w` requires every packet in `w` to
be retained under the iterated contexts and residuals.

## 3. Common-level reachability and legal right languages

Define a concrete T39 state `q` to be **reachable at external level `N`** when

\[
 \operatorname{ReachableAt}(N,q)
 :\Longleftrightarrow
 \operatorname{T39.Reachable}(q)\ \wedge\ q.\mathrm{level}=N.
 \tag{9}
\]

This uses T39 reachability only as a certificate that the residual occurs in
the exact balanced digit-`2`-avoiding system. The persistent controller state
induced by `q` is `T41.residualOf 1 q`; the full T39 prefix and its level are
not retained by the controller.

Define legality along the actual future balanced tail recursively:

\[
\begin{aligned}
 \operatorname{TailLegal}(N,[])&:=\mathrm{True},\\
 \operatorname{TailLegal}(N,p::w)&:=
   \bigl(p.\mathrm{width}=\delta_N\bigr)\ \wedge\
   \operatorname{TailLegal}(N+1,w).
                                                               \tag{10}
\end{aligned}
\]

Thus every run compared at level `N` receives the same sequence
`delta_N, delta_(N+1), ...`. Equation (2) ensures each required width is a
valid one- or two-digit T41 packet width.

For a persistent residual `rho`, define its common-level continuation language
by

\[
 \mathcal L_N(\rho)=
 \{w:\operatorname{List}(\operatorname{T41.Packet}):
   \operatorname{TailLegal}(N,w)\ \wedge
   \operatorname{T41.Accepted}(\operatorname{balancedContext}(N),1,\rho,w)
 \}.
                                                               \tag{11}
\]

For a concrete state `q` reachable at `N`, abbreviate

\[
            \mathcal L_N(q)=
            \mathcal L_N(\operatorname{T41.residualOf}(1,q)). \tag{12}
\]

Two reachable states at the same external level are **right-language
equivalent** exactly when their sets in (12) are equal. Notice that `N`
parameterizes the external experiment; it is not inserted into the persistent
state.

### Lemma 1: T39 legality supplies common-tail legality

If `T39.LegalContinuation q v`, then

\[
 \operatorname{TailLegal}
   (q.\mathrm{level},\operatorname{T41.packetsOfSymbols}(v)). \tag{13}
\]

**Proof.** Induct on `v`.

1. For the empty list, (13) is the first clause of (10).
2. Write `v=a::v'`. Unfolding `T39.LegalContinuation` gives
   `T39.RetainedStep q a` and
   `T39.LegalContinuation (T39.appendSymbol q a) v'`.
3. The first conjunct in `T39.RetainedStep q a` is
   `a.decimal.length = T39.scheduleIncrement q.level`.
   By the definitions of `T41.packetOfSymbol` and
   `T41.packetsOfSymbols`, this is exactly the head-width equality required
   in (10).
4. Definitionally,
   `(T39.appendSymbol q a).level = q.level+1`. The induction hypothesis is
   therefore the tail clause of (10).

This proves (13). No schedule-tail claim from T38 or T40 is used.

## 4. Exactly `K` reachable states at one level

Fix an arbitrary `K>0` and set

\[
 M=K-1,\qquad r=1,\qquad
 N_K=\operatorname{T41.witnessLevel}(M,1).
 \tag{14}
\]

Since T41 defines

\[
 \operatorname{witnessLevel}(M,r)=2(M+r+1),
 \tag{15}
\]

positivity of `K` gives `M+1=K` and `N_K=2(K+1)`. For each `j : Fin K`, use
this equality to regard `j` as an element of `Fin (M+1)` and define

\[
                       q_j=\operatorname{T41.witnessState}(M,1,j).
                                                               \tag{16}
\]

Concretely, T41's witness has decimal value

\[
                  D_j=\operatorname{witnessDecimalValue}(1,j)
                     =10^{1+j},                               \tag{17}
\]

represented at fixed width by a one-hot decimal word. It therefore avoids
`2` and has last decimal digit zero. Its hexadecimal prefix is selected by
T41's `rationalHexValue` so that all scheduled prefixes are balanced.

The machine-checked theorem `T41.witnessState_reachable j` gives
`T39.Reachable q_j` for every `j`. By the definition of `witnessState`, every
`q_j.level` is definitionally `N_K`. Hence

\[
                    \operatorname{ReachableAt}(N_K,q_j)       \tag{18}
\]

for all `j : Fin K`.

## 5. Pairwise explicit separating continuations

For each `u : Fin K`, define the explicit packet continuation

\[
                  W_u=
                  \operatorname{T41.distinguishingContinuation}(M,1,u).
                                                               \tag{19}
\]

This is not an existentially chosen word. T41 defines it as
`packetsOfSymbols` of `distinguishingSymbols`, which is the endpoint slice of
`extendedWitnessState M 1 u`, beginning at `N_K` and having the explicit
positive length

\[
 t=\operatorname{T41.separationSteps}(M,1)
   =5^{m_{N_K}}.                                              \tag{20}
\]

The machine-checked theorem `T41.distinguishingSymbols_legal u` states

\[
 \operatorname{T39.LegalContinuation}
   (q_u,\operatorname{T41.distinguishingSymbols}(M,1,u)).     \tag{21}
\]

Applying Lemma 1 to (21) proves

\[
                       \operatorname{TailLegal}(N_K,W_u).     \tag{22}
\]

The machine-checked theorems
`T41.distinguishingContinuation_accepted` and
`T41.distinguishingContinuation_rejected_of_ne` supply the behavior of the
same explicit word:

\[
\begin{aligned}
 &\operatorname{T41.distinguishingContinuation\_accepted}(u):\\
 &\quad \operatorname{Accepted}
   (\operatorname{balancedContext}(N_K),1,
    \operatorname{residualOf}(1,q_u),W_u),                   \tag{23}\\
 &\operatorname{T41.distinguishingContinuation\_rejected\_of\_ne}(u\ne v):\\
 &\quad \neg\operatorname{Accepted}
   (\operatorname{balancedContext}(N_K),1,
    \operatorname{residualOf}(1,q_v),W_u).                   \tag{24}
\end{aligned}
\]

Now fix distinct `u,v : Fin K`. Equations (22)-(23), together with definition
(11), give

\[
                              W_u\in\mathcal L_{N_K}(q_u).    \tag{25}
\]

Equation (24) gives

\[
                              W_u\notin\mathcal L_{N_K}(q_v),\tag{26}
\]

even though (22) shows that `W_u` is a legal continuation along their common
future balanced-schedule tail. Therefore

\[
                         \mathcal L_{N_K}(q_u)
                         \ne\mathcal L_{N_K}(q_v).            \tag{27}
\]

Thus (19) is an explicit oriented separator for every ordered pair `u != v`.
In particular, the `q_j` are distinct: equality of two concrete states would
make their induced residuals and hence their languages equal, contradicting
(27).

When `K=1`, (18) supplies the one required reachable state and there are no
distinct index pairs, so (27) is vacuously satisfied. Therefore Sections 4-5
construct, for every positive `K`, exactly `K` common-level reachable states
whose right languages are pairwise distinct.

## 6. Infinite index and arbitrary finite quotients

Equation (27) proves that the number of right-language classes among residuals
reachable at the single external level `N_K` is at least `K`. Since `K` is
arbitrary, the common-level externally clocked system has unbounded, hence
infinite, right-language index.

For the equivalent quotient formulation, let `Q` be any finite type and let

\[
                     \operatorname{code}:\operatorname{ResidualState}\to Q
                                                               \tag{28}
\]

be arbitrary. Suppose it is exactly behavior-preserving with the external
clock, meaning that for every level `N` and every pair `q,q'` reachable at
that same `N`,

\[
 \operatorname{code}(\operatorname{residualOf}(1,q))
 =\operatorname{code}(\operatorname{residualOf}(1,q'))
 \quad\Longrightarrow\quad
 \mathcal L_N(q)=\mathcal L_N(q').                           \tag{29}
\]

Take `K=|Q|+1` and the family (16). Pigeonhole gives distinct `u,v : Fin K`
with equal codes in (28). Condition (29) would make their languages equal,
contradicting the explicit separator (25)-(26). Therefore no arbitrary finite
code of persistent residual states satisfies (29). This argument does not
assume that the code is a congruence-and-suffix code, a transition congruence,
or any other natural quotient family.

The common-level construction is essential: the collision and separator are
tested with one identical external context and one identical actual schedule
tail. The conclusion cannot be attributed to storing or comparing absolute
schedule positions in persistent state.

## 7. Exact conclusion and scope exclusions

**Conclusion (`proof sketch`).** For every positive natural `K`, the explicit
family (16) consists of `K` states reachable at the one external level `N_K`.
For every distinct pair `u,v`, the explicit continuation (19) follows their
common future balanced-schedule tail, is accepted from `q_u`, and is rejected
from `q_v`. Hence their right languages are pairwise distinct, the common-level
right-language index is infinite, and no arbitrary finite persistent-state
code can preserve all externally clocked continuation languages.

The conclusion is restricted as follows:

1. It is a theorem about the abstract exact T37/T39/T41 digit-`2`-avoidance
   residual system, not about any observed or conjectured digit stream.
2. It proves nothing about the hexadecimal or decimal digits of `Real.pi`.
3. It does not prove, assume, or provide evidence for `T37.JMix Real.pi`.
4. It proves nothing about canonical V1, the assertion that every finite
   decimal word occurs contiguously in pi.
5. It proves nothing about sibling V3, the assertion that every infinite
   decimal sequence occurs as a scattered subsequence of pi.
6. It makes no claim about literature novelty.
7. It does not promote this prose argument to `machine-checked`; only the
   cited T37, T39, and T41 interfaces have that status.
