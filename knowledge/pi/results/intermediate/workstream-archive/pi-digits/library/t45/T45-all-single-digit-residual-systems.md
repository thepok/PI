# T45: Single-digit variants of the externally clocked residual carry system

Status: `proof sketch`. The cited T37, T39, T41, and T43 declarations are
machine-checked. The digit-parameterized definitions and transfer argument in
this note are rigorous prose and are not separately machine-checked.

## 1. Provenance and exact scope

- Canonical source: `knowledge/pi/statements/pi-digits.txt`.
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
- Original external source URL: none. The source is a human-authored local
  root recording Marcel's request of 2026-07-21.
- Machine-checked T37 interface:
  `TheoryLib.PiDigits.T37CrossBaseCarry`, SHA-256
  `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6`.
- Machine-checked T39 implementation dependency exposed through T43:
  `TheoryLib.PiDigits.T39BalancedCarryMyhillNerode`, SHA-256
  `ca4a062d143829622001d92864c686d7c5a6fbaae1dd3997b33054753e806a35`.
- Machine-checked T41 implementation dependency exposed through T43:
  `TheoryLib.PiDigits.T41ExternallyClockedResidualQuotients`, SHA-256
  `28c5e8dd241b04df6a59f36943bdc7fcebc13f987e509273161c66b02b19e5c3`.
- Machine-checked T43 interface:
  `TheoryLib.PiDigits.T43CommonLevelResidualIndex`, SHA-256
  `b3658d1fb1f63e58f76d968658f57a9cc380fa3a830a4cbab9e8e7b0293298be`.

The T39 hash displayed above is part of the inspectable dependency record; the
definitions below are matched primarily to T37 and T43. T43 itself names the
T39 concrete state and the T41 packet/residual types, so those two
machine-checked implementation modules are cited rather than re-derived. No
claim from an unverified T38, T40, or T42 note is used.

The canonical question V1 asks whether every finite decimal word occurs
contiguously in the decimal expansion of pi. This note does not address V1.
It studies a structural sibling: ten abstract residual carry systems, one for
each forbidden single decimal digit.

### Normalized quantifiers and ambiguities

1. A forbidden digit is one fixed `d : Fin 10`; it is fixed throughout a run.
2. Only the one-letter word `[d]` is forbidden. This is not a construction for
   an arbitrary finite forbidden word.
3. The external hexadecimal level `N`, balanced scale, and future schedule are
   supplied by a common external clock. They are not persistent-state fields.
4. A right language contains all finite legal packet lists, with no bound on
   continuation length. Equality is literal set equality.
5. States in one right-language comparison are reachable at the same
   level and receive the same actual future schedule tail.
6. "T43's exact witness schema" means the unchanged one-hot decimal witnesses,
   unchanged floor-selected hexadecimal prefixes, and unchanged endpoint
   continuations from T41/T43. Changing the nonzero one-hot digit would be a
   new schema and is not analyzed here.
7. Failure of that schema for one digit does not imply finite right-language
   index for that digit's system. It only invalidates this witness argument.
8. The corrected condition below is sufficient for this exact schema; no
   necessity claim is made.

## 2. T37 coordinates retained unchanged

For hexadecimal level `n`, put

\[
 m_n=\operatorname{T39.decimalLevel}(n)
     =\lfloor\log_{10}(16^n)\rfloor,
 \qquad
 \delta_n=m_{n+1}-m_n.
\tag{1}
\]

The machine-checked T39 bounds give

\[
 10^{m_n}\le 16^n<10^{m_n+1},\qquad
 \delta_n\in\{1,2\}.
\tag{2}
\]

For hexadecimal and decimal prefix values `A,D`, T37 defines the signed carry

\[
 C(n,m_n,A,D)=10^{m_n}A-16^nD.
\tag{3}
\]

Set

\[
 a_n=5^{m_n},\qquad b_n=2^{4n-m_n},\qquad c=a_nA-b_nD.
\tag{4}
\]

T41's machine-checked factorization of T37's carry is

\[
 C(n,m_n,A,D)=2^{m_n}c,
\tag{5}
\]

and its `overlap_iff_reducedCarry_bounds`, derived from T37's
`cylinders_overlap_iff_carry_bounds`, is

\[
 \operatorname{prefixCylinder}(16,n,A)\cap
 \operatorname{prefixCylinder}(10,m_n,D)\ne\varnothing
 \quad\Longleftrightarrow\quad -a_n<c<b_n.
\tag{6}
\]

Equations (1)-(6) do not mention a forbidden digit. Every digit-specific
system below uses these exact coordinates and bounds.

## 3. The system for an arbitrary forbidden digit

Fix `d : Fin 10`. The following definitions are obtained by replacing only
T39/T41's digit-`2` avoidance predicates. All lengths, values, transitions,
and strict carry bounds remain unchanged.

### 3.1 Concrete balanced states and reachability

For a decimal list `v : List (Fin 10)`, define

\[
 \operatorname{Avoids}_d(v)\quad:\Longleftrightarrow\quad d\notin v.
\tag{7}
\]

A T39 concrete state `q` has fields `level`, `hexPrefix`, and
`decimalPrefix`. Define `Balanced_d(q)` to mean the conjunction

\[
\begin{aligned}
 &|q.\mathrm{hexPrefix}|=q.\mathrm{level},\\
 &|q.\mathrm{decimalPrefix}|=m_{q.\mathrm{level}},\\
 &\operatorname{T37.ValidPrefix}
      (16,q.\mathrm{level},\operatorname{T37.wordValue}(q.\mathrm{hexPrefix})),\\
 &\operatorname{T37.ValidPrefix}
      (10,m_{q.\mathrm{level}},
       \operatorname{T37.wordValue}(q.\mathrm{decimalPrefix})),\\
 &\operatorname{Avoids}_d(q.\mathrm{decimalPrefix}),\\
 &\operatorname{prefixCylinder}(16,q.\mathrm{level},A_q)\cap
   \operatorname{prefixCylinder}(10,m_{q.\mathrm{level}},D_q)
   \ne\varnothing,
\end{aligned}
\tag{8}
\]

where `A_q` and `D_q` are the two displayed `wordValue`s. Definition (8) is
literally `T39.Balanced` with its fifth conjunct
`T39.avoidsTwo q.decimalPrefix` replaced by (7). By (6), its last conjunct is
equivalently the exact reduced-carry bound.

For a T39 symbol `x`, retain T39's `appendSymbol` and define

\[
 \operatorname{RetainedStep}_d(q,x)
 :\Longleftrightarrow
 |x.\mathrm{decimal}|=\delta_{q.\mathrm{level}}
 \ \wedge\
 \operatorname{Balanced}_d(\operatorname{appendSymbol}(q,x)).
\tag{9}
\]

Define legal concrete continuations recursively:

\[
\begin{aligned}
 \operatorname{LegalContinuation}_d(q,[])&:=\operatorname{Balanced}_d(q),\\
 \operatorname{LegalContinuation}_d(q,x::w)&:=
   \operatorname{RetainedStep}_d(q,x)\ \wedge\
   \operatorname{LegalContinuation}_d(\operatorname{appendSymbol}(q,x),w).
\end{aligned}
\tag{10}
\]

Using T39's unchanged `initialState` and `run`, define

\[
 \operatorname{Reachable}_d(q)
 :\Longleftrightarrow
 \exists w,
 \operatorname{LegalContinuation}_d(\operatorname{initialState},w)
 \ \wedge\
 \operatorname{run}(\operatorname{initialState},w)=q.
\tag{11}
\]

Finally, common-level concrete reachability is

\[
 \operatorname{ReachableAt}_d(N,q)
 :\Longleftrightarrow
 \operatorname{Reachable}_d(q)\ \wedge\ q.\mathrm{level}=N.
\tag{12}
\]

This is T43's `ReachableAt` with `T39.Reachable` replaced by (11).

### 3.2 Persistent residual transitions

Persistent state remains exactly T41's

\[
 \rho=(c,z):\operatorname{ResidualState},
\tag{13}
\]

where `c : Int` is exact reduced carry and `z : Nat` is a decimal suffix. As
in T43, fix suffix width `r=1`. The external context at level `n` is exactly
`T41.balancedContext n=(n,m_n,a_n,b_n)`.

A T41 packet `p` has width `s`, hexadecimal digit `h`, and an `s`-digit
decimal block of value `e`. T41's unchanged transition is

\[
\begin{aligned}
 a'&=5^s a,& b'&=2^{4-s}b,\\
 c'&=16\,5^s c+a'h-b'e,&
 z'&=(10^s z+e)\bmod 10.
\end{aligned}
\tag{14}
\]

Define `RetainedPacket_d(1,context,rho,p)` by the four conditions

\[
 s\in\{1,2\},\qquad
 \operatorname{Avoids}_d(p.\mathrm{decimal}),\qquad
 -a'<c',\qquad c'<b'.
\tag{15}
\]

This is T41's `RetainedPacket` with only `packetAvoidsTwo` replaced by (7).
Define `Accepted_d` recursively by

\[
\begin{aligned}
 \operatorname{Accepted}_d(C,\rho,[])&:=\mathrm{True},\\
 \operatorname{Accepted}_d(C,\rho,p::w)&:=
   \operatorname{RetainedPacket}_d(1,C,\rho,p)\ \wedge\\
 &\hspace{25mm}
   \operatorname{Accepted}_d
     (\operatorname{nextContext}(C,p.\mathrm{width}),
      \operatorname{nextResidual}(1,C,\rho,p),w).
\end{aligned}
\tag{16}
\]

All functions in (14)-(16), except the subscripted avoidance predicates, are
the exact T41 definitions referenced by T43.

### 3.3 One common schedule tail and right languages

Do not allow an arbitrary sequence of packet widths. Retain T43's definition
verbatim:

\[
\begin{aligned}
 \operatorname{TailLegal}(N,[])&:=\mathrm{True},\\
 \operatorname{TailLegal}(N,p::w)&:=
   (p.\mathrm{width}=\delta_N)\ \wedge\
   \operatorname{TailLegal}(N+1,w).
\end{aligned}
\tag{17}
\]

Persistent reachability at a common level is

\[
 \operatorname{PersistentReachableAt}_d(N,\rho)
 :\Longleftrightarrow
 \exists q,
 \operatorname{ReachableAt}_d(N,q)\ \wedge\
 \operatorname{T41.residualOf}(1,q)=\rho.
\tag{18}
\]

Define the finite continuation language

\[
 \mathcal L_{d,N}(\rho)=
 \{w:\operatorname{List}(\operatorname{T41.Packet}):
   \operatorname{TailLegal}(N,w)\ \wedge\
   \operatorname{Accepted}_d
     (\operatorname{T41.balancedContext}(N),\rho,w)\}.
\tag{19}
\]

Then define digit-`d` right-language equivalence at the shared level by

\[
 \rho\equiv_{d,N}\rho'
 \quad:\Longleftrightarrow\quad
 \mathcal L_{d,N}(\rho)=\mathcal L_{d,N}(\rho').
\tag{20}
\]

Equations (17)-(20) are exactly T43's `TailLegal`,
`PersistentReachableAt`, `ContinuationLanguageAt`, and
`RightLanguageEquivalentAt`, with reachability and acceptance changed only at
the explicitly displayed single-digit avoidance tests.

Thus (7)-(20) define the requested system for every one of the ten choices
`d=0,1,...,9`; no finite computation is involved.

## 4. T43's exact witness schema

For `K : Nat` and `j : Fin (K+1)`, T43 fixes

\[
\begin{aligned}
 N_K&=\operatorname{T43.familyLevel}(K)
     =\operatorname{T41.witnessLevel}(K,1),\\
 q_{K,j}&=\operatorname{T43.familyState}(K,j)
     =\operatorname{T41.witnessState}(K,1,j),\\
 \rho_{K,j}&=\operatorname{T43.familyResidual}(K,j)
     =\operatorname{T41.residualOf}(1,q_{K,j}),\\
 W_{K,j}&=\operatorname{T43.familySeparator}(K,j)
     =\operatorname{T41.distinguishingContinuation}(K,1,j).
\end{aligned}
\tag{21}
\]

Write `L=m_(N_K)` and `k=1+j`. T41 defines the decimal prefix of `q_(K,j)`
to be

\[
 \operatorname{oneHotWord}(L,k)
 =0^{L-(k+1)}\,1\,0^k.
\tag{22}
\]

The machine-checked `T41.witness_digit_position_lt` gives `k<L`, so (22) is
the intended fixed-width word. The hexadecimal prefix is unchanged from T41's
`rationalHexValue` construction.

## 5. First exact failure: forbidden digit 1

Let `d=1`. We prove that the first reachability obligation in T43's unchanged
witness schema fails for every `K` and every `j : Fin (K+1)`.

### Lemma 1: every exact witness contains the forbidden digit

For all `K,j`,

\[
 1\in q_{K,j}.\mathrm{decimalPrefix}.
\tag{23}
\]

**Proof.** By (21)-(22), the decimal prefix is
`replicate (L-(k+1)) 0 ++ [1] ++ replicate k 0`. The middle singleton
contains `1`, and membership is preserved by list append. Hence (23). This is
a symbolic identity valid for every `K,j`, not a bounded check. `QED`

By (7), (23) gives

\[
 \neg\operatorname{Avoids}_1(q_{K,j}.\mathrm{decimalPrefix}).
\tag{24}
\]

Since this predicate is the fifth conjunct of (8),

\[
 \neg\operatorname{Balanced}_1(q_{K,j}).
\tag{25}
\]

### Lemma 2: reachability implies final balancedness

For every digit `d` and concrete state `q`,

\[
 \operatorname{Reachable}_d(q)\Longrightarrow\operatorname{Balanced}_d(q).
\tag{26}
\]

**Proof.** More generally, induction on `w` in (10) shows

\[
 \operatorname{LegalContinuation}_d(q_0,w)
 \Longrightarrow
 \operatorname{Balanced}_d(\operatorname{run}(q_0,w)).
\]

For `w=[]`, this is the first line of (10). For `w=x::v`, the first conjunct
of (10) makes `appendSymbol(q_0,x)` balanced, and the induction hypothesis
applied to the tail gives balancedness of the final run. Apply this with
`q_0=initialState` and the equality in (11). `QED`

Combining (25) and (26) gives

\[
 \neg\operatorname{Reachable}_1(q_{K,j}),
\qquad
 \neg\operatorname{ReachableAt}_1(N_K,q_{K,j}).
\tag{27}
\]

This is the first failed T43 witness obligation: the digit-`1` analogue of
`T43.family_reachableAt` is false for the displayed source state. Therefore
the unchanged schema cannot proceed to `family_persistent_reachableAt` or to
its continuation-separation theorem. No carry or continuation inequality is
needed: reachability already fails at the exact digit-avoidance conjunct.

Statement (27) does **not** say that `rho_(K,j)` cannot be induced by some
other digit-`1`-avoiding source, and it does not determine the digit-`1`
system's right-language index. It says precisely that T43's displayed source
witness is invalid after the requested substitution.

## 6. Corrected sufficient condition for the exact schema

The relevant invariant is the support of every decimal word used by the
construction. Define the safe-support condition

\[
 \operatorname{Safe}(d):\Longleftrightarrow d\ne0\ \wedge\ d\ne1.
\tag{28}
\]

For decimal digits this is exactly `d in {2,3,4,5,6,7,8,9}`.

### Lemma 3: support avoidance

If `Safe(d)` and every entry of a decimal list `v` is `0` or `1`, then
`Avoids_d(v)`.

**Proof.** If `d` belonged to `v`, the support assumption would give `d=0` or
`d=1`, contradicting (28). `QED`

### Lemma 4: all exact-schema decimal data have support `{0,1}`

Assume the exact T43 schema (21).

1. By (22), each witness decimal prefix is a list of zeroes with one `1`.
2. T41's `extendedWitnessState K 1 j` has decimal value
   `10^(1+j+S)`, where `S` is the scheduled extension length. The
   machine-checked proof of `T41.extendedWitness_avoidsTwo` rewrites its
   fixed-width decimal prefix to `oneHotWord`; this rewrite depends on the
   value and width, not on forbidden digit `2`. Hence its entries are all
   `0` or `1`.
3. Every scheduled prefix used to certify reachability is a `take` of one of
   these one-hot words. Every decimal packet in `W_(K,j)` is a `drop`/`take`
   slice of the extended one-hot word. Taking a prefix or slice introduces no
   new digit.

Therefore every decimal prefix and packet used by the exact witness and its
explicit continuation has support contained in `{0,1}`. `QED`

### Proposition 5: corrected transfer criterion

If `Safe(d)`, then T43's unchanged family (21) supplies arbitrarily large
common-level families with pairwise distinct digit-`d` right languages.

**Proof.** Fix `K` and `j : Fin (K+1)`.

1. **Reachability.** T41 proves reachability of `q_(K,j)` by showing every
   scheduled prefix of its rational endpoint is balanced. Valid-prefix facts,
   cylinder overlap, and scheduled widths are independent of the forbidden
   digit. Lemmas 3-4 replace the sole digit-`2` avoidance step by
   `Avoids_d`. Replaying the recursive construction (9)-(11) gives
   `ReachableAt_d(N_K,q_(K,j))`, hence
   `PersistentReachableAt_d(N_K,rho_(K,j))`.

2. **Common-tail legality.** T43's induction
   `tailLegal_packetsOfSymbols_of_legal` uses only the scheduled-width
   conjunct of each retained step. The same induction applied to the replayed
   digit-`d` legal continuation gives `TailLegal(N_K,W_(K,j))`.

3. **Acceptance from the oriented witness.** Every packet of `W_(K,j)` has
   support in `{0,1}` by Lemma 4, hence avoids `d` by Lemma 3. The exact carry
   bounds are the same bounds certified by the rational endpoint path.
   Therefore

   \[
   \operatorname{Accepted}_d
     (\operatorname{balancedContext}(N_K),\rho_{K,j},W_{K,j}).
   \tag{29}
   \]

4. **Rejection from every other witness.** Fix distinct `u` and `v`. Suppose, for a
   contradiction, that `W_(K,u)` were also accepted from `rho_(K,v)` in the
   digit-`d` system. T41's separator proof after this assumption is purely
   arithmetic, so we reproduce its decisive inequalities.

   Let `x_u,x_v` be the two final reduced carries, `a_f,b_f` the final context
   scales, `t=a_(N_K)>0` the continuation length, and `F>0` T41's
   `fiveMultiplier` of the continuation. Acceptance of both runs gives

   \[
      |x_u-x_v|<a_f+b_f<11a_f,
   \tag{30}
   \]

   because T41's `balancedContext_b_lt_ten_a` gives `b_f<10a_f`. T41's exact
   carry-difference identity and injectivity of the witness reduced carries
   give

   \[
   16^tF
     =\operatorname{carryMultiplier}(W_{K,u})
     \le |x_u-x_v|.
   \tag{31}
   \]

   T41's context identity gives `a_f=F a_(N_K)=Ft`. Combining (30)-(31) and
   cancelling positive `F` yields

   \[
                         16^t<11t.
   \tag{32}
   \]

   This contradicts the machine-checked arithmetic inequality
   `T41.eleven_mul_lt_sixteen_pow`, namely `11t<16^t` for `t>0`. Thus

   \[
   \neg\operatorname{Accepted}_d
     (\operatorname{balancedContext}(N_K),\rho_{K,v},W_{K,u}).
   \tag{33}
   \]

5. Equations (29), (33), and common-tail legality put `W_(K,u)` in
   `L_(d,N_K)(rho_(K,u))` and outside `L_(d,N_K)(rho_(K,v))`. Hence distinct
   members of the `K+1` family have unequal right languages.

Since `K` is arbitrary, the common-level right-language index is unbounded for
every `d` satisfying (28). `QED`

The role of (28) is now exact: it guarantees that the existing zero/one
decimal support is safe. It is the corrected sufficient condition for this
schema. It neither asserts nor requires a construction for forbidden digit
`0` or forbidden digit `1`.

## 7. Per-digit outcome and exact conclusion

The definitions in Section 3 apply uniformly to all ten digits. The unchanged
T43 witness schema has the following status in this note:

| Forbidden digit `d` | Exact T43 one-hot schema |
|---|---|
| `0` | Not covered by `Safe(d)`; no index conclusion is made here. |
| `1` | Fails at source-state reachability by (23)-(27). |
| `2,3,4,5,6,7,8,9` | Satisfies `Safe(d)`; Proposition 5 transfers the schema. |

**Structural conclusion (`proof sketch`).** Replacing digit-`2` avoidance by
digit-`d` avoidance gives the precise externally clocked residual system
(7)-(20) for every decimal digit. T43's exact witness schema is not uniform
over all ten digits: for forbidden digit `1`, every displayed one-hot source
already contains `1`, so its common-level reachability certificate fails
before any continuation inequality. The condition `d` not in `{0,1}` is
sufficient for the unchanged schema because all decimal data in the witness
and separator paths use only `0` and `1`; under that condition the arithmetic
separator is unchanged.

This result is restricted as follows:

1. It is about an abstract structural sibling of T37/T43, not a digit stream.
2. It proves nothing about arbitrary forbidden words or even about the
   unresolved single-digit systems for `d=0` and `d=1` beyond failure of the
   exact displayed witness schema.
3. It proves nothing about the hexadecimal or decimal digits of `Real.pi`.
4. It does not prove, assume, or provide evidence for `T37.JMix Real.pi`.
5. It proves nothing about canonical V1.
6. It proves nothing about sibling V3.
7. It makes no claim about a separate "canonical V1" encoding or about any
   sibling V3 formalization.
8. No bounded computation, digit search, or finite experiment is used as
   evidence for any universal statement.
