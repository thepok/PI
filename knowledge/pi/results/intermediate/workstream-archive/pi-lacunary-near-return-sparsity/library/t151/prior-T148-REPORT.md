# T148: a positive Landau atom need not give positive valuation drift

Status: `proof sketch`. This note independently reconstructs the carry graph
and gives an exact counterfamily to the agenda's literal assertion. The replay
is an `experiment`: it validates exact finite calculations but is not the proof.
This is an A13/A14 coefficient-model result. It makes no fixed-pi, canonical
A1, C1, C2, or literature-novelty claim.

```text
ENDPOINT_COUNT: 1
ENDPOINT_KIND: EXACT_COUNTERFAMILY
COMPARATOR_COUNT: 6
SCOPED_VERDICT_COUNT: 1
```

## 1. Provenance, scope, and normalized quantifiers

The canonical source is the system-formulated local statement; no external
source URL exists. Its byte-exact delivered copy is `canonical_statement.txt`,
with SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
It asks whether, for fixed pi and base 10,

```text
for every A >= 1 there exists n0 >= 1 such that
for every n >= n0 there exists N >= 1 with
A*n*Q_pi(n,N) <= N^2,
```

where pairs are ordered and diagonal-inclusive and the circle-distance cutoff
is strict. Nothing below addresses those quantifiers.

The literal T148 coefficient question fixes:

1. a prime `p`;
2. nonempty finite lists `a=(a_1,...,a_r)` and `b=(b_1,...,b_s)` of positive
   integers, with repetitions retained;
3. balance `sum_i a_i=sum_j b_j` and unequal coefficient multisets;
4. `Lambda(x)=sum_i floor(a_i*x)-sum_j floor(b_j*x)` and
   `M=max(a_i,b_j)`.

It does **not** assume that the factorial ratio is integral for every `n`.
That omission is decisive. T145 assumed all-`n` integrality before deriving
`Lambda>=0`; T148 asks to treat T145 as motivation and independently prove or
refute the displayed stronger inequality. This note therefore does not silently
add integrality.

Ambiguities are fixed as follows. Digits are read least-significant first
(LSDF); all digit-labeled parallel edges are retained; a state/cycle is
accessible only if reachable from the all-zero state; a cycle is a nonempty
closed walk and its weight excludes terminal weights; `mu_+` is measured in
the edge units `(p-1)*v_p`; a constancy atom is an open component between
successive discontinuities on `[0,1]`; and `d_p(I)` requires a grid point in
the open interior, so endpoint values are irrelevant.

## 2. Independently reconstructed carry graph and Landau identity

For a positive coefficient `c`, its carry lies in

\[
 K_c=\{0,1,\ldots,c-1\}.
\tag{2.1}
\]

Indeed, if `0<=gamma<c` and `0<=e<p`, then
`0<=floor((ce+gamma)/p)<c`. The full raw state space is

\[
 K=\prod_i K_{a_i}\times\prod_j K_{b_j}.
\tag{2.2}
\]

Write `q=(alpha_1,...,alpha_r;beta_1,...,beta_s)`, initially all zero. On
digit `e in {0,...,p-1}`, define

\[
 \alpha'_i=\left\lfloor{a_i e+\alpha_i\over p}\right\rfloor,
 \qquad
 \beta'_j=\left\lfloor{b_j e+\beta_j\over p}\right\rfloor.
\tag{2.3}
\]

The emitted product digit for a coefficient `c` and carry `gamma` is

\[
 \rho_c(\gamma,e)=ce+\gamma-p\left\lfloor{ce+\gamma\over p}\right\rfloor.
\tag{2.4}
\]

Set

\[
 w(q,e)=\sum_j\rho_{b_j}(\beta_j,e)
       -\sum_i\rho_{a_i}(\alpha_i,e),
\quad
 \tau(q)=\sum_j s_p(\beta_j)-\sum_i s_p(\alpha_i).
\tag{2.5}
\]

If a length-`T` LSDF word represents `n=sum_(u<T)e_u p^u`, induction in
(2.3) gives the exact final carries

\[
 \boxed{\alpha_i=\lfloor a_i n/p^T\rfloor,\qquad
        \beta_j=\lfloor b_j n/p^T\rfloor.}
\tag{2.6}
\]

Thus these vectors, as `T,n` vary with `0<=n<p^T`, are precisely the
accessible states. Summing emitted digits and then the unflushed high carries
gives

\[
 \sum_{u<T}w(q_u,e_u)+\tau(q_T)
 =\sum_j s_p(b_jn)-\sum_i s_p(a_in).
\tag{2.7}
\]

Legendre's elementary identity
`(p-1)v_p(m!)=m-s_p(m)` and balance therefore give, for the nonzero rational

\[
 R(n)={\prod_i(a_i n)!\over\prod_j(b_j n)!},
\]

the exact finite-word formula

\[
 \boxed{\sum_{u<T}w(q_u,e_u)+\tau(q_T)
       =(p-1)v_p(R(n)).}
\tag{2.8}
\]

No integrality is needed for the rational valuation in (2.8).

Define

\[
 \Phi(q)=\sum_i\alpha_i-\sum_j\beta_j.
\tag{2.9}
\]

For the accessible state (2.6), direct substitution gives the Landau identity

\[
 \boxed{\Phi(q)=\Lambda(n/p^T).}
\tag{2.10}
\]

Expanding (2.5), balance cancels every term linear in `e`, leaving

\[
 \boxed{w(q,e)=p\Phi(q')-\Phi(q).}
\tag{2.11}
\]

For a closed walk `C=(q_0,...,q_l=q_0)`, cyclic reindexing proves

\[
 \boxed{W(C)=(p-1)\sum_{u=0}^{l-1}\Phi(q_u).}
\tag{2.12}
\]

This is the needed potential identity. Crucially, (2.12) sums the potential at
**every** orbit point. One positive point does not control the sign unless an
additional hypothesis, such as all-`n` integrality through Landau
nonnegativity, controls all the other points.

## 3. General periodic state, accessibility, and zero flush

This section proves the periodic-orbit-to-accessible-cycle step without using
T141 or T145. Let `d>=1`, `P=p^d`, `Q=P-1`, and

\[
 x={k\over Q}\in(0,1),\qquad
 k=\sum_{u=0}^{d-1}z_up^u.
\tag{3.1}
\]

The padded repeating base-`p` expansion of `x` displays the digits in the
opposite, MSDF order, but the carry graph reads the block
`z_0,...,z_(d-1)` LSDF. Define

\[
 q_x=(\lfloor a_ix\rfloor_i;\lfloor b_jx\rfloor_j).
\tag{3.2}
\]

After that block, a coefficient-`c` carry `gamma` becomes
`floor((ck+gamma)/P)`. Put `gamma=floor(ck/Q)`. From
`gamma Q<=ck<(gamma+1)Q`, adding `gamma` yields

\[
 \gamma P\le ck+\gamma<(\gamma+1)P,
\]

so the block fixes `gamma`. Hence it fixes `q_x` and gives a length-`d`
closed walk.

The fixed state need not be visibly reachable in `d` steps. An explicit
uniform preperiod is available. Let

\[
 H=\min\{h\ge0:p^h\ge M\},\qquad T=d+H,
 \qquad A=\lceil p^T x\rceil.
\tag{3.3}
\]

For every coefficient `c`, the distance from `cx=ck/Q` to the next **strictly
larger** integer is a positive integer multiple of `1/Q`, hence at least
`1/Q`; this remains true when `cx` itself is integral. Also `A<p^T`: otherwise
`0<1-x<=A/p^T-x<1/p^T`, whereas `1-x=(Q-k)/Q>=1/Q>1/p^T`. Finally,

\[
 0\le A/p^T-x<1/p^T\le1/(PM)<1/(QM).
\tag{3.4}
\]

Thus `floor(cA/p^T)=floor(cx)` for every `c<=M`; by (2.6), the `T` digits of
`A` reach `q_x`. This proves accessibility with preperiod at most

\[
 \boxed{T=d+\lceil\log_p M\rceil.}
\tag{3.5}
\]

For zero input, every carry obeys `gamma -> floor(gamma/p)`. Since
`0<=gamma<M<=p^H`, at most

\[
 \boxed{H=\lceil\log_p M\rceil}
\tag{3.6}
\]

zero digits flush every state to zero. These are uniform bounds, not claims of
minimality.

For completeness, if the access word represents `A`, repeat the period block
`m` times and put

\[
 N_m=A+p^T k{P^m-1\over P-1}.
\tag{3.7}
\]

The resulting length is `T+md`, its final state is again `q_x`, and (2.8)
gives the exact finite-length identity

\[
 \boxed{(p-1)v_p(R(N_m))=(p-1)v_p(R(A))+mW(C_x).}
\tag{3.8}
\]

If all orbit potentials were nonnegative and `Lambda(x)>0`, (2.12) and (3.8)
would give the proposed positive finite-length lower bound. The counterfamily
below shows exactly why that premise is unavailable in the literal question.

## 4. Exact counterfamily and its atoms

For every integer `t>=1`, take

\[
 p=2,\qquad
 a_t=(1^{3t},3^t),\qquad b_t=(2^{3t}),
\tag{4.1}
\]

where exponents denote multiplicities. The lists are nonempty, unequal, and
balanced because `3t+3t=6t=2(3t)`. Here `M=3`, and

\[
 R_t(n)=\left({(n!)^3(3n)!\over((2n)!)^3}\right)^t,
\quad
 \Lambda_t(x)=t\bigl(3\lfloor x\rfloor+\lfloor3x\rfloor
                         -3\lfloor2x\rfloor\bigr).
\tag{4.2}
\]

On `[0,1)`, the complete atom table is

| open atom `I` | width | `Lambda_t(I)` | `d_2(I)` | first witness |
|---|---:|---:|---:|---:|
| `(0,1/3)` | `1/3` | `0` | `3` | `1/7` |
| `(1/3,1/2)` | `1/6` | `t` | `3` | `3/7` |
| `(1/2,2/3)` | `1/6` | `-2t` | `3` | `4/7` |
| `(2/3,1)` | `1/3` | `-t` | `3` | `5/7` |

Every endpoint is a reduced rational with denominator at most `M`. Consecutive
distinct endpoints `r/s<u/v` therefore satisfy

\[
 {u\over v}-{r\over s}={us-rv\over sv}\ge {1\over sv}
 \ge {1\over M^2}={1\over9}.
\tag{4.3}
\]

The actual minimum `1/6` confirms this general interval-width calculation.
For `d=1`, the denominator `2^d-1` is 1. For `d=2`, the grid is
`{0,1/3,2/3,1}` and meets only endpoints of the positive atom. At `d=3`,
`3/7` is strictly between `1/3` and `1/2`. Thus

\[
 \boxed{d_2((1/3,1/2))=3.}
\tag{4.4}
\]

Also

\[
 \boxed{D_2(3)=\min\{d:2^d-1>9\}=4.}
\tag{4.5}
\]

The ratio is not always integral: `R_1(1)=3/4`. This is not a defect in the
example; it isolates the hypothesis absent from the agenda's literal domain.

## 5. Complete accessible graph and cycle calculation

Coefficient-one carries are zero. Equal coefficient-two coordinates remain
synchronized from the zero state. It is therefore lossless to write an
accessible state as `(alpha,beta)`, where `alpha` is the coefficient-three
carry and `beta` the common coefficient-two carry. For `t=1`,

\[
 \Phi(\alpha,\beta)=\alpha-3\beta.
\tag{5.1}
\]

The full Cartesian graph has `3*2^3=24` states, but (2.3) reaches exactly four:

| name | `(alpha,beta)` | `Phi` | digit 0: next/weight | digit 1: next/weight |
|---|---:|---:|---|---|
| `Z` | `(0,0)` | `0` | `Z / 0` | `U / -4` |
| `U` | `(1,1)` | `-2` | `Z / 2` | `V / 0` |
| `V` | `(2,1)` | `-1` | `P / 3` | `V / -1` |
| `P` | `(1,0)` | `1` | `Z / -1` | `V / -3` |

The table follows directly from (2.3) and `w=2Phi'-Phi`; it is not copied
from T141 or T145. The complete simple-cycle list is

| cycle | total | length | mean |
|---|---:|---:|---:|
| `Z -> Z` | `0` | `1` | `0` |
| `V -> V` | `-1` | `1` | `-1` |
| `Z -> U -> Z` | `-2` | `2` | `-1` |
| `P -> V -> P` | `0` | `2` | `0` |
| `Z -> U -> V -> P -> Z` | `-2` | `4` | `-1/2` |

Every closed walk decomposes into simple cycles, with its mean a
length-weighted average. Therefore

\[
 \boxed{\mu_+(2;a_1,b_1)=0.}
\tag{5.2}
\]

For multiplicity `t`, every potential, edge weight, terminal weight, and cycle
mean is multiplied by `t`, while the aggregate accessible graph is unchanged.
Consequently

\[
 \boxed{\mu_+(2;a_t,b_t)=0\quad(t\ge1).}
\tag{5.3}
\]

## 6. The periodic orbit, transients, and finite valuations

For the positive atom choose `x=3/7`, with padded binary block `k=3=011_2`.
The LSDF block is `1,1,0`. Its inverse-branch orbit is

\[
 {3\over7}\xrightarrow{1}{5\over7}
 \xrightarrow{1}{6\over7}\xrightarrow{0}{3\over7}.
\tag{6.1}
\]

The corresponding state cycle and potentials for `t=1` are

\[
 P\xrightarrow{1}V\xrightarrow{1}V\xrightarrow{0}P,
 \qquad (1,-1,-1).
\tag{6.2}
\]

Thus (2.12) gives

\[
 \boxed{W(C_x)=t(1-1-1)=-t,
        \qquad \operatorname{mean}(C_x)=-t/3.}
\tag{6.3}
\]

This is the named mechanism of failure: **periodic-orbit sign loss**. The
positive atom controls the first potential only; the next two orbit points lie
in negative atoms.

The same block accesses `P` from zero:

\[
 Z\xrightarrow{1}U\xrightarrow{1}V\xrightarrow{0}P.
\tag{6.4}
\]

Hence the exact preperiod is 3 here, improving the general bound
`d+ceil(log_2 3)=5`. One zero digit sends `P` to `Z`, improving the uniform
zero-flush bound `ceil(log_2 3)=2`.

After access and `m>=0` cycle repetitions, the digit word is `110` repeated
`m+1` times and represents

\[
 n_m=3{8^{m+1}-1\over7}<2^{3(m+1)}.
\tag{6.5}
\]

The access edge sum is `-t`, the terminal weight at `P` is `-t`, and every
extra cycle has weight `-t`. Formula (2.8) gives the exact finite-length value

\[
 \boxed{v_2(R_t(n_m))=-(m+2)t.}
\tag{6.6}
\]

Appending the one-digit zero flush leaves the represented integer unchanged;
its edge weight is `-t` and the terminal weight becomes zero, reproducing
(6.6) at padded length `3(m+1)+1`.

There is also an exact global finite-length inequality. Legendre gives

\[
 v_2(R_t(n))
 =t\sum_{h\ge1}\Lambda_1(n/2^h).
\tag{6.7}
\]

Equivalently, the elementary factorization

\[
 R_1(n)={\binom{3n}{n}\over\binom{2n}{n}^2}
\tag{6.8}
\]

and the digit-sum identity yield the same rational valuation. Direct carry
induction from the four-state graph shows every terminal-completed path has
nonpositive total: define `G(q)=-tau(q)`, check
`w(q,e)+tau(q')<=tau(q)` on all eight displayed edges, and telescope from
`tau(Z)=0`. Therefore, for every `L>=0`,

\[
 \boxed{\max_{0\le n<2^L}v_2(R_t(n))=0,}
\tag{6.9}
\]

with equality at `n=0`. Thus the correct finite-length lower bound for the
maximum is only `0`; the positive atom supplies no positive drift.

## 7. Refutation of both proposed inequalities

The unique positive atom has height `t` and `d_2=3`, while (5.3) gives
`mu_+=0`. Hence, for every `t>=1`,

\[
 \boxed{0=\mu_+ < {t\over3}
 =(p-1)\max_{\Lambda_t(I)>0}{\Lambda_t(I)\over d_2(I)}.}
\tag{7.1}
\]

Equation (4.5) also refutes the advertised consequence:

\[
 \boxed{0=\mu_+ < {1\over4}={p-1\over D_2(3)}.}
\tag{7.2}
\]

This is not a `1/|V_acc|` estimate. Here `|V_acc|=4`; the usual positive-cycle
integer-weight argument would suggest `1/4` only **after** proving that a
positive accessible cycle exists. It does not exist. Numerically, the proposed
interval estimate `t/3` would even exceed the state-count scale `t/4`, but both
positive conclusions fail because the omitted Landau-nonnegativity premise is
load-bearing.

## 8. Comparison with T133, T141, T143, T145, T146, and T147

The four available comparator reports are delivered byte-for-byte. Their
claims are not premises. Sketch-level notes remain unverified comparison
memory.

| Item and delivered SHA-256 | Level and mechanism | T148 boundary |
|---|---|---|
| T133, `53a1c70ff1fe9d91cc21f9044372a0ecca96567654ae1b6e3e04955be69c9d40` | Its report self-labels a `proof sketch`; it specializes a centered base-5 factorial valuation, minimizes six carries to three classes, and computes exact extrema. | T148 uses a raw binary graph for a balanced rational ratio and refutes a proposed interval-to-cycle inequality. It imports no T133 table, quotient, or arithmetic conclusion. |
| T141, `e7ca132fa2221a46be4f4611f87eb1d25bda036e90ae12c4387e1f08f8c8c356` | The note self-labels an unverified `proof sketch`; it argues for general carry totals, tropical extrema, and accessible-cycle asymptotics. | Motivation only. Sections 2--3 independently derive the graph, terminal formula, potential identity, accessibility preperiod, flush bound, and exact periodic finite-length identity. |
| T143, `b446b83025fd408fdbc8580e0e6871ab514ad169b0fe1d33407f6ad9061ca0d9` | The note self-labels a `proof sketch`; it minimizes a fixed weighted transducer by terminal-normalized residual equivalence and argues that cycle means lift through powers. | T148 performs no minimization. T143-style quotienting preserves existing cycle means and therefore cannot turn this graph's `mu_+=0` into positive drift. The direct atom claim fails before minimization is relevant. |
| T145, `17774f8020ddba63203d2a956e1edbd3e2d432a32cafde11386d35a3514d229c` | The note self-labels a `proof sketch`; under all-`n` integrality it argues that Landau potentials are nonnegative and unequal multisets force a positive accessible cycle. | T148 pinpoints that integrality is absent from its literal assumptions. Its counterfamily has `R_1(1)=3/4`, negative Landau atoms, and a positive point whose periodic orbit has negative total. There is no contradiction with T145's narrower hypothesis. |
| active T146 | The agenda names it active and the byte-pinned `active-items-snapshot.txt` records its lease metadata, but the refreshed supplied record contains no T146 artifact, result, title, or mathematical fingerprint. | Availability boundary only. No theorem, novelty, or duplication claim is inferred. |
| active T147 | The agenda names it active and the byte-pinned `active-items-snapshot.txt` records its lease metadata, but the refreshed supplied record contains no T147 artifact, result, title, or mathematical fingerprint. | Availability boundary only. No theorem, novelty, or duplication claim is inferred. |

The duplication boundary is exact: T148 reuses only the general subject of
multiplication carries. Its new scoped content is the literal-assumption audit,
the exact counterfamily, and the periodic-orbit sign-loss diagnosis.

## 9. Separate fixed-pi firewall

Any transfer from this coefficient model to fixed pi would still require an
entirely unproved package, stated here only to prevent accidental inference:

1. a proved exact pi representation by relevant rational coefficients;
2. truncation error uniform after multiplication by all `10^i-10^j` in the
   chosen prefix;
3. complete reduced-numerator and cancellation control;
4. consumption of every power-of-2 and power-of-5 decimal transient;
5. a lower bound for the multiplicative order of 10 modulo the surviving
   coprime modulus;
6. ordered, diagonal-inclusive metric occupancy at a length
   `N asymp log q`, with the canonical strict cutoff.

No clause is proved or asserted to hold. The counterfamily is not a
representation of pi. This note makes no fixed-pi, A1, C1, C2, or other
program-conjecture claim.

## 10. Self-contained replay and evidence boundary

From a directory containing only the delivered files, run

```bash
python3 verify_t148.py
sha256sum -c SHA256SUMS
```

The script uses exact integer and rational arithmetic. It hash-checks the
canonical statement, active-item snapshot, and all available comparator
reports; reconstructs every atom, width, `d_2`, carry state, edge, terminal,
simple cycle, access path, periodic orbit, and flush; checks the Landau and
terminal-completed path identities on bounded inputs, checks (6.6), verifies
counterfamily scaling for bounded positive `t`, and validates that valuations
are nonpositive for `0<=n<4096`. These finite checks are an
`experiment`, not the proof. Sections 2--7 contain the universal derivation and
exact counterfamily argument.

## 11. Sole endpoint

SCOPED_VERDICT: EXACT COUNTERFAMILY
