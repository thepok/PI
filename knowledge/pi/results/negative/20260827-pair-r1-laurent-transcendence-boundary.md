# Pair-R1 Laurent-polynomial transcendence boundary

Date: 2026-08-27 UTC

Claim labels: the specialization of the registered T138/T177/T179 formulas
and the elementary DFT/transcendence deductions are `proof sketch`; the cited
source statements were checked against primary sources.  The actual-pi node
separator below is an `experiment`.  Uniform Pair-R1 is refuted; no pathwise
signed transport theorem for pi is proved.

## Exact finite carrier

Put `Q=10q`, `z=exp(2*pi^2*i)`, and
`zeta=exp(2*pi*i/(20q))`.  For a fresh horizon block `H>N`, T179 gives the
unnormalized predecessor-sector increment

```text
C_r = sum_(0<=ell<2q) sum_(N<=n<H)
  b_(r,ell) * z^((10ell+r)*10^n),

b_(r,ell)=10*a_(Q,10ell+r)*zeta^(-(10ell+r)*(2A+1)).
```

Here `a_(Q,h)` is the positive boundary coefficient and
`b_(r,ell)` lies in the cyclotomic field `K_q=Q(zeta_(20q))`.  For
`1<=r<=4`, define `P_r=C_r+conj(C_(10-r))`; for `r=5`, use the self-pair
`P_5=C_5+conj(C_5)`.  Since `conj(z)=z^(-1)`, each `P_r` is

```text
P_r=L_(q,A,N,H,r)(z),
L_(q,A,N,H,r) in K_q[X,X^(-1)].
```

The Laurent polynomial is formally nonzero.  Its positive monomial
`X^(r*10^N)` is unique by ten-adic valuation and has nonzero coefficient by
T138/T142 positivity; the conjugate half has negative exponents.  This proves
`L_r!=0` as a formal polynomial, **not** `L_r(z)!=0`.

At the natural block `N=q`, `H=10q`, the pair has at most `36q^2` formal
terms.  Clearing negative exponents produces degree less than

```text
40q*10^(10q-1).
```

Thus even a generic degree-dependent transcendence measure would operate at
a scale vastly below Pair-R1's required `O(1/q)` inequality.

## What unconditional transcendence theory supplies

The number `z` is not a root of unity: `z^m=1` would imply `m*pi` is an
integer.  Hence it is not rational.  The bounded PaperSearch and primary
source audit found no theorem proving whether `z=exp(2*pi^2*i)` is algebraic
or transcendental.  Lindemann--Weierstrass does not apply because its
exponent is transcendental; Gelfond--Schneider does not apply to
`(-1)^(2*pi)` because the exponent is not algebraic; Baker theory does not
allow the resulting transcendental logarithmic coefficient.  The analogous
status of `exp(pi^2)` is discussed in
[Waldschmidt's survey](https://arxiv.org/abs/math/0502582).

Schanuel's conjecture would imply that `z` and `pi` are algebraically
independent: apply it to the Q-linearly independent numbers `2*pi*i` and
`2*pi^2*i`.  This remains conditional and would yield only qualitative
nonvanishing of `L_r(z)`, not a quantitative Pair-R1 margin or target sign.

There is one unconditional two-term fragment.  From
[Zeilberger--Zudilin's](https://arxiv.org/abs/1912.06345) bound
`mu(pi)<=7.103205334137...`, every fixed
`mu>7.103205334137...` admits `c_mu>0` such that, for `m>=1` and `u!=v`,

```text
|z^u-zeta_m^s*z^v|
  >= 4*c_mu*m^(-mu)*|u-v|^(1-mu).
```

This follows by reducing the left side to the distance of
`(u-v)*pi-s/m` from an integer.  It controls equal-amplitude cyclotomic
binomials only.  It does not prevent cancellation among the `O(q^2)` terms
of `L_r`, and exponential exponent gaps make it far smaller than `1/q`.

## Literal coefficient no-gos and the parity factor

Two further exact-coefficient observations narrow the live route. Each
coefficient `b_(r,ell)` repeats across all `9q` fresh horizons, so no single
formal monomial or single horizon slice can dominate the sum of all remaining
coefficient magnitudes. Also, with

```text
s=q/gcd(2A+1,q),
b_(r,ell+s)/b_(r,ell) < 0
```

whenever both indices occur. Thus no scalar rotation puts all literal
coefficients in one open positive half-plane. These are coefficient-level
no-gos only; evaluated actual-π phases could still compensate them.

The self-paired residue `r=5` has the exact real factorization, for `Q=10q`
and `alpha_Q=1-cos(pi/Q)`,

```text
K_(Q,5)(t) = (1/10) F_q(10t)^2 cos(10*pi*t)
  * ((1+8*alpha_Q) cos(20*pi*t)-1+92*alpha_Q).
```

Equivalently the final zero is at
`beta_Q=(1-92*alpha_Q)/(1+8*alpha_Q)`. Both real factors change sign, so this
identity exposes the literal parity/suffix weight but supplies no π-specific
sign or Pair-R1 margin.

## Disposition

### Actual-pi positive-node separator

A standalone directed-interval `experiment`, independently reproduced with a
second interval engine, evaluates the correctly conjugated pairs
`P_r=C_r+conj(C_(10-r))` at `(q,A,N,H)=(1000,689,1000,10000)`.  The replay is
[`t189_pair_dc1_counterexample_interval.py`](../../../../workflows/experiments/t189_pair_dc1_counterexample_interval.py).
It certifies the positive parent margin `B(q,A,q)>80.21738`, while all five
Pair-R1 margins are negative (between `-6.71` and `-6.21`) and the DC1 right
side is below `-7199.92697`.  Yet the full same-child statistic has the unique
FMR witness

```text
D_8 > 12295.03615,       G_8+D_8 > 11062.69343.
```

Thus the complete fresh block can obtain its favorable digit from coherent
interference among several character sectors even when every individual pair
and the first-sector decagon envelope fail.  This refutes uniform Pair-pi and
universal actual-pi positivity of the DC1 premise.  It does not refute FMR,
the deterministic DC1 inequality, or a pathwise theorem that constructs
favorable nodes from independent arithmetic.

### Parity-neutral convex separator

A later independent high-precision `experiment` follows the legal root edge
`(1000,334) --d=1--> (10000,1334)`. At the reached positive node, `d=5` is
the unique FMR witness, all ten cyclic adjacent averages of `Y_d` are
negative, and every convex mask annihilating predecessor sector `r=5` is
negative. In detail, the reproduced extrema are

```text
max_(d even) Y_d = -93553.778220620540...
max_(d odd)  Y_d =  67157.356680355889...
```

so a parity-balanced mask is at most `-13198.210770132325...`. Any positive
convex mask at this node must retain sector 5 with
`mu5=sum_d w_d*(-1)^d < -0.164247620779...`.

The signs were reproduced by independent 60-decimal, double, and extended
precision implementations. The original Pro memo's claimed sub-`10^-6`
directed intervals were not reproduced and are rejected; this remains an
`experiment`, not a certificate. The compact replay and the surviving exact
sector-5 direction are recorded in
[`20260828-sector5-odd-frequency-machin-direction.md`](../intermediate/20260828-sector5-odd-frequency-machin-direction.md).

There is a sharper but still carefully scoped five-block statement. Write the
ten real child values as `y in R^10`, let `V_j` be the two-dimensional real
character space belonging to sector pair `j`, and let `W_j` be the simplex of
convex digit masks annihilating that pair. Finite-dimensional LP duality gives

```text
max_(w in W_j) w dot y = min_(v in V_j) max_d (y_d+v_d).
```

Independent vertex enumeration at the same hard node gives the five deletion
optima

```text
M_1=M_3=M_5 = -13198.2107701325...,
M_2           = -29421.8421648713...,
M_4           = -24014.0645848527...
```

Thus every convex-mask certificate which annihilates any one complete real
character block fails at this node (`experiment`). This does **not** show
that every block is necessary for an arbitrary actual-orbit theorem: the LP
allows all algebraic completions in the missing conjugate DFT pair, and no
orbit-admissibility theorem says that all such completions are realizable.
The durable conclusion is only that a reduced convex-mask proof must add a
genuine cross-sector admissibility relation rather than delete a block.

A later antipodal Fejér-collapse attempt does not apply to this carrier. It
replaces the literal frequency-dependent T142 boundary coefficient by a
triangular surrogate, and its original version also used the wrong center and
horizon. Even after correcting the center and choosing the unique scalar that
matches the outer endpoint, the literal residue mask and the Fejér surrogate
have an explicit common-zero separator: for every `q>=1000` there is `t_q`
where the surrogate is zero while the real literal T179 sector is `>1/26`;
on a punctured neighborhood their signs are opposite (`proof sketch`). Thus
no scalar normalization or Chebyshev sign selector transfers the artificial
collapse to the literal carrier. The constructed point is free, not an
actual-pi orbit estimate.

The literal all-residue cubic factorization also does not orient a local
same-digit term. For any target and compatible common `Q=10q` digit prefix
ending in a candidate digit, two eventually periodic completions can keep
every inherited `G_e` (hence every deficit) within
`(1414*pi/9)*q*10^(-9q)` while the final same-digit paired summand has opposite
nonvanishing boundary-layer limits (`proof sketch`). This concerns only the
last summand, not the complete fresh block, so it is a separator for robust
local-orientation arguments rather than an FMR counterexample. Actual-pi
control of the ordered fresh suffixes is still missing.

The algebraic encoding is exact, but generic nonvanishing or transcendence is
not the missing arithmetic input and the uniform Pair-R1 target itself is now
closed.  Reopening a paired-sector argument requires a genuinely pathwise
actual-pi mechanism that selects favorable nodes and also supplies same-digit
R2 alignment.  The active target is instead complete same-child or genuinely
multi-sector signed transport.
