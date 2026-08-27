# T130 canonical pair-escape census

Status: `experiment`

Exact finite arithmetic falsifies the tested coarse one-step escape rules and
fixed escape horizons through five.  It proves no eventual bound, density,
infinitude, T130, T125, or V1 claim.

V1 remains open.

## Frozen definitions

The census uses the registered inclusive BBP prefix

```text
A_N=sum_(k=0..N) 16^(-k)nu_k/D_k,
q_j=10^j-16,
eps_j=(5/8)^j/[15(j+1)^2].
```

Centering is half-open in `[-1/2,1/2)`.  Put

```text
delta_(N,i)=q_(N+i)(A_(N+i)-A_N),
ell_N=min{i>=1:delta_(N,i)>=1/4},
J_N=N+ell_N.
```

Let `G_j` be the strict rational sufficient hit

```text
|center_1(q_j A_j)| < 1/4-eps_j.
```

The pair state `N` is called bad, or `O_N`, when both `G_(J_N-1)` and
`G_(J_N)` fail.  This is equivalently evaluated through the audited minimal
closed coordinate

```text
barM_N=M_N/48,
e_N=(S_N-191M_N/64) mod barM_N.
```

For transition labels use

```text
rho_N=Lambda_(N+1)/Lambda_N,
a_N=16rho_N,
u_(N+1)=nu_(N+1)Lambda_(N+1)/D_(N+1),
h_N=J_(N+1)-J_N in {1,2}.
```

The fresh-coset quarter is

```text
floor(4*(u_(N+1) mod a_N)/a_N) in {0,1,2,3}.
```

## Exact one-step census, `6<=N<=512`

There are 101 bad pair states.  Among the 506 in-range transitions
`6<=N<512`, exactly 44 are bad-to-bad.  The out-of-range transition
`512->513` is also bad-to-bad but is excluded from that count.

The in-range bad-to-bad transitions split as follows:

| Label | Counts |
|---|---:|
| `h_N=1 / h_N=2` | `39 / 5` |
| `rho_N>1 / rho_N=1` | `27 / 17` |
| fresh quarter `0 / 1 / 2 / 3` | `12 / 15 / 11 / 6` |

Exact smallest witnesses are:

| Falsified universal escape rule | First bad-to-bad `N` | Exact label data |
|---|---:|---|
| every bad pair escapes next | 6 | `h=1`, `rho=1891` |
| `h=1` forces escape | 6 | — |
| `h=2` forces escape | 168 | — |
| a branch switch forces escape | 60 | `h_59=2`, `h_60=1` |
| no branch switch forces escape | 6 | — |
| `rho=1` forces escape | 7 | — |
| `rho>1` forces escape | 6 | — |
| fresh quarter 0 forces escape | 6 | `(u mod a,a)=(5656,30256)` |
| fresh quarter 1 forces escape | 60 | `(u mod a,a)=(6,16)` |
| fresh quarter 2 forces escape | 7 | `(u mod a,a)=(11,16)` |
| fresh quarter 3 forces escape | 207 | `(u mod a,a)=(25405,26704)` |

The longest bad runs in this range have length five, at `168..172` and
`335..339`.

These witnesses refute only the enumerated categorical universal rules.  They
do not exclude finer full-composite subclasses, eventual rules, multi-step
arguments, or claims using the complete canonical history.

## Predeclared bad-run extension, `6<=N<=1024`

The extended exact census contains 244 bad states.  Its unique longest bad run
is

```text
874..879
```

of length six.  The six length-five runs are

```text
168..172, 335..339, 518..522,
627..631, 715..719, 938..942.
```

The endpoint `N=1024` is good, so the run ledger is not right-truncated.
With

```text
B(N)=min{L>=0: O_(N+L) fails},
```

the census proves only the finite fact `B(874)=6`.  Thus every proposed
universal fixed escape horizon `H<=5` has an exact counterexample.  No claim is
made for `H>=6`.

## Reproducibility and audit

The primary implementation used exact reduced rational prefixes and direct
half-open centering.  An independent audit rebuilt the canonical `S_N,M_N`
recurrence and evaluated every pair both as `q_jS_j mod M_j` and through
`e_N mod M_N/48`; the results agreed at every index.

The audit also checked at every row:

- minimality of `ell_N` and `J_(N+1)-J_N in {1,2}`;
- `48|M_N` and the exact `e_N` recurrence;
- the selector identities for both pair phases;
- strict rational epsilon margins and the half-open center rule.

There were no half-center ties, epsilon-boundary equalities, or
`delta=1/4` equalities in either declared range.

## Directional conclusion

The coarse one-step/switch/`rho`/quarter portfolio is retired.  The remaining
canonical question is global bad-run exclusion for the actual growing-modulus
state `e_N`, using the full selected prefix and the complete sequence of fresh
numerators.  Finite enumeration supplies no such theorem.
