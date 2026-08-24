# Exact current interface (2026-08-24)

Let `x_n=fract(10^n*pi)` and
`S_h(N)=sum_(n<N) exp(2*pi*i*h*x_n)`. For Jackson order `q`, the verified raw
load `L_raw` sums `|c_i||S_(h_i)|/N` over nonzero Jackson indices. Grouping
equal frequencies gives real coefficients
`A_q(h)=sum_(i:h_i=h)c_i` and

```text
L_agg(q,N)=sum_(h!=0) |A_q(h)| |S_h(N)|/N,
L_agg <= L_raw.
```

An empty interval `[a,a+1/q)` forces both loads above

```text
c_q = 1/(3q)+2/(3q^3).
```

The target-centered signed defect is

```text
D(q,N,a) = -(1/N) Re sum_(h!=0)
  A_q(h) exp(-2*pi*i*h*(a+1/(2q))) S_h(N).
```

Lean verifies `D<=L_agg`; an empty target interval forces `D>=c_q`. Hence the
wordwise premise `forall nonempty words s, exists N_s>0: D(10^|s|,N_s,a_s)<c_q`
implies V1. None of these pi premises is known.

The generic selected-block route partitions a consecutive block of length `L`
into `q` cells with counts `n(a)` and cell-smoothed density
`f=q*n(a)/L`. Uniform integrability means

```text
lim_(M->infinity) sup_j (1/L_j)
  sum_(a: n_j(a)>M*L_j/q_j) n_j(a) = 0.
```

For exact times-ten dynamics, `L_j,q_j->infinity` plus this condition makes the
selected block measures converge to Haar and therefore implies V1. It does not
imply ordinary prefix equidistribution. The older collision condition
`sum n(a)^2 <= C*(L^2/q+L)` with bounded `q/L` implies uniform integrability.
Exact decimal de Bruijn stages separate the converse. No such tail estimate is
proved for pi.

Useful proof-sketch coefficient facts, to be checked rather than blindly
assumed: `A_q(h)>0` on `|h|<=2q-1`, `A_q(0)=c_q`, and
`sum_h A_q(h)=2`. The exact orbit identity is
`S_(10h)(N)=S_h(N)+exp(h*x_N)-exp(h*x_0)`.

No task may claim fixed-pi cancellation, density, normality, V1, or novelty
without actually proving the universal fixed-pi quantifiers.

