# Uniform-integrability frontier for the decimal orbit

Status: `proof sketch`

This note proposes a weakening of the moving-mesh collision premise recorded in `FRONTIER.md`.
It does **not** prove decimal richness for `π`. It replaces a uniform second-moment requirement by a weaker and more directly targeted tail-nonconcentration requirement.

## 1. Setup

Let

\[
\mathbb T=\mathbb R/\mathbb Z,
\qquad
T_b(x)=b x\pmod 1,
\qquad b\ge 2,
\]

and let an exact base-`b` orbit be

\[
x_{n+1}=T_b(x_n).
\]

For each `j`, choose a consecutive block

\[
B_j=\{A_j,A_j+1,\ldots,A_j+L_j-1\},
\qquad L_j\longrightarrow\infty,
\]

and partition the circle into `q_j` equal half-open cells

\[
I_{j,a}=[a/q_j,(a+1)/q_j),
\qquad 0\le a<q_j,
\qquad q_j\longrightarrow\infty.
\]

Write

\[
n_j(a)=\#\{n\in B_j:x_n\in I_{j,a}\}
\]

and define the block empirical measure

\[
\mu_j=\frac1{L_j}\sum_{n\in B_j}\delta_{x_n}.
\]

Spread the mass in each cell uniformly over that cell. The resulting probability density is

\[
f_j(x)=\frac{q_j n_j(a)}{L_j}
\quad\text{for }x\in I_{j,a},
\]

and the corresponding absolutely continuous measure is

\[
\nu_j=f_j\,d\lambda,
\]

where `λ` is Haar measure on the circle.

## 2. New hypothesis

The cell densities are **uniformly integrable** when

\[
\boxed{
\lim_{M\to\infty}
\sup_j
\int_{\{f_j>M\}}f_j\,d\lambda
=0.
}
\tag{UI}
\]

In terms of the integer cell counts, this is exactly

\[
\boxed{
\lim_{M\to\infty}
\sup_j
\frac1{L_j}
\sum_{\substack{0\le a<q_j\\
 n_j(a)>M L_j/q_j}}
n_j(a)
=0.
}
\tag{UI-counts}
\]

Thus the new target does not ask for a bound on every collision. It asks only that cells whose occupancy is an arbitrarily large multiple of the mean occupancy carry an asymptotically negligible fraction of all visits.

## 3. The theorem

### Theorem (uniform-integrability criterion)

Assume

1. `L_j → ∞`;
2. `q_j → ∞`;
3. the orbit is exact: `x_{n+1}=T_b(x_n)`;
4. `(UI)` holds.

Then

\[
\mu_j\Longrightarrow\lambda.
\]

Consequently these selected block empirical measures converge to Haar measure.
This does not assert ordinary prefix equidistribution of the full orbit. It does
imply that every nonempty open interval is visited somewhere in the selected
blocks, and for `b=10` every finite decimal word occurs.

No separate assumption that `q_j/L_j` is bounded is required.

## 4. Proof

### Step 1: smearing changes no weak limit

Let `φ : 𝕋 → ℂ` be continuous and let `ω_φ` be its modulus of continuity. Every point is moved by at most one cell width when its mass is spread uniformly inside its cell. Therefore

\[
\left|
\int\varphi\,d\mu_j-
\int\varphi\,d\nu_j
\right|
\le
\omega_\varphi(1/q_j).
\]

Since `q_j → ∞`, the right-hand side tends to zero. Hence `μ_j` and `ν_j` have exactly the same weak subsequential limits.

### Step 2: uniform integrability makes every weak limit absolutely continuous

Condition `(UI)` implies uniform absolute continuity of the measures `ν_j` with respect to Haar measure.

Indeed, fix `ε>0`. Choose `M` so that

\[
\sup_j\int_{\{f_j>M\}}f_j\,d\lambda<\varepsilon/2.
\]

For every measurable set `E`,

\[
\nu_j(E)
=\int_E f_j\,d\lambda
\le
M\lambda(E)
+
\int_{\{f_j>M\}}f_j\,d\lambda.
\]

Thus, whenever `λ(E)<ε/(2M)`, one has `ν_j(E)<ε` uniformly in `j`.

Now take any weakly convergent subsequence `ν_{j_r} ⇒ ν`. If `K` is compact with `λ(K)=0`, choose an open set `O⊃K` with arbitrarily small Haar measure and a continuous function `0≤φ≤1` equal to `1` on `K` and supported in `O`. Then

\[
\nu(K)
\le
\int\varphi\,d\nu
=
\lim_{r\to\infty}
\int\varphi\,d\nu_{j_r}
\le
\sup_r\nu_{j_r}(O).
\]

The uniform absolute-continuity estimate makes the last quantity arbitrarily small. Hence `ν(K)=0`. By regularity, `ν≪λ`.

Therefore every weak subsequential limit of `μ_j` has an `L¹` density with respect to Haar measure.

### Step 3: every weak limit is `T_b`-invariant

For every continuous `φ`, exact orbit evolution gives the telescoping identity

\[
\int \varphi\!\circ T_b\,d\mu_j
-
\int \varphi\,d\mu_j
=
\frac{
\varphi(x_{A_j+L_j})-
\varphi(x_{A_j})
}{L_j}.
\]

Its absolute value is at most `2‖φ‖∞/L_j`, which tends to zero. Hence every weak subsequential limit `ν` is `T_b`-invariant.

### Step 4: Haar is the only absolutely continuous invariant probability

Write `dν=f dλ` with `f∈L¹(𝕋)`. For `h∈ℤ`, let

\[
\widehat\nu(h)=
\int_{\mathbb T}e^{-2\pi i h x}\,d\nu(x).
\]

`T_b`-invariance gives

\[
\widehat\nu(h)=\widehat\nu(bh).
\]

Iterating,

\[
\widehat\nu(h)=\widehat\nu(b^r h)
\qquad(r\ge0).
\]

For `h≠0`, the Riemann-Lebesgue lemma applied to `f∈L¹` gives

\[
\widehat\nu(b^r h)\longrightarrow0.
\]

Therefore `\widehat\nu(h)=0` for every nonzero `h`, while `\widehat\nu(0)=1`. Density of trigonometric polynomials in `C(𝕋)` now gives `ν=λ`.

Every subsequential limit is Haar, so the full sequence satisfies

\[
\mu_j\Longrightarrow\lambda.
\]

This proves the theorem.

## 5. The previous collision premise implies `(UI)`

The old moving-mesh route assumes constants `C,K<∞` such that

\[
\sum_{a<q_j}n_j(a)^2
\le
C\left(\frac{L_j^2}{q_j}+L_j\right)
\tag{C2}
\]

and

\[
q_j/L_j\le K.
\]

For the smeared density,

\[
\int f_j^2\,d\lambda
=
\frac{q_j}{L_j^2}
\sum_{a<q_j}n_j(a)^2
\le
C(1+K).
\]

Therefore

\[
\int_{\{f_j>M\}}f_j\,d\lambda
\le
\frac1M\int f_j^2\,d\lambda
\le
\frac{C(1+K)}M.
\]

So `(C2)` plus bounded `q_j/L_j` implies `(UI)`.

The new premise is therefore no stronger than the previous collision premise.

## 6. Histogram-level separation from the second moment

The converse fails even for genuine integer histograms.

For every integer `j≥2`, set

\[
q_j=j^3,
\qquad
L_j=j(q_j-1),
\]

and define cell counts by

\[
n_j(0)=q_j-1,
\qquad
n_j(a)=j-1
\quad(1\le a<q_j).
\]

These are nonnegative integers and

\[
\sum_{a<q_j}n_j(a)
=(q_j-1)+(q_j-1)(j-1)
=j(q_j-1)
=L_j.
\]

The normalized density on cell `0` is

\[
\frac{q_j n_j(0)}{L_j}=j^2,
\]

while the density on every other cell is

\[
\frac{q_j(j-1)}{j(q_j-1)}<1.
\]

The spike carries mass

\[
\frac{n_j(0)}{L_j}=\frac1j.
\]

Hence, for every `M>1`,

\[
\sup_j
\int_{\{f_j>M\}}f_j\,d\lambda
\le
\frac1{\sqrt M}.
\]

Thus `(UI)` holds.

But the `L²` norm diverges, because the contribution from the spike cell alone is

\[
\int f_j^2\,d\lambda
\ge
\frac1{q_j}(j^2)^2
=j.
\]

Therefore no uniform second-moment bound can hold. Also

\[
q_j/L_j
=
\frac{j^3}{j(j^3-1)}
\longrightarrow0,
\]

so the failure is not caused by an excessive mesh-to-block ratio.

This is an explicit separator among integer histograms:

\[
\boxed{
\text{uniform integrability does not imply a uniform }L^2
\text{ collision bound.}
}
\]

This histogram alone does not impose exact dynamics. Exact-orbit strictness is
supplied next.

### Exact decimal-orbit separator

Use Separator B from
[`20260824-entropy-deficit-haar-hierarchy.md`](20260824-entropy-deficit-haar-hierarchy.md).
At decimal scale `q=10^k`, concatenate a zero run of length
`z=floor(q/k)` with a linearized decimal de Bruijn word, include the `k-1`
transition windows, and embed these stages at disjoint positions of one
nonterminating decimal expansion. The resulting selected blocks obey the exact
times-ten dynamics and may be placed in literal intervals `[L_j,2L_j)`.

Their relative entropy deficits are uniformly bounded. For any cell-smoothed
density `f` with `D=integral f log f`, the negative part of `t log t` contributes
at most `1/e`; hence

```text
integral_(f>M) f <= (D + 1/e) / log M.
```

Thus these exact-orbit blocks satisfy uniform integrability. On the other hand,
the zero-word cell has mass at least `z/M_block`, so the same construction has
`q * sum_a p(a)^2 -> infinity`. Therefore no uniform collision/`L^2` bound can
hold. This supplies strictness inside the shared exact-decimal-orbit domain,
not merely among abstract histograms.

## 7. New fixed-`π` target

For the actual decimal orbit

\[
x_n=\{10^n\pi\},
\]

it is now enough to find consecutive blocks and meshes with `L_j,q_j→∞` for which

\[
\boxed{
\lim_{M\to\infty}
\sup_j
\frac1{L_j}
\sum_{\substack{a<q_j\\
 n_j(a)>M L_j/q_j}}
n_j(a)
=0.
}
\]

This is a tail estimate, not a second-moment estimate. It permits rare cells with very large occupancy, provided those cells carry a vanishing fraction of the visits.

Possible inputs that would establish it include, but are not limited to:

- any uniform `L^p` bound for some fixed `p>1`;
- an entropy bound strong enough to imply uniform integrability;
- a direct occupancy-tail inequality;
- a truncated collision estimate controlling only cells above a moving threshold.

A future contribution should target one of those statements for the fixed orbit of `π`, rather than rebuilding the already-complete consumer argument.

## 8. Claim boundary

This note gives a `proof sketch` of a new generic implication. The collision
premise implies its uniform-integrability premise. The integer histogram gives
the basic analytic nonconverse, and the reviewed de Bruijn construction above
gives strictness inside exact decimal dynamics.

It does **not** prove that the decimal orbit of `π` satisfies `(UI)`. The remaining frontier is still a fixed-`π` quantitative nonconcentration estimate.
