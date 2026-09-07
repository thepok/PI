# An exact-integer certificate for the two-digit Parry row-norm obstruction

## Result and scope

For every decimal forbidden word `ab` of length two, let `lambda` be the Perron eigenvalue of its two-state prefix automaton. Let `C_M` be the exact shifted terminal-state row norm in the question. The certificate and the analytical argument below prove

\[
 C_M\geq \left(\frac{291}{20\lambda}\right)^M
 >\left(\frac{1455}{991}\right)^M>10^{M/6}
 \qquad (M\geq1).
\]

Thus no finite block length satisfies the proposed contraction, for any of the 100 words. This is NOT a nonexistence theorem for positive-dimensional fixed-kappa BA--ALA sets. It rules out the specified clean-block Parry row-norm criterion. It does not assert a lower bound for the scalar Fourier transform of the final guarded measure, where additional cancellations might matter.

The one-step lemma below is computer-assisted, using integer arithmetic with a proved trigonometric error budget. The passage from that lemma to every block length is analytical. No FFT or floating-point operator estimate is used in the certificate.

## Reproduction

Requires a C++17 compiler supporting 128-bit integers, such as GCC or Clang. No external libraries are needed.

```sh
g++ -O3 -std=c++17 -fno-fast-math certify.cpp -o certify
./certify > reproduced.csv
cmp certificate.csv reproduced.csv
```

A single word or an inclusive range can also be certified:

```sh
./certify 49
./certify 0 49
./certify 50 99
```

Every word is checked separately with its actual digit phases. The computation does not identify all words having the same overlap type.

The completed run has 100 PASS records, 77,233,788 tree nodes, 38,616,944 leaves, 215,488 leaves covered by the analytic outside-disk estimate, and maximum total subdivision depth 35. The smallest recorded positive box margin is exactly

\[
\frac{421592800}{140737488355328000}.
\]

This is the remaining box margin AFTER subtracting the full trigonometric error budget and the full box-variation bound, not an uncorrected floating-point sample margin. Both `49` and `50` attain this recorded minimum. All 100 result records were reproduced with the final source.

## 1. The unweighted automaton

Write `e(t)=exp(2*pi*i*t)`, `S(t)=sum_{d=0}^9 e(-dt)`, and `E_d(t)=e(-dt)`.

For `a=b`, the digit-counting Fourier matrix is

\[
 T_{aa}(t)=\begin{pmatrix}S(t)-E_a(t)&E_a(t)\\S(t)-E_a(t)&0\end{pmatrix}.
\]

For `a!=b`, it is

\[
 T_{ab}(t)=\begin{pmatrix}S(t)-E_a(t)&E_a(t)\\S(t)-E_a(t)-E_b(t)&E_a(t)\end{pmatrix}.
\]

Set `rho=9/25` and define a norm on complex row vectors by

\[
 N(p_0,p_1)=|p_0+p_1|+\rho(|p_0|+|p_1|).
\]

The certified lemma is

\[
 \sum_{j=0}^9N\left(pT_{ab}\left(\frac{x+j}{10}\right)\right)
 \geq \frac{291}{20}N(p)
 \quad(x\in\mathbb R,\ p\in\mathbb C^2).
\]

The left side is periodic in `x` with period one, so `0<=x<=1` suffices.

## 2. Reduction to three real variables

For `p_0+p_1 != 0`, divide by that sum and write `p=(z,1-z)`. Put

\[
 t_j=(x+j)/10,\qquad
 K_j=\sum_{d\ne a}e(-(d-a)t_j),\qquad
 E_j=e(-(b-a)t_j).
\]

The input norm is

\[
 D(z)=1+\rho|z|+\rho|1-z|.
\]

The numerator of the lemma is, in the repeated-digit case,

\[
 F_{aa}(x,z)=\sum_j|K_j+z|+\rho\sum_j|K_j|+10\rho|z|.
\]

In the distinct-digit case put `V_j=K_j+(z-1)E_j`. Then

\[
 F_{ab}(x,z)=\sum_j|V_j+1|+\rho\sum_j|V_j|+10\rho.
\]

The certificate proves `G=F-(291/20)D >= 0`. Explicitly,

\[
\begin{aligned}
G_{aa}&=\sum_j|K_j+z|+\frac9{25}\sum_j|K_j|
-\frac{819}{500}|z|-\frac{2619}{500}|1-z|-\frac{291}{20},\\
G_{ab}&=\sum_j|V_j+1|+\frac9{25}\sum_j|V_j|
-\frac{2619}{500}(|z|+|1-z|)-\frac{219}{20}\quad(a\ne b).
\end{aligned}
\]

For `p_0+p_1=0`, direct substitution gives the ratio

\[
 \frac{10(1+\rho)}{2\rho}=\frac{170}{9}>\frac{291}{20},
\]

so this omitted affine-chart point is covered analytically.

## 3. The unbounded part of the complex plane

Discrete Fourier inversion gives `sum_j |K_j+z| >= 10|z|` and `sum_j |K_j| >= 10` in the repeated case. In the distinct case, the coefficient of `e(-(b-a)t_j)` in both `V_j` and `V_j+1` is `z`, so each of their shifted absolute sums is at least `10|z|`.

Consequently, in both cases,

\[
 F(x,z)\geq\frac{68}{5}|z|+\frac{18}{5}.
\]

Since `D(z)<=34/25+(18/25)|z|`,

\[
 G(x,z)\geq\frac{781|z|-4047}{250}.
\]

For `|z|>=6`, this is at least `639/250>0`. It remains to cover the compact box

\[
 [0,1]\times[-6,6]\times[-6,6],\qquad z=r+is.
\]

## 4. Proved variation bounds on every box

Parseval on the ten shifted points and Cauchy--Schwarz give

\[
 \sum_j|K'_j(x)|\leq2\pi\sqrt{\sum_{d\ne a}(d-a)^2}
 \leq2\pi\sqrt{285}.
\]

Also `sum_j |E'_j(x)|=2*pi*|b-a|`. The triangle inequality for modulus, with the explicit formulas for `G`, yields the following Lipschitz bounds:

* For `a=b`, use `L_x=146` and `L_z=17`.
* For `a!=b`, use `L_z=25` and, on a box centered at `(x_0,r_0,s_0)` with halfwidths `(h_x,h_r,h_s)`,

\[
 L_x=9\left(17+|b-a|\bigl(|r_0-1|+|s_0|+h_r+h_s\bigr)\right).
\]

These constants follow from `sqrt(285)<17` and `pi<22/7`. For example, the exact complex-variable Lipschitz constants before rounding upwards are `16.876` and `24.076` in the two cases.

Thus throughout the closed box,

\[
 G(x,r+is)\geq G(x_0,r_0+is_0)
 -L_xh_x-L_z(h_r+h_s).
\]

A box is accepted only when its certified center lower bound minus this entire variation allowance is strictly positive. A box entirely outside `|z|<6` is accepted by Section 3. Otherwise the code bisects one coordinate. Every split is checked to be exactly dyadic; no rounding gap in the cover is permitted.

## 5. Why the center bounds are rigorous

All represented real numbers have fixed-point denominator

\[
 S_*=2^{48}=281474976710656.
\]

All centers and halfwidths are exact dyadic rationals. All arithmetic used for acceptance decisions is integer arithmetic; products use signed 128-bit integers. The ranges in this computation are well within that type's capacity.

### Pi

The code uses Machin's elementary identity

\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
\]

and the alternating power series for arctangent. For each retained term it uses the integer part of its value times `S_*`. There are ten nonzero power terms for `1/5` and three for `1/239`. Bounding each truncation by `1/S_*` and each omitted alternating tail by `1/S_*` gives

\[
 \left|\pi-\frac{884279719003552}{S_*}\right|<\frac{192}{S_*}.
\]

The same enclosure verifies `pi<22/7` directly by rational comparison.

### Phases

The rational phase is first reduced modulo a full turn to an angle in `[-pi,pi]`. The fixed-point angle differs from the exact reduced angle by less than `193/S_*`. Sine and cosine are evaluated with the first 21 Taylor terms using fixed-point multiplication and integer division. Each elementary multiplication/division truncation is at most `1/S_*` in represented real value.

Here is a deliberately loose but sufficient error audit. With `Z` the rounded square of the angle, `0<=Z<10` and `|Z-theta^2|<1/S_*`. Each recurrence stage contributes less than `2/S_*` of rounding error. For cosine, after the first stage the propagation multiplier is at most `10/12=5/6`, so every term error is less than `12/S_*`; summing twenty such errors costs less than `240/S_*`. For sine the analogous sum costs less than `80/S_*`. On `0<=Z<=10`, the absolute derivative sums of the relevant Taylor polynomials with respect to `Z` are less than 10. The omitted Taylor remainders are less than `1/S_*`; for example

\[
 (22/7)^{42}/42!<2^{-48}.
\]

Combining these estimates gives substantially less than `1000/S_*` error per coordinate. The certificate's error accounting permits the still larger bound `10000/S_*` per sine/cosine coordinate.

### Absolute values and the complete G evaluation

`hyp(a,b)` returns `floor(sqrt(a^2+b^2))` exactly. A floating-point square root proposes a candidate, but integer comparisons and correction loops verify the defining inequalities. Its floating-point value is never trusted as a bound.

Each computed coordinate of `K_j` has error at most `90000/S_*`. In the certified square, `|Re(z-1)|<=7` and `|Im(z)|<=6`; hence each computed coordinate of `V_j` has error at most `220002/S_*`. The error in an absolute value, including its integer-square-root truncation, is at most `440005/S_*`. After all positive weights in `500*G` are included, possible overestimation is less than

\[
 \frac{680\cdot10\cdot440005}{500S_*}<3\cdot10^{-8}
\]

in the unscaled value of `G`. Negative absolute-value terms use an upper integer bound (`floor+1`), so they cannot introduce an additional overestimate.

Nevertheless, the program subtracts the much larger exact allowance `10^-6` from every center value, rounding that subtraction upwards in integer units. The box variation is also rounded upwards. Therefore a positive recorded integer margin proves positivity on the entire box, regardless of floating-point library accuracy.

The CSV denominator `140737488355328000` is exactly `500*S_*`. Its margin numerators are the remaining positive integers after all these deductions.

## 6. From the one-step lemma to all block lengths

Let

\[
 Q_M(t)=T(10^{M-1}t)\cdots T(t),\qquad
 H=\operatorname{diag}(h_0,h_1),\quad h_0=1.
\]

The Parry mask is exactly

\[
 R_M(t)=\lambda^{-M}H^{-1}Q_M(t)H.
\]

Repeatedly applying the certified lemma, grouping the shifted indices by their residue modulo ten, gives

\[
 \sum_{\ell=0}^{10^M-1}N\left(pQ_M\left(\frac{x+\ell}{10^M}\right)\right)
 \geq(291/20)^M N(p).
\]

Write `h_min=min(h_0,h_1)>0`. The elementary norm comparison is

\[
 \|vH\|_1\geq\frac{h_{\min}}{1+\rho}N(v).
\]

Taking `p=(1,0)`, for which `N(p)=1+rho`, proves

\[
 C_M\geq h_{\min}(291/(20\lambda))^M.
\]

The EXACT row norms are submultiplicative:

\[
 C_{m+n}\leq C_m C_n.
\]

This follows by factoring `R_{m+n}(t)=R_m(10^n t)R_n(t)`, retaining the intermediate state index, and summing the second block's shifted row norm before the first block's. It is a matrix row-norm argument, not a scalar truncation.

For fixed `M` apply the last two inequalities to `kM`:

\[
 C_M^k\geq C_{kM}\geq h_{\min}(291/(20\lambda))^{kM}.
\]

Taking kth roots and then `k` to infinity eliminates the prefactor. This proves the stated all-M lower bound.

The Perron eigenvalues are `(9+sqrt(117))/2` for repeated digits and `5+2*sqrt(6)` for distinct digits. Both are strictly less than `991/100`. Finally,

\[
 1455^6-10\,991^6=16066563032016215>0.
\]

The strict separation from `10^(1/6)` is therefore exact, not numerical.

## 7. The uniform tail beyond the actual horizon

Let the number of decimal cylinders at the horizon be `L=10^(nM)`, let their prefix probabilities be `p_j`, and define the periodic prefix transform

\[
 A_n(k)=\sum_{j=0}^{L-1}p_j e(-jk/L).
\]

Appending an independent uniform tail gives

\[
 \widehat\nu_n(k)=A_n(k)e(-k/(2L))\operatorname{sinc}(k/L),
 \qquad \operatorname{sinc}(y)=\frac{\sin(\pi y)}{\pi y}.
\]

Choose centered residues `-L/2<=r<L/2`. For `T>=L`, the elementary harmonic-sum bound gives, uniformly in `r`,

\[
 \sum_{m:\,|mL+r|\leq T}|\operatorname{sinc}(m+r/L)|
 \leq 1+\frac4\pi H_{\lfloor T/L\rfloor+1}.
\]

Consequently

\[
 \sum_{|k|\leq T}|\widehat\nu_n(k)|
 \ll\bigl(1+\log(2+T/L)\bigr)
 \sum_{-L/2\leq r<L/2}|A_n(r)|.
\]

Thus stopping at the true horizon does cost only a logarithm beyond it. If the prefix sum had a uniform bound `O(L^alpha)` with any fixed `alpha>0`, this logarithm would be absorbed into `O_alpha(T^alpha)` for `T>=L`. No per-block post-horizon Dirichlet constant is necessary. This valid tail repair does not affect the clean-block obstruction proved above.

## Exact remaining threshold

Within the proposed criterion, existence of a contracting finite block is equivalent to

\[
 \inf_{M\geq1}C_M^{1/M}<10^{1/6}.
\]

The certificate proves instead

\[
 \inf_{M\geq1}C_M^{1/M}\geq\frac{291}{20\lambda}
 >\frac{1455}{991}>10^{1/6}.
\]

There is therefore no untested larger block length left as a possible remedy for this criterion. A BA--ALA existence proof could still use an estimate retaining cancellations discarded by this row norm, a different digital measure, or another argument. No such existence claim is made here.

## File integrity

```text
ec5eb777d3e9de3f1a2c91030a9f91353350fc3a14dec9e3c1cbb40ee49bc565  certify.cpp
57a7d0d4e25ce5f81134f75f373d74605348b764099b0ad5ffc71121623aa2cc  certificate.csv
```


## Scalar consequence for the actual guarded 01 process — 2026-09-06

Status: proof sketch, independently checked; the numerical premise is the
one-step lemma certified above, not merely the all-block C_M lower bound.
This section concerns exactly the forward Parry process for w=01, alphabet
{1,...,9}, marker 2, initial prefix P22, and deterministic guarded packets
beginning with 2. It is not an obstruction to all measures supported on C_01.

Write lambda=5+2 sqrt(6), h=lambda-9, H=diag(1,h), rho=9/25,
q=291/(20 lambda), and define the physical-row norm M(p)=N(p H^(-1)).
The free mask K(t)=lambda^(-1) H^(-1) T_01(t) H satisfies
sum_j M(p K((x+j)/10))>=q M(p) for every complex p and real x.

A forced packet can collapse a complex row, so iteration of this free
inequality alone would be invalid. Pair each forced run with its preceding
free digit. If the resulting block has length m>=2, its forced suffix
starts with 2, consists only of nonzero digits and resets every incoming
state to zero. Put (a,b)=p H^(-1) and U=a+b. Before the reset its scalar
factor, apart from lambda^(-1), is
(a,b) T_01(t) H 1 = U(S(t)-(1-h))-b e(-t).
Its digit coefficients are hU at digit 0, a at digit 1, and U at digits
2,...,9. Fourier inversion gives a shifted ten-point absolute sum at least
10 max(|a|,|U|), while N(a,b)<= (1+3rho) max(|a|,|U|).
The deterministic suffix contributes a phase of modulus one. Grouping
the full m-digit frequency grid by its residue modulo 10 therefore gives,
for the actual block matrix B_m,

    sum_(r=0)^(10^m-1) M(p B_m((x+r)/10^m))
    >= [10^m (1+rho)/(lambda (1+3rho))] M(p)
    >= q^m M(p).

For m=2 the first multiplier is 850/(13 lambda)>6, whereas q^2<3;
each further forced digit multiplies it by 10>q. This controls arbitrarily
long packets without a loss depending on their length. Use free singleton
blocks elsewhere. A horizon inside a packet uses its truncated forced suffix.
The initial deterministic P22 ends in state zero and contributes 10^p
to its p-digit grid sum. Thus the actual probability Fourier row v_N at
every horizon N>=p satisfies, on every complete shifted grid Gamma_N(x),

    sum_(t in Gamma_N(x)) M(v_N(t)) >= q^N (1+rho),
    Gamma_N(x) = {(x+r)/10^N : 0<=r<10^N}.

Now let Psi_N=v_(N,0)+v_(N,1) be the scalar prefix transform. Terminal
state 1 means exactly that the last digit is 0, so

    v_(N,1)(t) = (1/10) sum_(j=0)^9 Psi_N(t+j/10),
    v_(N,0)(t) = Psi_N(t)-v_(N,1)(t).

Translation by j/10 permutes Gamma_N(x) modulo one. Hence the row l1 sum
on that grid is at most three times the scalar sum. Since
M(p)<=(1+rho)(|p0|+|p1|)/h, it follows that

    sum_(r=0)^(10^N-1) |Psi_N((x+r)/10^N)| >= (h/3) q^N.

Appending the independent uniform tail multiplies integer Fourier
coefficients by a phase and sinc(r/10^N). On centered residues its magnitude
is at least 2/pi. Therefore the actual finite-horizon measures obey

    sum_(|r|<=10^N/2) |nu_N_hat(r)|
    >= (2h/(3 pi)) [291/(20 lambda)]^N.

In particular any horizon-uniform scalar Fourier-l1 upper exponent for
this exact process must be at least log10(291/(20 lambda))=0.1672725...>1/6.
Indeed lambda<99/10 implies 291/(20 lambda)>97/66, and
97^6-10*66^6=6432504769>0. This lower bound includes the forced packets
and true horizon; it is not an extrapolation of finite frequency samples.
It rules out the proposed scalar estimate, not this P1 instance by other
constructions. The coordinator separately recovered the terminal-state
projection argument before reading the independent continuation, then checked
the stronger free-digit/reset-block expansion and all norm comparisons above.

## Repository verification status — 2026-09-06

Status: proof sketch for the analytical and certified-arithmetic argument; experiment for the executable reproduction. Not Lean, not a universal P1 resolution, and not pi-digit progress. The coordinator inspected every acceptance decision, the integer/trigonometric error budget, the complex-row norm lemma, the Parry conjugation, submultiplicativity and the removal of the prefactor. The full source was compiled locally with GCC and run: 100 PASS records, 77,233,788 nodes. A second run matched certificate.csv byte for byte (cmp exit 0). These checks do not upgrade the claim to machine-checked in the repository's Lean sense. No novelty claim is made.
