# T30: One fixed real with sparse large ordinary Fejer energy

Status: `proof sketch`

## Provenance and scope

- Agenda item: T30, serving G5.
- Canonical local statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Canonical statement SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Original source URL: none is recorded. The canonical question was formulated
  locally by this system on 2026-07-22.
- Previously checked definitions matched here: the signed strict band and
  triangular weights in T10's `ordinaryFejerEnergy`.
- Literature input: none. No novelty claim is made.

This note constructs one fixed real `x` from one infinite decimal expansion.
It is a sibling fixed-real separation. It is not a construction involving the
decimal expansion of pi and is not evidence for or against C1. The T29 note is
an unverified proof sketch and is not used as a premise below. All fixed-seed
compatibility statements needed here are proved directly in Section 8.

Here `C1` denotes the program conjecture that pi has positive decimal factor
entropy; `C2` through `C7` refer to the other program conjectures listed in the
agenda context. They are not the `A1` through `A18` ambiguity labels in the
canonical statement.

## 1. Normalized statement and conventions

Write

\[
  e(u)=\exp(2\mathop{\rm pi} i u).
\]

For a fixed real `x`, put

\[
  X_j=\{10^j x\},\qquad
  S_x(h;M)=\sum_{j=0}^{M-1}e(hX_j) \quad (h\in\mathbb Z).
\]

For positive integers `H,M`, define the complete ordinary Fejer energy

\[
  \operatorname{Energy}_H(M;x)
   =\sum_{\substack{h\in\mathbb Z\\ |h|<H}}
      \left(1-\frac{|h|}{H}\right)|S_x(h;M)|^2.       \tag{1.1}
\]

Thus the frequency cutoff is strict, both signs and the zero mode are
included, and no normalization is hidden in the definition.

We construct integer sequences `n_s,M_s,H_s,D_s` for every `s>=1` such that

\[
  M_s=10^{n_s},\qquad H_s=M_s/2,\qquad D_s=3^s,       \tag{1.2}
\]

and prove

\[
 \frac{\operatorname{Energy}_{H_s}(M_s;x)}{M_s^2}
       \longrightarrow +\infty,                       \tag{1.3}
\]

while

\[
 \frac{\operatorname{Energy}_{H_s}(M_s;x)}{H_sM_s^2}
       \longrightarrow 0.                              \tag{1.4}
\]

The limits are only along the explicitly defined scales indexed by `s`.

The following possible ambiguities are fixed throughout.

1. The orbit is the ordinary orbit of one real `x`, always starting at
   `j=0`; the starting seed is not changed with `s`.
2. `D_s` is the exact period of the rational template used in decimal block
   `s`. It is not asserted to be a period of the whole orbit of `x`.
3. The old prefix before block `s` is retained in every sum. It is estimated,
   not discarded or cyclically reordered.
4. Agreement of decimal strings is converted to an ordinary phase estimate;
   no finite-circle energy is substituted for (1.1).
5. The quantization moduli in Section 8 are auxiliary powers of ten. They are
   distinct from `M_s`, `H_s`, and `D_s`.
6. The phrase "tends to infinity" in (1.3) means: for every real `B`, all
   sufficiently large `s` have the displayed quotient greater than `B`.

## 2. The exact periodic templates

For `s>=1`, define

\[
  D_s=3^s,\qquad y_s=\frac{1}{9D_s}=\frac1{3^{s+2}}.  \tag{2.1}
\]

The denominator is coprime to ten, so the standard decimal expansion of
`y_s` is purely periodic. We now verify its exact period and the character
sums that will be used later.

### Lemma 2.1: the period is exactly `D_s`

For every positive integer `m`,

\[
  v_3(10^m-1)=2+v_3(m).                                \tag{2.2}
\]

Here is an elementary verification. Write `m=3^r u` with `3` not dividing
`u`. Since `10=1+9`, the binomial expansion modulo `27` gives

\[
  10^u-1\equiv 9u\pmod {27}.
\]

Therefore `v_3(10^u-1)=2`. If `z` is congruent to one modulo three, then

\[
 z^3-1=(z-1)(z^2+z+1),
 \qquad v_3(z^2+z+1)=1,                                \tag{2.3}
\]

because, on writing `z=1+3c`, the second factor is
`3(1+3c+3c^2)`. Applying (2.3) successively `r` times proves (2.2).
Consequently

\[
  9D_s\mid 10^m-1
   \quad\Longleftrightarrow\quad D_s\mid m.            \tag{2.4}
\]

Multiplication by ten modulo the denominator `9D_s` therefore has exact
order `D_s`. This proves that the decimal period of `y_s` is exactly `D_s`.

### Lemma 2.2: complete and incomplete character sums

Set

\[
  c_t=\frac{10^t-1}{9}\in\mathbb Z.                   \tag{2.5}
\]

The residues `c_0,...,c_{D_s-1}` form a permutation of
`0,...,D_s-1` modulo `D_s`. Indeed, if `0<=u<t<D_s` and
`c_t` were congruent to `c_u` modulo `D_s`, cancellation of the power of ten
would give

\[
  D_s\mid\frac{10^{t-u}-1}{9}.
\]

This is equivalent to `9D_s | 10^(t-u)-1`, which contradicts (2.4) because
`0<t-u<D_s`.

In the circle `R/Z`, equation `10^t=1+9c_t` gives

\[
  \{10^t y_s\}=\frac1{9D_s}+\frac{c_t}{D_s}\pmod 1.  \tag{2.6}
\]

It follows from the elementary sum of all `D_s`-th roots of unity that, for
every integer `h`,

\[
 \sum_{t=0}^{D_s-1}e\bigl(h\{10^t y_s\}\bigr)
 =
 \begin{cases}
   D_s e(h/(9D_s)),&D_s\mid h,\\
   0,&D_s\nmid h.
 \end{cases}                                           \tag{2.7}
\]

If `D_s | h`, every individual summand in (2.7), not merely their sum, is
the same number `e(h/(9D_s))`. If `D_s` does not divide `h`, divide any
finite consecutive interval into complete periods and one remainder. The
complete periods vanish and the remainder has fewer than `D_s` unit terms.
Thus, for every `L>=0`,

\[
 \left|\sum_{t=0}^{L-1}e\bigl(h\{10^t y_s\}\bigr)\right|
 =L\quad(D_s\mid h),                                   \tag{2.8}
\]

and

\[
 \left|\sum_{t=0}^{L-1}e\bigl(h\{10^t y_s\}\bigr)\right|
 \le D_s\quad(D_s\nmid h).                            \tag{2.9}
\]

Equations (2.8) and (2.9) are the only periodic-orbit Fourier facts used in
the construction.

## 3. Explicit recursive scales and boundaries

Let

\[
  A_1=0,\qquad n_0=0.                                  \tag{3.1}
\]

Suppose `A_s` and `n_(s-1)` have been defined. Let `n_s` be the least natural
number satisfying both

\[
 n_s>n_{s-1}                                             \tag{3.2}
\]

and

\[
 10^{n_s}\ge 2^{s+4}(A_s+D_s+1).                       \tag{3.3}
\]

Such an integer exists because powers of ten are unbounded. Define

\[
 \begin{aligned}
  M_s&=10^{n_s},& H_s&=M_s/2,\\
  P_s&=n_s+2s+10,& A_{s+1}&=M_s+P_s.
 \end{aligned}                                          \tag{3.4}
\]

This is a fully deterministic recursion: "least" in (3.2)-(3.3) removes any
choice of scales.

The first three rows, included to make the recursion immediately
reproducible, are

| `s` | `D_s` | `A_s` | `n_s` | `M_s` | `H_s` | `P_s` | `A_(s+1)` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 0 | 3 | 1000 | 500 | 15 | 1015 |
| 2 | 9 | 1015 | 5 | 100000 | 50000 | 19 | 100019 |
| 3 | 27 | 100019 | 8 | 100000000 | 50000000 | 24 | 100000024 |

Put

\[
  \epsilon_s=2^{-(s+4)}.                                \tag{3.5}
\]

The following scale and boundary facts will be used explicitly.

1. Since `n_s>=s>=1`, `M_s` is even and `M_s=2H_s` exactly.
2. Equation (3.3) gives
   \[
     \frac{A_s}{M_s}\le\epsilon_s,
     \qquad \frac{D_s}{M_s}\le\epsilon_s.             \tag{3.6}
   \]
3. In particular `A_s<M_s<A_{s+1}`, so scale `M_s` lies strictly inside
   block `s`.
4. The current part of the first `M_s` digits has length
   \[
     M_s-A_s\ge(1-\epsilon_s)M_s.                       \tag{3.7}
   \]
5. The period is small compared with the bandwidth:
   \[
     \frac{H_s}{D_s}=\frac{M_s}{2D_s}\ge2^{s+3}.        \tag{3.8}
   \]
6. The block length `A_(s+1)-A_s` is greater than `D_s`, so every block
   contains at least one complete template period.
7. Both `D_s=3^s` and `M_s` tend to infinity, and the periods are strictly
   increasing.

The look-ahead exponent `P_s` was chosen so that the uniform phase loss

\[
 \delta_s=2\mathop{\rm pi} H_s10^{-P_s}                \tag{3.9}
\]

is explicit. Substituting (3.4) gives the exact identity

\[
 \delta_s=\mathop{\rm pi}\,10^{-2s-10}.                \tag{3.10}
\]

Using the elementary bound `pi<4`, one has, for every `s>=1`,

\[
 0<\delta_s\le\epsilon_s.                              \tag{3.11}
\]

For example, after multiplying the desired inequality by `2^(s+4)`, the
upper bound from `pi<4` is
`64*2^s/10^(2s+10)<1`; it is already less than one at `s=1` and decreases
by the factor `2/100` at each successor.

## 4. The single decimal expansion

Let

\[
  y_s=0.\overline{w_s}
\]

be its purely periodic decimal expansion, where `w_s` is the word of exact
length `D_s` proved in Section 2. Equivalently, digit `k>=1` of this infinite
periodic string is the explicitly computable integer

\[
 b_{s,k}=\left\lfloor10\{10^{k-1}y_s\}\right\rfloor
 =\left\lfloor10\left\{\frac{10^{k-1}}{3^{s+2}}\right\}\right\rfloor.
                                                               \tag{4.0}
\]

Define digits `d_r in {0,...,9}` for every `r>=1` as follows. For the unique
`s` with

\[
  A_s<r\le A_{s+1},
\]

set `d_r=b_(s,r-A_s)`. Finally define

\[
  x=\sum_{r=1}^{\infty}d_r10^{-r}.                     \tag{4.1}
\]

For example, positions `1,...,1015` repeat the word `037`, the period word of
`1/27`. Positions `1016,...,100019` repeat `012345679`, the period word of
`1/81`. Later blocks are fixed by the same floor formula (4.0), not by an
existential choice of a period word.

This is one definition of one real, not a scale-dependent family of seeds.
The intervals `(A_s,A_(s+1)]` are consecutive and exhaust the positive
integers, so every digit is defined exactly once.

The decimal representation in (4.1) is canonical and nonterminating. Indeed,
`0<y_s<1/10`, so the first digit of every block is zero. There are therefore
infinitely many zero digits, and the sequence is not eventually nine. Also
`y_s>0`, so its period word is not all zero; by item 6 of Section 3 every
block contains a nonzero digit. Hence the sequence is not eventually zero.

In particular `0<=x<1`. Since the usual circle constant satisfies `pi>3`,

\[
  x\ne\mathop{\rm pi}.                                  \tag{4.2}
\]

This elementary range argument is the only comparison between the
constructed real and pi itself. The fractional decimal orbit is also
different already at time zero. The first digit of `x` is zero and its
canonical expansion is not eventually nine, so `x<1/10`. On the other hand,
the elementary inscribed-regular-dodecagon bound gives

\[
 \mathop{\rm pi}>6\sqrt{2-\sqrt3}>\frac{31}{10}.        \tag{4.3}
\]

For completeness, the second strict inequality follows from
`sqrt(3)<97/56`, since `3<9409/3136`, and then
`36(2-sqrt(3))>36(15/56)=135/14>961/100`. Hence

\[
 \{\mathop{\rm pi}\}=\mathop{\rm pi}-3>\frac1{10}>x.  \tag{4.4}
\]

Thus `X_0=x` is not even the time-zero point of the decimal orbit of pi.

## 5. Block approximation and all cross-block errors

Fix `s>=1` for this section and abbreviate

\[
 A=A_s,\quad D=D_s,\quad M=M_s,\quad H=H_s,\quad P=P_s.
\]

If `A<=j<M`, the suffix defining `X_j={10^j x}` remains in block `s` through
digit `A_(s+1)`. It therefore agrees with the decimal expansion of
`{10^(j-A)y_s}` in at least

\[
 A_{s+1}-j\ge P+1
\]

successive digits. Two numbers in `[0,1]` with the same first `P` decimal
digits differ by at most `10^(-P)`. Thus

\[
 \left|X_j-\{10^{j-A}y_s\}\right|\le10^{-P}.           \tag{5.1}
\]

The elementary chord estimate

\[
 |e(hu)-e(hv)|\le2\mathop{\rm pi}|h|\,|u-v|            \tag{5.2}
\]

then gives, uniformly for every integer `h` with `|h|<H`,

\[
 \left|e(hX_j)-e\bigl(h\{10^{j-A}y_s\}\bigr)\right|
 \le2\mathop{\rm pi}H10^{-P}.                          \tag{5.3}
\]

Split the full ordinary sum, without deleting its old prefix, as

\[
 S_x(h;M)=U_s(h)+T_s(h)+R_s(h),                         \tag{5.4}
\]

where

\[
 \begin{aligned}
 U_s(h)&=\sum_{j=0}^{A-1}e(hX_j),\\
 T_s(h)&=\sum_{t=0}^{M-A-1}e\bigl(h\{10^t y_s\}\bigr),
 \end{aligned}
\]

and `R_s(h)` is the sum of the termwise differences on `A<=j<M`.
The three explicit estimates are

\[
 |U_s(h)|\le A,                                         \tag{5.5}
\]

\[
 |R_s(h)|\le2\mathop{\rm pi}HM10^{-P}=\delta_sM,       \tag{5.6}
\]

and, by (2.8)-(2.9),

\[
 |T_s(h)|=
 \begin{cases}
  M-A,&D\mid h,\\
  \text{at most }D,&D\nmid h.
 \end{cases}                                            \tag{5.7}
\]

The reverse triangle inequality in the first case and the triangle
inequality in the second yield the two ordinary-orbit Fourier estimates
needed below:

\[
 \boxed{|S_x(h;M_s)|\ge
   M_s-2A_s-\delta_sM_s
   \quad\text{if }D_s\mid h\text{ and }|h|<H_s.}        \tag{5.8}
\]

and

\[
 \boxed{|S_x(h;M_s)|\le
   A_s+D_s+\delta_sM_s
   \quad\text{if }D_s\nmid h\text{ and }|h|<H_s.}       \tag{5.9}
\]

For annihilator frequencies we also retain the universal upper bound

\[
 |S_x(h;M_s)|\le M_s.                                  \tag{5.10}
\]

Equations (5.5) and (5.6) are respectively the complete old-block error and
the complete phase error. There is no omitted boundary term: `j=A_s` is the
first template digit and `j=M_s-1` still has at least `P_s+1` copied digits
ahead of it.

By (3.6) and (3.11), the right side of (5.8) is at least

\[
 (1-3\epsilon_s)M_s\ge\frac78M_s.                      \tag{5.11}
\]

## 6. Divergence after `M_s^2` normalization

Let

\[
  E_s=\operatorname{Energy}_{H_s}(M_s;x).
\]

Set

\[
  K_s=\left\lfloor\frac{H_s}{2D_s}\right\rfloor.
\]

Equation (3.8) gives `H_s/(2D_s)>=2^(s+2)>=1`, and therefore

\[
 K_s\ge\frac{H_s}{4D_s}.                               \tag{6.1}
\]

For every `1<=m<=K_s`, the positive frequency `h=mD_s` obeys
`0<h<=H_s/2`, so it lies in the strict band, its Fejer weight is at least
`1/2`, and (5.11) applies. Keeping just these nonnegative terms in (1.1)
gives

\[
 \begin{aligned}
 \frac{E_s}{M_s^2}
 &\ge K_s\cdot\frac12\cdot\left(\frac78\right)^2\\
 &=\frac{49}{128}K_s\\
 &\ge\frac{49}{512}\frac{H_s}{D_s}\\
 &\ge\frac{49}{64}2^s.                                \tag{6.2}
 \end{aligned}
\]

The final expression tends to positive infinity. This proves (1.3), with an
explicit lower rate.

## 7. Vanishing after `H_s M_s^2` normalization

For every positive integer `H`, direct summation gives

\[
 \sum_{|h|<H}\left(1-\frac{|h|}{H}\right)
 =1+2\sum_{h=1}^{H-1}\left(1-\frac hH\right)=H.         \tag{7.1}
\]

All these weights lie in `[0,1]`. The number of multiples of `D_s` in the
strict band is

\[
 2\left\lfloor\frac{H_s-1}{D_s}\right\rfloor+1
 \le\frac{2H_s}{D_s}+1.                                \tag{7.2}
\]

Use (5.10) on those frequencies. On every remaining frequency use (5.9),
and bound the sum of their weights by the full sum (7.1). This gives

\[
 E_s\le
 \left(\frac{2H_s}{D_s}+1\right)M_s^2
 +H_s(A_s+D_s+\delta_sM_s)^2.                           \tag{7.3}
\]

After division by `H_sM_s^2`,

\[
 0\le\frac{E_s}{H_sM_s^2}
 \le\frac2{D_s}+\frac1{H_s}
   +\left(\frac{A_s}{M_s}+\frac{D_s}{M_s}
      +\delta_s\right)^2.                              \tag{7.4}
\]

Every term is quantitatively controlled. Namely,

\[
 D_s=3^s,\qquad
 \frac1{H_s}\le2^{-(s+3)},\qquad
 \frac{A_s}{M_s}+\frac{D_s}{M_s}+\delta_s
 \le3\epsilon_s.                                      \tag{7.5}
\]

Consequently

\[
 0\le\frac{E_s}{H_sM_s^2}
 \le \frac2{3^s}+2^{-(s+3)}+9\,2^{-(2s+8)},            \tag{7.6}
\]

whose right side tends to zero. The squeeze theorem proves (1.4).

Together, (6.2) and (7.6) establish the claimed separation for the same
ordinary orbit and the same sequence of scales.

## 8. Direct fixed-seed and nested-quantization checks

This section does not invoke the T29 note. It verifies the relevant
compatibility laws from the definition of `x`.

The exponents `P_s` are strictly increasing: (3.2) implies
`P_(s+1)>=P_s+3`. Define

\[
 Q_s=10^{P_s}.                                         \tag{8.1}
\]

Then `Q_s` divides `Q_t` whenever `t>=s`, and `Q_s` tends to infinity. For
every `s>=1` and every time `j>=0`, define the integer label

\[
 a_{s,j}=\left\lfloor Q_sX_j\right\rfloor
 =\left\lfloor Q_s\{10^jx\}\right\rfloor.             \tag{8.2}
\]

Thus, before proving any compatibility, every label at every scale and time
is already derived from the same fixed seed `x`.

### 8.1 Range and all-pairs coarse projection

Since `0<=X_j<1`,

\[
 0\le a_{s,j}<Q_s.                                     \tag{8.3}
\]

For `t>=s`, let `r_(t,s)=Q_t/Q_s`. Then

\[
 \boxed{
 \left\lfloor\frac{a_{t,j}}{r_{t,s}}\right\rfloor
 =a_{s,j}\quad(t\ge s,\ j\ge0).}                      \tag{8.4}
\]

To check (8.4), write `Q_sX_j=m+theta` with `m=floor(Q_sX_j)` and
`0<=theta<1`. Then

\[
 a_{t,j}=\lfloor r_{t,s}Q_sX_j\rfloor
          =r_{t,s}m+\lfloor r_{t,s}\theta\rfloor,
\]

where the last floor lies between zero and `r_(t,s)-1`. Division by
`r_(t,s)` and one more floor gives `m=a_(s,j)`. This is floor-cell projection,
not reduction modulo `Q_s`, and it holds for every pair `t>=s`.

The projections automatically compose because both sides of a composite are
equal to the same coarse label `a_(s,j)` by (8.4).

### 8.2 Half-open boundary compatibility

The floor inequalities are

\[
 \frac{a_{s,j}}{Q_s}\le X_j
  <\frac{a_{s,j}+1}{Q_s}.                              \tag{8.5}
\]

They also give

\[
 0\le X_j-\frac{a_{s,j}}{Q_s}<\frac1{Q_s}.             \tag{8.6}
\]

Since `Q_s` tends to infinity,

\[
 \sup_s\frac{a_{s,j}}{Q_s}=X_j.                        \tag{8.7}
\]

Combining (8.5) and (8.7) verifies the strict right-boundary condition at
every finite scale:

\[
 \boxed{
 \sup_t\frac{a_{t,j}}{Q_t}
 <\frac{a_{s,j}+1}{Q_s}\quad(s\ge1,\ j\ge0).}          \tag{8.8}
\]

Thus no inverse limit selects an excluded right endpoint.

### 8.3 Decimal successors at every scale and time

Define

\[
 e_{s,j}=\left\lfloor10\{Q_sX_j\}\right\rfloor.       \tag{8.9}
\]

Then `e_(s,j)` is an integer and

\[
 0\le e_{s,j}\le9.                                    \tag{8.10}
\]

Because `X_(j+1)={10X_j}`,

\[
\begin{aligned}
 a_{s,j+1}
 &=\lfloor Q_s\{10X_j\}\rfloor\\
 &=\lfloor10Q_sX_j\rfloor-Q_s\lfloor10X_j\rfloor\\
 &=10a_{s,j}+e_{s,j}-Q_s\lfloor10X_j\rfloor.
\end{aligned}                                          \tag{8.11}
\]

Hence

\[
 \boxed{
 a_{s,j+1}\equiv10a_{s,j}+e_{s,j}\pmod {Q_s},
 \qquad0\le e_{s,j}\le9}                              \tag{8.12}
\]

for every `s>=1` and every `j>=0`. There is no finite cyclic wrap in the time
index. Since `Q_s=10^(P_s)`, `e_(s,j)` is also literally the next decimal
digit after the `P_s`-digit quantization of the suffix beginning at `j+1`.

Equations (8.2), (8.4), (8.8), and (8.12) are respectively the fixed-seed,
nested-projection, boundary, and decimal-successor checks requested in the
agenda item.

## 9. Audit summary and explicit nonclaims

The construction supplies the following checkable data.

1. One fixed canonical nonterminating decimal expansion (4.1), with every
   digit assigned by one and only one block.
2. Explicit recursive boundaries and scales (3.1)-(3.4), including
   `M_s=10^(n_s)`, `H_s=M_s/2`, and exact template periods `D_s=3^s`.
3. Exact complete-period Fourier sums (2.7) and incomplete-period bound
   (2.9).
4. The old-prefix error (5.5), phase error (5.6), and resulting ordinary
   orbit estimates (5.8)-(5.9).
5. The quantitative divergent lower bound (6.2) and vanishing upper bound
   (7.6).
6. One fixed-seed label array at all scales and all times, satisfying the
   all-pairs floor projection (8.4), strict boundary condition (8.8), and
   decimal-successor congruence (8.12).

The scope exclusions are equally explicit.

- The constructed `x` is not pi, by (4.2).
- No estimate in this note is asserted for the decimal orbit of pi.
- This note neither proves nor disproves any of the program conjectures C1,
  C2, C3, C4, C5, C6, or C7.
- It makes no claim about the decimal factor entropy of pi or of `x`.
- It does not amplify a T10 resonance for pi and does not establish any
  arithmetic contradiction.
- It does not use any claim from the T29 proof sketch as an established
  premise; the compatibility calculations are repeated directly in Section
  8 for this explicit `x`.
- The occurrence of the usual constant `pi` in the phase bound (5.2) is only
  the standard analytic constant in the exponential map, not a use of the
  decimal orbit of pi.

Accordingly, the result is strictly a sibling fixed-real separation: fixed
seed compatibility by itself is consistent with energy unbounded after
`M_s^2` normalization but vanishing after `H_sM_s^2` normalization.
