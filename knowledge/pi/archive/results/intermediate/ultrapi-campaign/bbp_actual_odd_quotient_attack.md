# BBP actual odd quotient: a closed carry recurrence and explicit prime coordinates

Audit date: **2026-08-12 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Parent report:
[bbp_short_orbit_return_attack.md](bbp_short_orbit_return_attack.md),
SHA-256
eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained. Canonical V1 remains a "conjecture".

This branch attacks the actual complementary numerator left open by the
parent report. It obtains four exact advances, all with status "proof sketch".

1. The reflected BBP function satisfies
   \(F(X+1)=16F(X)+a(X)\). At precisely the precision available from depth
   \(M\), this gives a closed carry recurrence for the complete dyadic
   coordinate \(w_{M+1}\).
2. That carry recurrence and the real BBP increment give a closed
   cross-depth recurrence for the actual reduced odd quotient
   \(c_M/R_M\). It does not require nesting of the changing odd denominators.
3. On the parent report's clean bands, the actual additive CRT coordinate is
   exactly \(64\) or \(-32\). The same localization extends to **every**
   possible denominator prime \(p>M\): only eight fixed rational coordinates
   occur, and none vanishes once \(M\geq48\).
4. A sign and height argument pushes the explicit coordinates down to
   \(p>M/L_M\), where
   \(L_M\asymp\log M\). Removing them leaves one cofactor
   \(C_M\) with

   \[
    \log C_M=o(M).                                   \tag{1}
   \]

Thus the remaining target is one weighted \(O(M)\)-term power-generator sum
on a subexponential cofactor. The explicit high-prime product has logarithm
\((6+o(1))M\), the complete two-adic coordinate is explicit, and
\(\log R_M=(6+o(1))M\). No theorem found or proved controls the selected
cofactor residue at logarithmic orbit length.

The infinite identities and asymptotics below have status "proof sketch".
The companion exact replay has status "experiment". The dated source audit
has status "literature-checked". Nothing is "machine-checked" or a
"candidate resolution".

## 1. Exact target and proportional-band normalization

Use

\[
 a(k)=\frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_M=\sum_{k=0}^{M}\frac{a(k)}{16^k}.                \tag{2}
\]

Let \(\lambda=\log_{10}16\). The parent report proves the uniform transfer

\[
 \left|
 \|(10^n-16)\pi\|_{\mathbb T}
 -\|(10^n-16)B_M\|_{\mathbb T}
 \right|
 \leq\frac1{15(M+1)^2}                               \tag{3}
\]

whenever \(5\leq n\leq\lfloor\lambda M\rfloor\).

For this branch it is useful to remove every fixed exponent. Define

\[
 \Delta_M=
 \min_{M\leq n\leq\lfloor\lambda M\rfloor}
 \|(10^n-16)B_M\|_{\mathbb T}\qquad(M\geq5).         \tag{4}
\]

Then

\[
 \boxed{
 \liminf_{M\to\infty}\Delta_M=0
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|(10^n-16)\pi\|_{\mathbb T}=0.} \tag{5}
\]

The forward implication follows from (3), because every selected exponent
satisfies \(n\geq M\to\infty\). Conversely, given a return sequence \(n_j\),
take \(M_j=\lceil n_j/\lambda\rceil\). For all large \(j\),
\(M_j\leq n_j\leq\lfloor\lambda M_j\rfloor\), and (3) transfers the return
to the proportional row. The separately audited Furstenberg bridge makes the
right side of (5) equivalent to V1. Equation (5) does not prove either side;
it merely prevents a fixed small exponent from masking the remaining task.

## 2. The full-pole functional equation and exact dyadic carry

Recall the restricted analytic two-adic function

\[
 F(X)=\sum_{j\geq0}16^j a(X-1-j).                    \tag{6}
\]

Separating the first term after shifting \(X\) gives the exact global
functional equation

\[
\begin{aligned}
 F(X+1)
 &=\sum_{j\geq0}16^j a(X-j)\\
 &=a(X)+16\sum_{j\geq0}16^j a(X-1-j)\\
 &=\boxed{a(X)+16F(X)}.                              \tag{7}
\end{aligned}
\]

Write the reduced BBP sum as

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 K_M=4M-r_M,\qquad r_M=v_2(M+1),                    \tag{8}
\]

where \((P_M,2R_M)=1\) and \(R_M\) is odd. Put

\[
 s_M=K_M-4=4M-r_M-4,\qquad D_M=2^{s_M}.             \tag{9}
\]

The complete dyadic coordinate is

\[
 0\leq w_M<D_M,\qquad
 w_M\equiv P_MR_M^{-1}\pmod {D_M}.                  \tag{10}
\]

By the reflected-tail congruence in the parent report,

\[
 w_M\equiv u_M:=2^{-r_M}F(M+1)\pmod {2^{s_M}}.      \tag{11}
\]

Let \([x]_{2^t}\) denote the least nonnegative residue of a two-integral
rational modulo \(2^t\), and define

\[
 \alpha_M=[a(M+1)]_{2^{4M}}.                        \tag{12}
\]

Equation (7) gives

\[
 u_{M+1}
 =2^{-r_{M+1}}
 \left(a(M+1)+2^{r_M+4}u_M\right).                  \tag{13}
\]

The old coordinate contains exactly enough precision for the new one:

\[
 4M-(r_M+4)=s_M,\qquad
 s_{M+1}+r_{M+1}=4M.                                \tag{14}
\]

Consequently the complete finite carry recurrence is

\[
 \boxed{
 w_{M+1}
 =2^{-r_{M+1}}
 \left[
 \alpha_M+2^{r_M+4}w_M
 \right]_{2^{4M}}.}                                 \tag{15}
\]

The canonical residue in brackets is divisible by \(2^{r_{M+1}}\), because
it is congruent to \(F(M+2)\), whose valuation is
\(r_{M+1}=v_2(M+2)\). After division it lies in
\([0,2^{s_{M+1}})\), so (15) is equality, not merely congruence.

This recurrence uses the actual four-pole coefficient at every step. It is
stronger than the isometry statement alone, but it still extracts high
two-adic digits along a diagonal whose precision grows by roughly four bits
per depth.

## 3. Closed recurrence for the actual reduced odd quotient

Define

\[
 c_M=\frac{P_M-R_Mw_M}{D_M},\qquad
 q_M=\frac{c_M}{R_M},\qquad
 y_M=\frac{w_M}{D_M},\qquad
 x_M=16B_M.                                         \tag{16}
\]

Then exactly

\[
 x_M=y_M+q_M.                                       \tag{17}
\]

Moreover \(q_M\) is already reduced. Indeed,
\(P_M\equiv D_Mc_M\pmod {R_M}\), while \(P_M\) and \(D_M\) are units
modulo \(R_M\), so

\[
 (c_M,R_M)=1.                                       \tag{18}
\]

The real BBP increment is

\[
 x_{M+1}-x_M
 =16(B_{M+1}-B_M)
 =\frac{a(M+1)}{16^M}.                              \tag{19}
\]

Combining (15), (17), and (19) gives a closed recurrence for the actual
changing odd quotient:

\[
 \boxed{
 q_{M+1}
 =q_M+\frac{a(M+1)}{16^M}+y_M-y_{M+1}.}             \tag{20}
\]

Thus nonnesting of \(R_M\) is not an obstacle to evolving \(c_M/R_M\):
start from one exact \(q_M\), generate \(w_{M+1}\) by (15), and reduce the
rational in (20); its denominator is exactly \(R_{M+1}\).

Let \(z_M=\{q_M\}\). Modulo one, (20) says

\[
 z_{M+1}-z_M+y_{M+1}-y_M
 \equiv\frac{a(M+1)}{16^M}\pmod1.                   \tag{21}
\]

The right side is exponentially small, while \(y_M\) frequently makes
macroscopic jumps. The odd quotient compensates those jumps almost exactly.
This is a rigid correlation, not a source of independent samples.

## 4. The actual high-prime coordinates are explicit

Use the two clean prime bands from the corrected parent report:

\[
\begin{aligned}
 \mathcal P_{1,M}={}&
 \{p\ {\rm prime}:4M+3<p\leq8M+1,\ p\equiv1\pmod8\}\\
 &\cup
 \{p\ {\rm prime}:4M+3<p\leq8M+5,\ p\equiv5\pmod8\},\\
 \mathcal P_{2,M}={}&
 \{p\ {\rm prime}:(8M+5)/3<p\leq4M+3\}.
\end{aligned}                                       \tag{22}
\]

Every \(p\) in these bands occurs exactly once in \(R_M\). Define its
additive CRT coordinate by

\[
 \gamma_{M,p}
 \equiv c_M(R_M/p)^{-1}\pmod p.                     \tag{23}
\]

Because \(B_M=P_M/(16D_MR_M)\) and
\(P_M\equiv D_Mc_M\pmod p\),

\[
 \gamma_{M,p}\equiv16pB_M\pmod p.                   \tag{24}
\]

Only the unique \(p\)-singular summand of \(B_M\) survives after
multiplication by \(p\). If its index is \(k_p\), then

\[
 \gamma_{M,p}\equiv16^{1-k_p}p\,a(k_p)\pmod p.      \tag{25}
\]

All three possible localized computations are constant:

| singular factor | congruence class | \(p\,a(k_p)\) | \(16^{1-k_p}\) | \(\gamma_{M,p}\) |
|---|---:|---:|---:|---:|
| \(4k+3=p\) | \(p\equiv3\pmod4\) | \(-1/2\) | \(64\) | \(-32\) |
| \(8k+1=p\) | \(p\equiv1\pmod8\) | \(4\) | \(16\) | \(64\) |
| \(8k+5=p\) | \(p\equiv5\pmod8\) | \(-1\) | \(-64\) | \(64\) |

For example, at \(k=-3/4\), the numerator is \(5/4\) and the other
three denominator factors multiply to \(-5/2\), giving
\(p\,a(k)=-1/2\). Fermat gives
\(16^k=2^{p-3}=1/4\), hence \(16^{1-k}=64\). The other two rows follow
from the supplementary law for \((2/p)\).

Put

\[
\begin{aligned}
 \mathcal P_M^+
 &=\mathcal P_{1,M}\cup
   \{p\in\mathcal P_{2,M}:p\equiv1\pmod4\},\\
 \mathcal P_M^-
 &=\{p\in\mathcal P_{2,M}:p\equiv3\pmod4\}.
\end{aligned}                                       \tag{26}
\]

Then the full actual local result is

\[
 \boxed{
 \gamma_{M,p}=
 \begin{cases}
 64\pmod p,&p\in\mathcal P_M^+,\\
 -32\pmod p,&p\in\mathcal P_M^-.
 \end{cases}}                                       \tag{27}
\]

This is numerator information, not merely denominator survival. It extends
past the two clean bands. More generally, let \(p>5\) be prime with
\(p^2>8M+5\), put \(\chi_p=(2/p)\), and sum over positive odd
multipliers \(m\):

\[
\begin{aligned}
 G_{M,p}={}&
 -\sum_{mp\leq2M+1}\frac{8}{m4^{m-1}}\\
 &-\sum_{\substack{mp\leq4M+3\\mp\equiv3\ (4)}}
       \frac{2^{6-m}}m\\
 &+\sum_{\substack{mp\leq8M+1\\mp\equiv1\ (8)}}
       \frac{64\chi_p}{m2^{(m-1)/2}}\\
 &-\sum_{\substack{mp\leq8M+5\\mp\equiv5\ (8)}}
       \frac{64\chi_p}{m2^{(m-1)/2}}.
\end{aligned}                                       \tag{27a}
\]

Each summand is the localization of one factor
\(2k+1=mp\), \(4k+3=mp\), \(8k+1=mp\), or \(8k+5=mp\).
The hypotheses make every multiplier a \(p\)-unit and prevent \(p^2\)
from dividing a linear factor. Thus the same calculation as (24)--(25)
gives the precise survival criterion

\[
 G_{M,p}\not\equiv0\pmod p
 \quad\Longleftrightarrow\quad v_p(R_M)=1.           \tag{27b}
\]

On this equivalent event,
\(\gamma_{M,p}\equiv G_{M,p}\pmod p\). If the residue vanishes, the
possible factor \(p\) cancels and \(\gamma_{M,p}\) is not defined. This
distinction occurs in small rows and is why rational nonvanishing alone is
insufficient below the height cutoff.

When \(p>M\), only \(m=1\) occurs in the first sum, at most \(m=1,3\)
in the second, and at most \(m=1,3,5,7\) in the last two. According to
the interval containing \(p\) and whether \(p\equiv1\) or \(3\pmod4\),
the nonempty local sum is one of:

| prime interval | \(p\equiv1\pmod4\) | \(p\equiv3\pmod4\) |
|---|---:|---:|
| \(p>(8M+5)/3\) | \(64\) | \(-32\) |
| \(2M+1<p\leq(8M+5)/3\) | \(64\) | \(-128/3\) |
| \((8M+5)/5<p\leq2M+1\) | \(56\) | \(-152/3\) |
| \((4M+3)/3<p\leq(8M+5)/5\) | \(264/5\) | \(-152/3\) |
| \((8M+5)/7<p\leq(4M+3)/3\) | \(752/15\) | \(-152/3\) |
| \(M<p\leq(8M+5)/7\) | \(752/15\) | \(-1040/21\) |

The table is restricted to primes that actually divide at least one linear
factor; impossible residue classes in the top range are simply absent. The
prime divisors of all eight rational numerators and denominators are at most
47. Hence, for \(M\geq48\), every possible denominator prime \(p>M\)
has \(G_{M,p}\not\equiv0\pmod p\), occurs in \(R_M\) to exponent one, and
has the explicit coordinate (27b).

Let

\[
 \mathcal Q_M=
 \{p\ {\rm prime}:p>M,\ p\mid
  (2k+1)(4k+3)(8k+1)(8k+5)
  \text{ for some }0\leq k\leq M\}.                 \tag{27c}
\]

Every prime \(M<p\leq4M+O(1)\) lies in this set, while above \(4M\)
exactly the residue classes \(1,5\pmod8\) occur up to \(8M+O(1)\).
The PNT/AP therefore gives

\[
 \sum_{p\in\mathcal Q_M}\log p=(5+o(1))M.           \tag{27d}
\]

Thus (27b) determines the actual additive coordinate on a divisor of
\(R_M\) with logarithm \((5+o(1))M\).

The localization can be pushed to a moving cutoff. For a reduced nonzero
rational \(u\), write \(H(u)\) for the maximum of the absolute numerator and
the positive denominator. The contributions in (27a) have a fixed sign
after grouping by multiplier blocks. More explicitly, for
\(p\equiv1,5\pmod8\), block \(j\geq0\), in its order of appearance as
\(M\) increases, consists of one positive term followed by three negative
terms. Its completed value is

\[
 \frac1{16^j}\left(
 \frac{64}{8j+1}-\frac8{2j+1}
 -\frac{16}{8j+5}-\frac8{4j+3}
 \right)
 =\frac{16a(j)}{16^j}>0.                           \tag{27e+}
\]

For \(p\equiv3,7\pmod8\), block \(j\) consists of three negative terms
followed by one positive term, and its completed value is

\[
 -\frac1{16^j}
 \left(
  \frac8{2j+1}+\frac{32}{4j+1}
  +\frac{32}{8j+3}-\frac8{8j+7}
 \right)<0.                                        \tag{27e-}
\]

Blocks do not interleave. In the first case, every successive partial sum
within a block decreases to the still-positive completed value. In the
second case, it remains negative before and after the final positive term.
Adding completed earlier blocks preserves the same sign. Hence every
nonempty partial localization has the sign determined by \(p\bmod4\), and
in particular

\[
 G_{M,p}\ne0\quad\hbox{over }\mathbb Q.             \tag{27e}
\]

If \(p>M/L\), put \(N=\lfloor(8M+5)/p\rfloor\), so
\(N\leq8L+O(1)\). A common denominator for (27a) divides
\[
 2^{2N}\operatorname{lcm}(1,\ldots,N).
\]
The elementary Chebyshev bound
\(\log\operatorname{lcm}(1,\ldots,N)=O(N)\) makes its logarithm \(O(L)\).
Moreover, the sums of the absolute values of all four multiplier families
are bounded uniformly in \(N\): after the factors \(1/m\), their powers of
two decay geometrically. The reduced numerator is therefore at most an
absolute constant times the displayed common denominator. Hence there is an
absolute constant \(C_0\) such that

\[
 \log H(G_{M,p})\leq C_0L.                          \tag{27f}
\]

Choose a fixed \(A>4C_0\) and, for sufficiently large \(M\), put

\[
 L_M=\left\lfloor
 \frac{\log M}{A}
 \right\rfloor.                                    \tag{27g}
\]

For all sufficiently large \(M\), a prime \(p>M/L_M\) satisfies
\(p^2>8M+5\), every multiplier is a \(p\)-unit, and (27f) gives
\(H(G_{M,p})\leq M^{1/4}<p\). Hence its nonzero numerator cannot vanish
modulo \(p\).
Every possible denominator prime above \(M/L_M\) therefore survives to
exponent one with the explicit coordinate (27b).

Let \(\mathcal Q_M^\star\) be the possible denominator primes
\(p>M/L_M\). The union of all possible prime supports has logarithmic mass

\[
 4M+2M+o(M)=6M+o(M):                                \tag{27h}
\]

all primes up to \(4M+O(1)\), followed by the two classes
\(1,5\pmod8\) up to \(8M+O(1)\). Discarding primes at most \(M/L_M\)
costs \(O(M/\log M)=o(M)\), so

\[
 \sum_{p\in\mathcal Q_M^\star}\log p=(6+o(1))M.     \tag{27i}
\]

## 5. The only remaining odd modulus has sublinear prime support

Let

\[
 S_M=\prod_{p\in\mathcal Q_M^\star}p,
 \qquad C_M=\frac{R_M}{S_M}.                         \tag{28}
\]

For all sufficiently large \(M\), (27b) and (27f)--(27g) prove that these
primes occur to exponent one, so \((S_M,C_M)=1\). By construction and the
noncancellation just proved, every prime factor of \(C_M\) is at most

\[
 Y_M=M/L_M=O(M/\log M)=o(M).                        \tag{29}
\]

It remains to control prime powers. Put \(X_M=8M+5\). For \(p>5\), no two
of the four linear factors in (2) can be divisible by \(p\) at the same
index: their pairwise common divisors divide \(1,3,4,\) or \(5\).
Consequently

\[
 v_p(R_M)\leq\lfloor\log_pX_M\rfloor\qquad(p>5).    \tag{30}
\]

The fixed primes 3 and 5 have the harmless bound
\(v_p(R_M)\leq4\lfloor\log_pX_M\rfloor\). Therefore

\[
\begin{aligned}
 \log C_M
 &\leq\vartheta(Y_M)
   +\sum_{\ell\geq2}\vartheta(X_M^{1/\ell})
   +O(\log M)\\
 &=o(M).                                            \tag{31}
\end{aligned}
\]

The first term is the squarefree support; the remaining sum is
\(O(\sqrt M\log M)=o(M)\). This proves (1). In particular,

\[
 P^+(C_M)\leq M/L_M=O(M/\log M)=o(M)
 \qquad(C_M>1).                                     \tag{32}
\]

This sharpens (1): the surviving cofactor is subexponential. Conversely,
every denominator prime belongs to the possible support in (27h), and the
higher-prime-power contribution is \(o(M)\). Together with (27i), this also
gives the exact denominator asymptotic

\[
 \boxed{\log R_M=(6+o(1))M.}                        \tag{32a}
\]

Despite (31), size alone does not make a power of 10 assume a prescribed
residue modulo \(C_M\) in only \(O(M)\) steps.

## 6. Exact CRT decomposition and the single surviving coordinate

Define the cofactor coordinate

\[
 0\leq\eta_M<C_M,\qquad
 \eta_M\equiv c_MS_M^{-1}\pmod {C_M},               \tag{33}
\]

with \(\eta_M=0\) if \(C_M=1\). For each
\(p\in\mathcal Q_M^\star\), let
\(\widehat\gamma_{M,p}\in\{0,\ldots,p-1\}\)
be the integer residue of the rational number \(G_{M,p}\) modulo \(p\),
and put

\[
 \Xi_M=\sum_{p\in\mathcal Q_M^\star}
       \frac{\widehat\gamma_{M,p}}p.                 \tag{33a}
\]

The additive CRT decomposition and (27b) give

\[
 \boxed{
 \frac{c_M}{R_M}
 \equiv
 \Xi_M+\frac{\eta_M}{C_M}\pmod1.}                   \tag{34}
\]

Every summand in (33a) is explicit: the eight-entry table applies when
\(p>M\), while (27a) has only \(O(L_M)\) terms when
\(M/L_M<p\leq M\). On the original clean subset, signed representatives
recover

\[
 64\sum_{p\in\mathcal P_M^+}\frac1p
 -32\sum_{p\in\mathcal P_M^-}\frac1p,               \tag{35}
\]

but the additional rational coordinates can contribute fixed fractions
after modular inversion and must not be discarded.

There is still a useful exact lacunary form. Recall
\(A_n=(10^n-16)/16\) and put

\[
 \rho_M=\frac{\Xi_M}{16},
 \qquad
 A_n\Xi_M=10^n\rho_M-\Xi_M.                         \tag{38}
\]

Combining (17), (34), and (38), the complete phase is

\[
 \boxed{
 (10^n-16)B_M
 \equiv
 A_n\left(
 y_M+\Xi_M+\frac{\eta_M}{C_M}
 \right)\pmod1.}                                    \tag{39}
\]

Here \(y_M\) is generated by the closed carry (15), \(\Xi_M\) is the
explicit high-prime sum (33a), and only the single residue
\(\eta_M\bmod C_M\) remains unexpanded.

## 7. The genuinely narrower surviving estimate

Define

\[
 \kappa_M=y_M+\Xi_M,\qquad
 \mathcal E_M=
 \min_{M\leq n\leq\lfloor\lambda M\rfloor}
 \left\|
 A_n\left(\kappa_M+\frac{\eta_M}{C_M}\right)
 \right\|_{\mathbb T}.                              \tag{40}
\]

Equations (5) and (39) give the exact necessary-and-sufficient statement

\[
 \boxed{
 \liminf_{M\to\infty}\mathcal E_M=0
 \quad\Longleftrightarrow\quad
 \text{the fixed-sixteen return}
 \quad\Longleftrightarrow\quad \mathrm{V1}.}         \tag{41}
\]

Equation (40) is narrower than the parent report's undifferentiated odd
quotient: the actual coordinates on \(\exp((6+o(1))M)\) prime mass and the
complete dyadic coordinate have been removed explicitly. The only
unexpanded arithmetic datum is one residue on the cofactor \(C_M\), with
\(P^+(C_M)=O(M/\log M)\) and \(\log C_M=o(M)\).

An exponential-sum route is now equally precise. With

\[
 T_M=\lfloor\lambda M\rfloor-M+1,
\]

set

\[
 \mathcal S_{M,h}
 =\sum_{n=M}^{\lfloor\lambda M\rfloor}
 e\!\left(
 hA_n\kappa_M
 \right)
 e\!\left(
 \frac{hA_n\eta_M}{C_M}
 \right).                                           \tag{42}
\]

If along some unbounded sequence of depths

\[
 \frac{\mathcal S_{M,h}}{T_M}\longrightarrow0
 \qquad\text{for every fixed }h\ne0,                \tag{43}
\]

then the proportional rows converge weakly to Haar measure by the Weyl
criterion, hence (40) tends to zero along that subsequence. This would prove
the return. The known first factor in (42) is a synchronized unit weight;
discarding it or bounding only one CRT component does not bound the product.

No estimate of type (43) was proved. General power-generator bounds concern
complete or substantially longer orbits, averages over moduli, or generic
starting points. Here \(T_M\asymp M\) while \(\log C_M=o(M)\), but \(C_M\)
may still be much larger than \(T_M\), its residue \(\eta_M\) is selected by
pi's four-pole recurrence, the modulus changes with \(M\), and the explicit
first factor in (42) is synchronized with it.

## 8. Falsified shortcuts

The recurrences and localization make four tempting shortcuts untenable.

1. **Cross-depth independence.** Equation (21) shows near-perfect
   compensation between the dyadic and odd coordinates. They do not supply
   two independent samples.
2. **Large explicit-prime mass implies cancellation.** The local coordinates
   are exact rational localizations: eight constants above \(M\), and an
   \(O(\log M)\)-term formula below. Their synchronized product is the single
   lacunary phase (38). Every factor has modulus one.
3. **Rational nonvanishing implies nonvanishing modulo every prime.**
   Equation (27e) rules out \(G_{M,p}=0\) over \(\mathbb Q\), but its
   numerator can still be divisible by \(p\). The exact replay finds 88 such
   modular cancellation rows through \(M=240\), beginning with
   \((M,p)=(9,19)\). This is precisely why the height comparison following
   (27f), rather than the sign argument alone, is needed.
4. **A subexponential cofactor must be hit in an \(O(M)\) row.** The bound
   \(\log C_M=o(M)\) still allows, for example, \(C_M=\exp(\sqrt M)\), far
   more residues than the \((\lambda-1)M+O(1)\) available exponents. More
   importantly, the cofactor factor is multiplied by the synchronized
   explicit unit weight in (42). Size alone supplies neither a compatible
   discrete logarithm nor a weighted short-orbit discrepancy bound.

As an "experiment", exact proportional-row minima are not monotone:

\[
 \Delta_{20}=0.001144132300430\ldots,\qquad
 \Delta_{21}=0.072845332310798\ldots .               \tag{44}
\]

Through depth 500, the finite proportional record remains the depth-five
value \(0.000159642895927\ldots\). Finite absence of a better return is not
evidence that no return exists.

## 9. Exact finite replay

The script
[bbp_actual_odd_quotient_check.py](bbp_actual_odd_quotient_check.py)
has SHA-256
c5f55d07feb84aa53285c8e0aee0bf32654a1bd7aed207ad518acfc07941d053.
It uses only integers, Python Fraction, gcds, and modular inverses. It imports
no branch checker. It verifies the source and parent hashes, the functional
equation at finite precision, the complete carry recurrence, the reduced
odd-quotient recurrence, all clean and high-prime CRT constants, the
general localization formula and its rational sign, every finite instance
protected by the height criterion, the cofactor support and exponent bounds,
the exact CRT reconstruction, the phase factorization, and the compensation
law.

Run:

    python -m py_compile \
      work/ultrapi-resume/bbp_actual_odd_quotient_check.py
    python work/ultrapi-resume/bbp_actual_odd_quotient_check.py \
      --max-depth 240

Retained output:

    claim_status=experiment
    source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    parent_report_sha256=eed140ef58160c09ae65b2596105882ff7614440b36ce45a9c94185bcf881e7d
    functional_equation_checks=238
    carry_recurrence_checks=238
    quotient_recurrence_checks=238
    clean_crt_coordinate_checks=14566
    all_high_prime_coordinate_checks=21801
    generic_localization_checks=27597
    rational_localization_sign_checks=27597
    height_protected_nonvanishing_checks=20583
    genuine_mod_p_local_cancellation_rows=88
    first_genuine_mod_p_local_cancellations=[(9, 19), (10, 19), (11, 19), (12, 19), (13, 19), (14, 19), (15, 19), (19, 13)]
    cofactor_support_checks=21321
    crt_decomposition_checks=432
    phase_factorization_checks=12040
    compensation_checks=476
    large_dyadic_jumps_over_one_quarter=126
    last_p_gt_M_cofactor_log_ratio=1.109965511667064
    last_p_gt_M_signed_component=3.757333809018680
    proportional_monotonicity_falsifier=M20:0.001144132300430->M21:0.072845332310798
    finite_proportional_record=M5:n5:0.000159642895927
    all exact checks passed

An additional run through depth 500 also passed, including 109166 general
localization/sign checks, 83564 height-protected nonvanishing checks, and 163
observed modular-cancellation rows.

Every finite row has status "experiment"; none proves (31), (43), or V1.

## 10. Dated literature and applicability audit

| Source | Checked statement | Exact scope here |
|---|---|---|
| [Bailey--Borwein--Plouffe, On the Rapid Computation of Various Polylogarithmic Constants (1997), Theorem 1](https://doi.org/10.1090/S0025-5718-97-00856-9) | The four-pole series (2). | Source of the coefficient recurrence; no decimal-distribution estimate. |
| [Barsky--Muñoz--Pérez-Marco, On the genesis of BBP formulas (2021)](https://arxiv.org/abs/1906.09629) | Logarithmic and null-formula provenance for BBP identities. | Does not state (15), (20), (27), or a fixed return. |
| [Lagarias, On the Normality of Arithmetical Constants (2001), Theorem 4.1](https://arxiv.org/abs/math/0101055v2) | BBP remainder dynamics; digit-density consequences remain conditional on a dichotomy hypothesis. | Confirms that a pointwise estimate such as (43) is not supplied by the standard BBP framework. |
| [Aistleitner--Fukuyama, Extremal discrepancy behavior of lacunary sequences (2014)](https://arxiv.org/abs/1403.1630v2) | Quantitative lacunary discrepancy results for almost every real parameter. | A metric theorem cannot be specialized to the selected diagonal parameters \(\kappa_M+\eta_M/C_M\), much less to pi. PDF SHA-256: 4c2990ec21a5962bfee2f7d603074d71b987e1dddaa1a885b3c55934f1749eea. |
| [Konyagin--Shparlinski, On the consecutive powers of a primitive root: gaps and exponential sums (2012)](https://doi.org/10.1112/S0025579311002117) | Uniform gap and exponential-sum bounds for \(ag^n\bmod p\) with \(g\) a primitive root of a prime modulus. | The cofactor \(C_M\) is composite and varying, 10 need not be a primitive root (or even a unit at its 5-part), and (42) carries an additional synchronized weight. |
| [Bennett--Martin--O'Bryant--Rechnitzer, Explicit bounds for primes in arithmetic progressions (2018), Theorem 1.2](https://arxiv.org/abs/1802.00085v3) | For fixed reduced \(a\bmod q\), \(\theta(x;q,a)=x/\varphi(q)+O(x/\log x)\), explicitly. | Supplies more than the fixed-modulus PNT/AP input used in (27d), (27h), and (27i); it says nothing about numerator cancellation. |

Fresh searches on 2026-08-12 UTC combined “lacunary discrepancy”, “powers
modulo composite modulus”, “short exponential sums”, “power generator”, and
“BBP numerator recurrence”. The closest results were metric in the real
parameter, averaged over moduli, restricted to prime moduli and primitive
roots, or nontrivial only once the orbit length exceeds a positive-power
threshold in the modulus. The estimate \(\log C_M=o(M)\) alone does not imply
\(T_M\gg C_M^\delta\) for any fixed \(\delta>0\). No primary theorem located
in this bounded search applies to the weighted composite-modulus sum (42).
This is an applicability record, not a claim that the literature is
exhausted.

A same-date mathlib search found
[Chebyshev.psi_eq_log_lcmUpto](../../.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean)
and explicit Chebyshev bounds, plus Dirichlet infinitude in
[LSeries/PrimesInAP.lean](../../.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/PrimesInAP.lean),
but no formalized PNT/AP asymptotic suitable for (27h). No formal declaration
is added in this branch.

## Sharp conclusion

The actual odd quotient is no longer a completely opaque Euclidean
remainder. It obeys the closed cross-depth recurrence (20); its entire prime
coordinate above \(M/L_M\), where \(L_M\asymp\log M\), is the explicit
localization (27a)--(27b); and all remaining odd uncertainty is one residue
\(\eta_M\) on a cofactor \(C_M\) satisfying
\(P^+(C_M)=O(M/\log M)\) and \(\log C_M=o(M)\).

The same calculation also explains why these advances do not yet prove a
return. The odd quotient is forced to compensate the dyadic carry, and the
remaining phase is a selected, weighted \(O(M)\)-term sum along powers of
10. Proving (40), or the concrete sufficient estimate (43), would prove the
fixed return and hence V1. No such estimate was obtained, so V1 remains a
"conjecture".
