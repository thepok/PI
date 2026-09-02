Status: `proof sketch`; independently audited at proof level for Theorem A on
2026-09-02; Theorems B and C not yet independently audited.
Date: 2026-09-02.
Provenance: Produced by a ChatGPT Pro run from the repository's separator
sketches, corrected after an adversarial audit, and reviewed by Claude.

# Finite-word avoidance, badly approximable points, and all-label fresh-window abundance

## Abstract

Let \(w\) be a nonempty decimal word, \(P\) a finite \(w\)-free prefix, and \(C_w\) the set of reals in \([0,1)\) whose canonical decimal expansion avoids \(w\). We prove two full-relative-dimension theorems.

First,

$$
\dim_H\bigl(C_w\cap[P]\cap\mathrm{BA}\cap\mathrm{Trans}\bigr)
=\dim_H C_w
=\frac{h_w}{\log 10}
=\frac{\log\rho_w}{\log 10}.
$$

This is obtained from guarded self-similar subsystems and the established fractal theorems for badly approximable points.

Second, if \(A\) is a nine-digit alphabet such that every word over \(A\) avoids \(w\), and \(c\in A\cap\{1,\ldots ,8\}\), then the set satisfying the repository-strength all-label property

$$
\forall k\ge k_0\;\forall u\in A^k\;\exists n\in[10^k+1,10^{k+1})
:\quad a_{n+1}\cdots a_{n+k+1}=uc
$$

has full dimension in \(C_w\cap[P]\); almost every point for a natural Perron–Frobenius measure is transcendental and has irrationality exponent \(2\).

These results cannot presently be intersected by the standard friendly-measure argument. We prove a precise obstruction: the all-label set contains no positive-dimensional Ahlfors-regular subset. Thus the forced de Bruijn Moran construction fails the power-law and absolute-decay hypotheses of Kleinbock–Weiss, Kristensen–Thorn–Velani, and Fishman. Simultaneous bad approximability and all-label abundance remains unproved here.

The decimal-orbit consequences used by T191–T194 are then recorded with the corrections required by the audit: the predecessor coordinate is properly quantified, omega-limit dynamics are formulated on the circle, canonical endpoint discrepancies are separated, and the free-phase T192–T193 statement is identified as an ordinary-mathematics generalization rather than a current generic Lean theorem.

---

## 1. Definitions and statements

Use the canonical decimal expansion, the one not eventually equal to \(9\):

$$
x=0.a_1(x)a_2(x)\ldots ,
\qquad
T(x)=\{10x\}.
$$

Let \(w=w_1\cdots w_m\), \(m\ge1\), and define

$$
C_w=\{x\in[0,1):a_j(x)\cdots a_{j+m-1}(x)\ne w
\text{ for every }j\ge1\}.
$$

For a finite word \(P\), let \([P]\) be its canonical decimal cylinder.

A **proper alphabet for \(w\)** is a set

$$
A\subset\{0,\ldots ,9\},\qquad |A|=9,
$$

such that \(w\notin A^m\). Equivalently, the unique digit omitted from \(A\) occurs somewhere in \(w\). Therefore every finite word over \(A\) is \(w\)-free. Since \(A\) omits only one digit,

$$
A\cap\{1,\ldots ,8\}\ne\varnothing.
$$

Fix \(c\in A\cap\{1,\ldots ,8\}\). We say that \(x\) has **central all-label abundance**, denoted \(\mathrm{ALA}_{A,c}\), if

$$
\exists k_0\;\forall k\ge k_0\;\forall u\in A^k\;
\exists n,\qquad
10^k+1\le n<10^{k+1},
\quad
a_{n+1}(x)\cdots a_{n+k+1}(x)=uc.                 \tag{1.1}
$$

This is slightly stronger than merely requiring \(u\), and matches the repository’s central-positive-unit formulation.

### Theorem A — the corrected Diophantine separator

For every nonempty \(w\) and every finite \(w\)-free prefix \(P\),

$$
\boxed{
\dim_H\bigl(C_w\cap[P]\cap\mathrm{BA}\cap\mathrm{Trans}\bigr)
=\dim_H C_w
=\frac{h_w}{\log 10}
=\frac{\log\rho_w}{\log 10}.
}                                                       \tag{1.2}
$$

Every point in this set is irrational, has irrationality exponent \(2\), satisfies `IrrationalityMeasureBelow x 8`, has the untimed and timed central returns used in the ordinary generic reconstruction of T194, and has the exact predecessor floor and coordinate identities.

### Theorem B — full-dimensional all-label abundance with exponent \(2\)

For every \(w,P,A,c\) as above,

$$
\boxed{
\dim_H\left(
C_w\cap[P]\cap\mathrm{ALA}_{A,c}
\cap\mathrm{Trans}\cap\{x:\mu(x)=2\}
\right)
=\dim_H C_w.
}                                                       \tag{1.3}
$$

Here \(\mu(x)\) denotes the classical irrationality exponent.

### Theorem C — regularity obstruction

Let

$$
E_{w,P,A}=
\{x\in C_w\cap[P]:x\text{ has all-label abundance over }A\}.
$$

Then \(E_{w,P,A}\) contains no nonempty Ahlfors-regular subset of positive dimension. Equivalently, its Ahlfors-regularity dimension is zero:

$$
\dim_R E_{w,P,A}=0.                                    \tag{1.4}
$$

Consequently the friendly-measure, self-similar, and ordinary Ahlfors-regular Schmidt-game theorems cannot be applied to a compact Moran set on which all-label abundance is imposed pointwise.

The simultaneous conclusion

$$
\dim_H\bigl(
C_w\cap[P]\cap\mathrm{BA}\cap\mathrm{Trans}
\cap\mathrm{ALA}_{A,c}
\bigr)=\dim_H C_w                                      \tag{1.5}
$$

is therefore **not proved here**. Theorem C invalidates the suggested direct proof but does not disprove (1.5).

---

## 2. Entropy and guarded self-similar subsystems

Let \(\mathcal A_w(L)\) be the set of \(w\)-free words of length \(L\), and set

$$
N_w(L)=|\mathcal A_w(L)|.
$$

Restriction to the first \(L\) and last \(R\) digits gives an injection

$$
\mathcal A_w(L+R)\longrightarrow
\mathcal A_w(L)\times\mathcal A_w(R),
$$

hence

$$
N_w(L+R)\le N_w(L)N_w(R).                              \tag{2.1}
$$

Fekete’s lemma gives

$$
h_w=\lim_{L\to\infty}\frac{\log N_w(L)}{L}.
                                                               \tag{2.2}
$$

The prefix-suffix automaton for \(w\) has states \(0,\ldots ,m-1\), with state \(r\) recording the longest suffix equal to a prefix of \(w\). The transition completing \(w\) is deleted. If \(M_w\) is its adjacency matrix and \(\rho_w\) its Perron–Frobenius eigenvalue, then

$$
h_w=\log\rho_w.                                        \tag{2.3}
$$

Moreover,

$$
9\le\rho_w<10.                                         \tag{2.4}
$$

The lower bound follows by omitting \(w_1\). For the strict upper bound, every \(w\)-free word of length \(jm\), partitioned into aligned blocks of length \(m\), has at most \(10^m-1\) possibilities per block. Thus

$$
N_w(jm)\le(10^m-1)^j,
\qquad
\rho_w\le(10^m-1)^{1/m}<10.
$$

### Guarded systems

Choose

$$
b\in\{1,\ldots ,8\}\setminus\{w_1,w_m\}.
$$

For \(L\ge1\), define

$$
\mathcal V_L=\{\,b^mub^m:u\in\mathcal A_w(L)\,\},
\qquad
R_L=L+2m.
$$

For a decimal word \(v\) of length \(R_L\), put

$$
\phi_v(t)=\frac{[v]_{10}+t}{10^{R_L}},
$$

and let \(K_L\) be the associated attractor.

Every concatenation of words in \(\mathcal V_L\) avoids \(w\). An occurrence lying inside \(u\) is excluded by definition. An occurrence beginning in a guard has first digit \(b\ne w_1\). An occurrence entering a guard ends there and has last digit \(b\ne w_m\). A word of length \(m\) cannot cross an entire guard of length \(m\).

If \(P\) is \(w\)-free, then

$$
K_{L,P}:=\psi_{P,b}(K_L)\subset C_w\cap[P],
\qquad
\psi_{P,b}(z)=\frac{[Pb^m]_{10}+z}{10^{|P|+m}}.         \tag{2.5}
$$

For \(u\ne u'\),

$$
\left|[b^mub^m]_{10}-[b^mu'b^m]_{10}\right|
=10^m|[u]_{10}-[u']_{10}|
\ge10^m.
$$

Since the images have diameter at most \(10^{-R_L}\), the first-level gap is at least

$$
\frac{10^m-1}{10^{L+2m}}>0.                            \tag{2.6}
$$

Thus the system satisfies strong separation.

Hutchinson’s Theorem 5.3 gives

$$
\dim_HK_L
=s_L
=\frac{\log N_w(L)}{(L+2m)\log10}.                     \tag{2.7}
$$

Therefore

$$
s_L\longrightarrow\frac{h_w}{\log10}.                 \tag{2.8}
$$

Conversely, \(C_w\) is covered by \(N_w(L)\) level-\(L\) decimal cylinders. This gives

$$
\dim_HC_w\le\frac{h_w}{\log10}.
$$

The inclusion \(K_L\subset C_w\) and (2.8) give the reverse inequality, proving

$$
\dim_HC_w=\frac{h_w}{\log10}
=\frac{\log\rho_w}{\log10}.                            \tag{2.9}
$$

For \(m=1\), the symbolic nine-map deleted-digit attractor and the canonical set \(C_w\) can differ at terminating rationals represented by eventually-\(9\) expansions. Their symmetric difference is countable. The dimension and badly approximable conclusions are unchanged. The guarded systems themselves have infinitely many digits \(b\le8\), so their coding is canonical.

---

## 3. Badly approximable points: proof of Theorem A

We use the following cited result.

**Kleinbock–Weiss, Theorem 1.1 and Corollary 1.2.**
If a finite measure on \(\mathbb R^n\) is Federer and absolutely decaying, badly approximable vectors have the lower local dimension asserted in every open ball of positive measure. If in addition the measure satisfies a power law—equivalently here, is Ahlfors regular—then the intersection with the badly approximable set has full local dimension.

The exact assumptions are Federer plus absolute decay; the power law is needed for the numerical local full-dimension conclusion. ([ResearchGate][1])

Alternatively, KTV Theorem 9 and Corollary 10 apply to an **irreducible** finite similarity system satisfying OSC, and Fishman Theorem 3.1 and Corollaries 5.3–5.4 give a winning refinement under the friendly/packing assumptions. Irreducibility cannot be omitted from their broad higher-dimensional IFS formulations. It is automatic for the present non-singleton one-dimensional systems. ([arXiv][2])

Let \(\nu_L\) be the uniform Bernoulli measure on \(K_L\). Every level-\(j\) cylinder has mass

$$
N_w(L)^{-j}=10^{-jR_Ls_L}.
$$

Strong separation implies

$$
c_1r^{s_L}\le\nu_L(B(x,r))\le c_2r^{s_L}.              \tag{3.1}
$$

Hence \(\nu_L\) is \(s_L\)-Ahlfors regular and Federer.

To verify absolute decay correctly, suppose

$$
B(x,r)\cap B(y,\varepsilon r)\cap K_L\ne\varnothing
$$

and choose \(z\) in this intersection. Then

$$
B(y,\varepsilon r)\cap K_L
\subset B(z,2\varepsilon r)\cap K_L.
$$

Using the upper Ahlfors estimate for the numerator and the lower estimate for \(B(x,r)\),

$$
\nu_L(B(x,r)\cap B(y,\varepsilon r))
\le C\varepsilon^{s_L}\nu_L(B(x,r)).                  \tag{3.2}
$$

Thus \(\nu_L\) is absolutely friendly. Kleinbock–Weiss Corollary 1.2 yields

$$
\dim_H(K_L\cap\mathrm{BA})=s_L,                        \tag{3.3}
$$

locally in every nonempty relative ball.

The map \(\psi_{P,b}\) preserves bad approximability. Indeed, if

$$
x=\frac{M+z}{10^R},
$$

then

$$
\left|x-\frac pq\right|
=10^{-R}
\left|z-\frac{10^Rp-Mq}{q}\right|.
$$

Thus a bad-approximation constant \(c\) for \(z\) gives \(c10^{-R}\) for \(x\). Transcendence is also preserved because

$$
z=10^Rx-M.
$$

The algebraic reals are countable, so

$$
\dim_H(K_{L,P}\cap\mathrm{BA}\cap\mathrm{Trans})=s_L.
$$

Letting \(L\to\infty\) and using (2.8) proves Theorem A.

---

## 4. Full-dimensional all-label abundance: proof of Theorem B

We use the prefix automaton of Section 2. It is primitive. A guard \(b^m\), with \(b\ne w_1,w_m\), is admissible after every \(w\)-free prefix and returns the automaton to state \(0\). State \(0\) also has a one-step loop using any digit different from \(w_1\), so the period is one.

Let \(r=(r_i)\) be a positive right Perron–Frobenius eigenvector:

$$
M_wr=\rho_wr.
$$

Starting after the prefix \(P\), define the Markov measure \(\nu_P\) by assigning an admissible labeled path

$$
i_0\longrightarrow i_1\longrightarrow\cdots\longrightarrow i_\ell
$$

probability

$$
\rho_w^{-\ell}\frac{r_{i_\ell}}{r_{i_0}}.             \tag{4.1}
$$

Since there are finitely many states,

$$
C^{-1}\rho_w^{-\ell}
\le\nu_P([v])
\le C\rho_w^{-\ell}                                   \tag{4.2}
$$

for every admissible cylinder \(v\) extending \(P\).

Consequently the push-forward decimal measure is

$$
s_w\text{-Ahlfors regular},
\qquad
s_w=\frac{\log\rho_w}{\log10}.                         \tag{4.3}
$$

The countable eventually-\(9\) endpoint discrepancy has measure zero.

Fix \(u\in A^k\). Since \(uc\) uses only digits of \(A\), it avoids \(w\). The word

$$
gucg,\qquad g=b^m,                                     \tag{4.4}
$$

is admissible after every automaton state. Its length is

$$
\ell_k=k+1+2m.
$$

By (4.1), conditional on any preceding admissible digits, the probability of seeing this exact word is at least

$$
p_k\ge C_0\rho_w^{-k}.                                \tag{4.5}
$$

Inside

$$
[10^k+1,10^{k+1})
$$

place

$$
M_k\ge C_1\frac{10^k}{k+2m+1}
$$

disjoint candidate blocks of length \(\ell_k\). Successive conditioning and (4.5) give

$$
\nu_P(u\text{ is absent from all candidates})
\le(1-p_k)^{M_k}
\le
\exp\left(
-C_2\frac{(10/\rho_w)^k}{k+2m+1}
\right).                                               \tag{4.6}
$$

There are \(9^k\) choices of \(u\). Hence the probability that at least one label fails at level \(k\) is at most

$$
\delta_k
\le
9^k
\exp\left(
-C_2\frac{(10/\rho_w)^k}{k+2m+1}
\right).                                               \tag{4.7}
$$

Because \(\rho_w<10\),

$$
\sum_k\delta_k<\infty.                                 \tag{4.8}
$$

Borel–Cantelli proves that \(\nu_P\)-almost every point satisfies \(\mathrm{ALA}_{A,c}\).

Since \(\nu_P\) is \(s_w\)-Ahlfors regular, every set of full \(\nu_P\)-measure has Hausdorff dimension \(s_w\). Therefore

$$
\dim_H(C_w\cap[P]\cap\mathrm{ALA}_{A,c})
=s_w=\dim_HC_w.                                        \tag{4.9}
$$

An Ahlfors-regular measure on the real line is Federer and absolutely decaying by the argument in (3.2). Kleinbock–Lindenstrauss–Weiss, Theorem 1.1, therefore implies that \(\nu_P\)-almost every point is not very well approximable. After removing the countable rational set, its irrationality exponent is exactly \(2\). Removing the countable algebraic set also leaves full measure. This proves Theorem B.

For comparison, Hochman–Shmerkin prove that natural measures on finite continued-fraction Cantor sets—hence measures supported entirely on badly approximable numbers—are pointwise normal in every integer base; see their Theorem 1.12. That nearby theorem demonstrates compatibility of bad approximability with strong digit randomness in the ambient interval, but it does not preserve a prescribed decimal avoidance subshift \(C_w\). ([arXiv][3])

---

## 5. Why the friendly-measure route cannot prove the simultaneous theorem

We now prove Theorem C.

Choose

$$
a\in A\cap\{1,\ldots ,8\}.
$$

For \(j\ge1\), let \(E_j\) be the set of points satisfying all-label abundance at every level \(k\ge j\). Then

$$
E_{w,P,A}=\bigcup_{j\ge1}E_j.                          \tag{5.1}
$$

Suppose, for contradiction, that a compact

$$
K\subset E_{w,P,A}
$$

supports a \(\delta\)-Ahlfors regular measure \(\mu\), with \(\delta>0\).

By (5.1), some \(E_j\) has positive \(\mu\)-measure inside \(K\). Remove the countable terminating rationals and choose a compact

$$
F\subset K\cap E_j
$$

with \(\mu(F)>0\).

Since \(\mu\) is doubling, the differentiation theorem applies. By Egorov’s theorem we may choose a compact \(D\subset F\), \(\mu(D)>0\), and \(r_0>0\), such that

$$
\mu(D\cap B(x,r))\ge\frac12\mu(B(x,r))
\quad
(x\in D,\ 0<r<r_0).                                   \tag{5.2}
$$

Construct \(x\in D\) greedily. Having chosen a decimal prefix \(v\), choose a next digit different from \(a\) whenever some point of \(D\cap[v]\) has such a next digit. Choose \(a\) only when every point of \(D\cap[v]\) has next digit \(a\). Compactness supplies an infinite resulting branch \(x\in D\).

For every sufficiently large \(k\), all-label abundance supplies an occurrence

$$
a_{n+1}(x)\cdots a_{n+k}(x)=a^k
$$

with

$$
10^k\le n<10^{k+1}.
$$

At each of these \(k\) positions the greedy construction chose \(a\). Therefore, at each corresponding prefix, no point of \(D\) has a different next digit. If \(I_n(x)\) denotes the level-\(n\) decimal cylinder containing \(x\), then

$$
D\cap I_n(x)\subset I_{n+k}(x).                       \tag{5.3}
$$

Because \(a\in\{1,\ldots ,8\}\), the point \(x\) lies a fixed proportion away from both endpoints of \(I_n(x)\). Thus there is

$$
r_n\asymp10^{-n},\qquad B(x,r_n)\subset I_n(x).
$$

From (5.3),

$$
D\cap B(x,r_n)
\subset B(x,C10^{-k}r_n).                              \tag{5.4}
$$

For large \(k\), \(r_n<r_0\), and (5.2) gives

$$
\mu(B(x,C10^{-k}r_n))
\ge\frac12\mu(B(x,r_n)).                               \tag{5.5}
$$

Ahlfors regularity would instead give

$$
\frac{\mu(B(x,C10^{-k}r_n))}
{\mu(B(x,r_n))}
\le C'10^{-k\delta}\longrightarrow0,                  \tag{5.6}
$$

contradicting (5.5).

Therefore no positive-dimensional Ahlfors-regular subset of \(E_{w,P,A}\) exists.

The same argument directly contradicts uniform absolute decay: at arbitrarily small relative radii \(\varepsilon_k\asymp10^{-k}\), a ball of radius \(\varepsilon_kr_n\) contains a fixed proportion of the mass of \(B(x,r_n)\).

### Consequences for the proposed construction

A forced de Bruijn packet lists all \(9^k\) labels and therefore forces every point of the constructed compact set to satisfy the constant-label requirement \(a^k\). The preceding argument produces arbitrarily long one-child portions of its digit tree. Hence:

1. its natural Moran measure is not Ahlfors regular;
2. it is not absolutely decaying;
3. it is not absolutely friendly;
4. KTV’s power-law condition and its irreducible self-similar corollary do not apply;
5. Kleinbock–Weiss Corollary 1.2 and Fishman’s friendly-measure theorem do not apply.

The fact that the forced digits have zero asymptotic density proves the Hausdorff-dimension statement but does **not** repair small-scale regularity. Density loss and uniform geometric regularity are different issues.

The theorem of Angelevska–Käenmäki–Troscheit says that a sub-self-conformal set having positive Hausdorff measure in its critical dimension is Ahlfors regular. It does not rescue this construction: the fresh-window property is tied to absolute positions and the resulting nonstationary set is not a finite sub-self-conformal system; Theorem C shows that no positive-dimensional Ahlfors-regular subsystem can be hidden inside the all-label set anyway. ([arXiv][4])

Thus the simultaneous BA assertion requires a method which genuinely works beyond friendly or positive-dimensional Ahlfors-regular supports—for example, a direct continued-fraction construction, a game with sparse specification obligations, or a new dimension theorem for intersections of BA with regularity-dimension-zero liminf sets.

---

## 6. Decimal-orbit consequences and the corrected T191–T194 interface

Put

$$
q=10^k,\qquad
A_k(n,x)=\lfloor qT^nx\rfloor,
\qquad
y_k(n,x)=qT^nx-A_k(n,x)-\frac12.
$$

Then exactly

$$
y_k(n,x)=T^{n+k}x-\frac12.                             \tag{6.1}
$$

Thus

$$
|y_k(n,x)|\le\frac9{22}
\iff
T^{n+k}x\in
J:=\left[\frac1{11},\frac{10}{11}\right].              \tag{6.2}
$$

A next digit in \(\{1,\ldots ,8\}\) places the orbit in

$$
\left[\frac1{10},\frac9{10}\right)
\subset J.                                             \tag{6.3}
$$

The interval is half-open, as required by the canonical decimal convention.

### Untimed central return

Every irrational \(x\) has arbitrarily late visits to \(J\).

Indeed, suppose that after time \(L\) the orbit avoids \(J\). It must remain in one of

$$
[0,1/11)
\quad\text{or}\quad
(10/11,1).
$$

In the lower component, avoidance gives

$$
T^{L+r}x=10^rT^Lx<1/11
\quad(r\ge0),
$$

forcing \(T^Lx=0\), hence \(x\in\mathbb Q\). In the upper component,

$$
1-T^{L+r}x=10^r(1-T^Lx)<1/11,
$$

which is impossible unless \(T^Lx=1\), again corresponding to a rational endpoint. This proves the claim.

### Timed return from `IrrationalityMeasureBelow x 8`

Suppose

$$
\operatorname{IrrationalityMeasureBelow}(x,8).
$$

Choose a witnessing \(\mu<8\) and take \(\varepsilon=8-\mu\). Then for all sufficiently large \(Q\),

$$
Q^{-8}<\left|x-\frac pQ\right|
\quad(p\in\mathbb Z).                                  \tag{6.4}
$$

If the orbit avoids \(J\) for every \(m\in[s,8s]\), the trapping argument gives, with \(Q=10^s\), either

$$
\left|x-\frac{\lfloor Qx\rfloor}{Q}\right|
<\frac1{11}10^{-8s}<Q^{-8}
$$

or the analogous inequality with numerator \(\lfloor Qx\rfloor+1\), contradicting (6.4).

Hence for all large \(s\) there is \(m\in[s,8s]\) with \(T^mx\in J\). Take

$$
s=10^k+1+k,\qquad n=m-k.
$$

Then, for \(k\ge3\),

$$
10^k+1\le n<10^{k+1}.                                 \tag{6.5}
$$

Bad approximability implies the exact Lean-style exponent premise by taking \(\mu=2\): if

$$
\left|x-\frac pq\right|\ge\frac c{q^2},
$$

then for every \(\varepsilon>0\), sufficiently large \(q\) satisfy

$$
q^{-(2+\varepsilon)}<cq^{-2}
\le\left|x-\frac pq\right|.                            \tag{6.6}
$$

### Corrected predecessor predicate

A **central witness** at level \(k\) is a tuple \((n,A,y)\) satisfying

$$
10^k+1\le n<10^{k+1},\quad
A<q,\quad
A=\lfloor qT^nx\rfloor,
$$

$$
y=qT^nx-A-\frac12,
\qquad
|y|\le\frac9{22}.                                      \tag{6.7}
$$

The corrected predecessor predicate quantifies \(y\):

$$
\begin{aligned}
P_6(x):\quad
\exists k_0\ \forall k\ge\max(3,k_0)\
\exists n,A,d,C,y:\quad&
q+1\le n<10q,\\
&A<q,\ d<10,\ C<10q,\\
&A=\lfloor qT^nx\rfloor,\\
&d=\lfloor10T^{n-1}x\rfloor,\\
&C=A+dq=\lfloor10qT^{n-1}x\rfloor,\\
&y=qT^nx-A-\frac12,\\
&T^nx-\frac{A+1/2}{q}=\frac yq,\\
&T^{n-1}x-\frac{C+1/2}{10q}=\frac y{10q},\\
&|y|\le\frac9{22}.
\end{aligned}                                          \tag{6.8}
$$

This is a closed proposition; the free-variable error is removed.

To prove the identities, set

$$
d=\lfloor10T^{n-1}x\rfloor.
$$

Then

$$
T^nx=10T^{n-1}x-d,
$$

so

$$
10qT^{n-1}x=dq+qT^nx.
$$

Taking floors gives

$$
\lfloor10qT^{n-1}x\rfloor=dq+A=C,
$$

and subtracting \(C+\tfrac12\) gives

$$
10qT^{n-1}x-C-\frac12
=qT^nx-A-\frac12=y.                                   \tag{6.9}
$$

Thus predecessor lifting is an identity once a timed central witness has been chosen.

### Infinite omega-limit set: the circle correction

Work on

$$
\mathbb T=\mathbb R/\mathbb Z
$$

with the circle metric, and let \(Tz=10z\) on \(\mathbb T\). This is a continuous map of a compact metric space. Define

$$
\omega_T(x)=
\bigcap_{N\ge0}
\overline{\{T^nx:n\ge N\}}^{\,\mathbb T}.
$$

If \(\omega_T(x)\) were finite, \(T\) would permute it. For some \(p\ge1\), \(T^p\) would fix every point of \(\omega_T(x)\). Since the orbit approaches its omega-limit set,

$$
d_{\mathbb T}(T^{n+p}x,T^nx)\to0.                     \tag{6.10}
$$

For

$$
u=(10^p-1)x
$$

this says

$$
\|10^nu\|_{\mathbb T}\to0.
$$

The trapping argument above then forces \(u\in\mathbb Q/\mathbb Z\), hence \(x\in\mathbb Q/\mathbb Z\), a contradiction. Therefore every irrational \(x\) has infinitely many circle omega-limit points.

### Status of T191–T194 genericization

T191 is genuinely stated with a free real \(y\). T192 and T193, at the audited commit, use `piOrbit n` syntactically, and the public T194 conclusions do not expose every internal coordinate \(y\).

Define at paper level a free-phase primitive atom

$$
\mathfrak p_{q,A}(z)
$$

by replacing `piOrbit n` in the repository definition by \(z\in[0,1)\). Inspection of the T192–T193 arguments shows that the phase is used only pointwise and through the central-coordinate equality. Replacing `piOrbit n` by \(z\) therefore gives the routine ordinary-mathematics generalization:

$$
z-\frac{A+1/2}{q}=\frac yq,\quad |y|\le\frac9{22}
$$

implies

$$
\Re\operatorname{boundaryMinorant}(q,y/q)
>\frac{4859}{10000},                                  \tag{6.11}
$$

$$
\Re\mathfrak p_{q,A}(z)
>\frac{7139}{45000},                                   \tag{6.12}
$$

and

$$
q\Re\mathfrak p_{q,A}(z)-\frac7{3q}
>\frac{3q}{20}.                                        \tag{6.13}
$$

The numerical combination is

$$
\frac9{20}\frac{4859}{10000}
-\frac{108019}{1800000}
=\frac{7139}{45000},
$$

and

$$
\frac{7139}{45000}-\frac3{20}
=\frac{389}{45000}.
$$

For \(q\ge1000\),

$$
\frac7{3q}<\frac{389}{45000}q.
$$

At the predecessor, (6.9) supplies the same \(y\) at scale \(10q\), yielding

$$
U^x_{10q,C}(n-1)>\frac{3(10q)}{20}=\frac{3q}{2}.       \tag{6.14}
$$

These free-phase statements are proved here as ordinary mathematical generalizations of the displayed repository estimates. They are **not** claimed to be existing generic Lean declarations. A Lean refactor must parameterize the atom and shells by a free phase and separately package the internal T194 coordinate witnesses.

---

## 7. Correct logical conclusion

Let \(\mathcal P_{\mathrm{core}}(x)\) denote bad approximability, transcendence, the derived exponent-below-\(8\) property, untimed and timed central returns, the corrected predecessor identities, infinite circle omega-limit set, and the ordinary free-phase parent/child estimates.

Then, for every nonempty word \(w\) and every \(w\)-free prefix \(P\),

$$
\dim_H\{x\in C_w\cap[P]:\mathcal P_{\mathrm{core}}(x)\}
=\dim_HC_w.                                            \tag{7.1}
$$

If finitely many additional predicates \(F_1,\ldots ,F_r\) are proved uniformly throughout the cylinder \([P]\), adjoining them changes nothing:

$$
[P]\subseteq\bigcap_iF_i
\quad\Longrightarrow\quad
\dim_H\{x\in C_w\cap[P]:
\mathcal P_{\mathrm{core}}(x)\land\bigwedge_iF_i(x)\}
=\dim_HC_w.                                            \tag{7.2}
$$

This applies to the endpoint-separation or finite signed-root premises only after the required uniform cylinder implication has actually been proved. It is not automatic from strictness alone.

For a fixed long prefix \(\Pi_D\), the statement is conditional on compatibility:

$$
w\text{ occurs in }\Pi_D
\quad\Longrightarrow\quad
C_w\cap[\Pi_D]=\varnothing.
$$

When \(w\) does not occur in \(\Pi_D\), (7.1) applies.

Nothing here proves or disproves decimal disjunctivity of \(\pi\). The result only shows that the generic T191–T194-style package and any finite compatible cylinder-local package do not logically imply disjunctivity.

---

## References

1. J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. **30** (1981), 713–747. Theorem 5.3.

2. D. Kleinbock and B. Weiss, *Badly approximable vectors on fractals*, Israel J. Math. **149** (2005), 137–170. Theorem 1.1 and Corollary 1.2.

3. S. Kristensen, R. Thorn and S. Velani, *Diophantine approximation and badly approximable sets*, Adv. Math. **203** (2006), 132–169. Theorem 9 and Corollary 10.

4. L. Fishman, *Schmidt’s game on fractals*, Israel J. Math. **171** (2009), 77–92. Theorem 3.1 and Corollaries 5.3–5.4.

5. D. Kleinbock, E. Lindenstrauss and B. Weiss, *On fractal measures and Diophantine approximation*, Selecta Math. **10** (2004), 479–523. Theorem 1.1.

6. M. Hochman and P. Shmerkin, *Equidistribution from fractal measures*, Invent. Math. **202** (2015), 427–479. In particular Theorem 1.12.

7. J. Angelevska, A. Käenmäki and S. Troscheit, *Self-conformal sets with positive Hausdorff measure*, Bull. Lond. Math. Soc. **52** (2020), 200–223. Theorem 3.1 and the sub-self-conformal extension in Remark 6.2.
