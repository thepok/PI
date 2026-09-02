Status: `conjecture` (named unresolved propositions of the program), revised to revision 5 on 2026-09-02 after a cross-document consistency audit (frozen ALA definition, notation).
Audit: independently audited three times on 2026-09-02 for well-posedness and correctness of the "known" claims.
Date: 2026-09-02.
Provenance: paper Section 5, produced by ChatGPT Pro runs and revised after adversarial audits, reviewed by Claude.

## 5. Open problems and reopening conditions

Decimal expansions are canonical, i.e. not eventually $9$. Write $\mathbb N_0=\{0,1,\ldots\}$, $\mathbb N_+=\{1,2,\ldots\}$, $\mathcal D_b=\{0,\ldots,b-1\}$, and use the continuous evaluation map
$$
\pi_b((a_j)_{j\ge1})=\sum_{j\ge1}a_jb^{-j}.
$$
For decimal expansions, the paper digits are one-based:
$$
a_j(x)=d^{(10)}_{j-1}(x)\qquad(j\ge1),
$$
and, for $\pi$,
$$
a_j(\pi)=\operatorname{Nat}(\operatorname{piDigit}(j-1)).
$$
The map $\pi_b$ is non-injective only at the countable set of base-$b$ endpoints. For $v=v_1\cdots v_\ell\in\mathcal D_{10}^{\ell}$, set
$$
I(v)=\left[\frac{[v]_{10}}{10^\ell},\frac{[v]_{10}+1}{10^\ell}\right),
\qquad
[v]_{10}=\sum_{i=1}^{\ell}v_i10^{\ell-i}.
$$
For integers $z$ and $M\ge1$, $[z]_M\in\{0,\ldots,M-1\}$ is the least nonnegative residue, and $d_{\mathbb T}(x,y)=\|x-y\|_{\mathbb R/\mathbb Z}$.

For nonempty $w\in\mathcal D_{10}^m$, define
$$
\Sigma_w=\{\mathbf a=(a_j)_{j\ge1}\in\mathcal D_{10}^{\mathbb N_+}:\mathbf a\text{ contains no occurrence of }w\},
\qquad
K_w:=\pi_{10}(\Sigma_w).
$$
Then $\Sigma_w$ and $K_w$ are compact. Let
$$
C_w:=\{x\in[0,1):\text{the canonical decimal expansion of $x$ avoids $w$}\}
$$
and put $d_w=\dim_HC_w$. Since
$$
C_w\mathbin{\triangle}(K_w\cap[0,1))
$$
is countable, $\dim_HK_w=d_w$. If $\rho_w$ is the Perron root of the prefix automaton for avoiding $w$, then
$$
d_w=\frac{\log\rho_w}{\log10};
$$
see [the separator theorem note, §2, equation (2.9)](../results/intermediate/20260902-diophantine-separator-theorems.md).

For a finite word $u$, write
$$
[u]_{\Sigma,r}=\{\mathbf a:a_r\cdots a_{r+|u|-1}=u\},
\qquad
[u]_\Sigma=[u]_{\Sigma,1}.
$$
For nonempty $A\subseteq\mathcal D_{10}$ and $c\in A\cap\{1,\ldots,8\}$, define
$$
\begin{aligned}
\mathbf a\in\mathrm{ALA}^{\Sigma}_{A,c}\Longleftrightarrow{}&
(\exists k_0\in\mathbb N_+)(\forall k\ge k_0)(\forall u\in A^k)(\exists n\in\mathbb N_0)\\[-1mm]
&10^k+1\le n<10^{k+1}
\ \land\
 a_{n+1}\cdots a_{n+k+1}=uc.
\end{aligned}
$$
The real set $\mathrm{ALA}_{A,c}$ uses the canonical expansion. Every sequence in $\mathrm{ALA}^{\Sigma}_{A,c}$ contains $c$ at arbitrarily large positions and is therefore neither eventually $0$ nor eventually $9$. Hence
$$
\pi_{10}(\Sigma_w\cap\mathrm{ALA}^{\Sigma}_{A,c})
=C_w\cap\mathrm{ALA}_{A,c}.
\tag{5.1}
$$
Finally,
$$
\mathrm{BA}(\kappa)=
\left\{x:\left|x-\frac pq\right|\ge\frac{\kappa}{q^2}
\ \forall p\in\mathbb Z,\ q\in\mathbb N_+\right\},
\qquad
\mathrm{BA}=\bigcup_{\kappa>0}\mathrm{BA}(\kappa).
$$

Any unconditional proof or unconditional disproof of a displayed proposition, in the sense of [`TARGET_SPECIFICATION_v1.md`, version 1.0-rc2, §4.1](TARGET_SPECIFICATION_v1.md), counts as a mathematical resolution. The “does not by itself imply” paragraphs identify missing logical implications and do not prohibit proof methods.

### P1. The BA--ALA intersection problems

Put
$$
X(w,A,c)=C_w\cap\mathrm{BA}\cap\mathrm{ALA}_{A,c},
$$
and freeze the common parameter prefix as
$$
\mathfrak P_1:=
\left\{(m,w,A,c):
\begin{array}{l}
m\in\mathbb N_+,\ w\in\mathcal D_{10}^m,\ A\subseteq\mathcal D_{10},\ c\in\mathcal D_{10},\\[-1mm]
|A|=9,\ w\notin A^m,\ c\in A\cap\{1,\ldots,8\}
\end{array}
\right\}.
\tag{5.2}
$$
The three distinct propositions are
$$
\tag{P1-FD}
\forall(m,w,A,c)\in\mathfrak P_1,
\qquad
\dim_HX(w,A,c)=d_w,
$$
$$
\tag{P1-PD}
\forall(m,w,A,c)\in\mathfrak P_1,
\qquad
\dim_HX(w,A,c)>0,
$$
$$
\tag{P1-NE}
\forall(m,w,A,c)\in\mathfrak P_1,
\qquad
X(w,A,c)\ne\varnothing.
$$
Choose a digit $d$ occurring in $w$. Then
$$
(\mathcal D_{10}\setminus\{d\})^{\mathbb N_+}\subseteq\Sigma_w.
$$
Its image in $K_w$ has Hausdorff dimension $\log 9/\log 10$, and the countable endpoint bridge between $K_w\cap[0,1)$ and $C_w$ gives
$$
d_w\ge \frac{\log9}{\log10}>0.
$$
$$
(\mathrm{P1\!\!-FD})
\Longrightarrow
(\mathrm{P1\!\!-PD})
\Longrightarrow
(\mathrm{P1\!\!-NE}).
$$
The localized full-dimension strengthening is
$$
\tag{P1-FD-loc}
\begin{aligned}
&(\forall(m,w,A,c)\in\mathfrak P_1)
(\forall P\in\textstyle\bigcup_{\ell\ge1}\mathcal D_{10}^{\ell})\\[-1mm]
&\qquad C_w\cap I(P)\ne\varnothing
\Longrightarrow
\dim_H\bigl(X(w,A,c)\cap I(P)\bigr)=d_w.
\end{aligned}
$$
The condition is cylinder admissibility, not merely internal avoidance by $P$, since an occurrence of $w$ may cross a boundary.

The all-label packets occupy zero-density digit intervals, which preserves entropy but not a uniform Diophantine constant. The missing step is, for example, either a fixed-Markov-constant extension theorem—given $s<d_w$, choose $\kappa(s)>0$ before branching and retain dimension at least $s$—or a sparse-blackout theorem for Schmidt or potential games. Constants tending to zero along every branch do not establish bad approximability.

The relevant tails are first defined as symbolic coding objects:
$$
\widetilde E_j(w,A,c)
=
\Sigma_w\cap
\bigcap_{k\ge j}\bigcap_{u\in A^k}
\bigcup_{n=10^k+1}^{10^{k+1}-1}[uc]_{\Sigma,n+1},
\qquad
\Sigma_w\cap\mathrm{ALA}^{\Sigma}_{A,c}
=
\bigcup_{j\ge1}\widetilde E_j(w,A,c).
\tag{5.3}
$$
Each $\widetilde E_j$ is closed in the compact SFT $\Sigma_w$. For every admissible symbolic prefix $P$, put
$$
X_P:=\pi_{10}(\Sigma_w\cap[P]_\Sigma),
\qquad
E_{j,P}:=\pi_{10}(\widetilde E_j(w,A,c)\cap[P]_\Sigma),
$$
and
$$
\mathrm{ALA}_P
:=\pi_{10}(\Sigma_w\cap[P]_\Sigma\cap\mathrm{ALA}^{\Sigma}_{A,c})
=X_P\cap\mathrm{ALA}_{A,c}.
$$
The sets $X_P$ and $E_{j,P}$ are compact in the Euclidean metric. The equality defining $\mathrm{ALA}_P$ is exact because the interior marker $c$ excludes both eventually-$0$ and eventually-$9$ codings.

For every admissible cylinder $I(P)$, [Theorems A and B in the separator theorem note](../results/intermediate/20260902-diophantine-separator-theorems.md) give, respectively,
$$
\dim_H\bigl(C_w\cap I(P)\cap\mathrm{BA}\cap\mathrm{Trans}\bigr)=d_w,
$$
and
$$
\dim_H\!\left(
C_w\cap I(P)\cap\mathrm{ALA}_{A,c}\cap\mathrm{Trans}
\cap\{x:\mu(x)=2\}
\right)=d_w.
$$
Define
$$
\dim_{\mathrm{reg}}E
:=
\sup\left\{
\delta>0:
\exists F\subseteq E
\text{ supporting a }\delta\text{-Ahlfors-regular probability measure}
\right\},
$$
with value $0$ if the class is empty. [Theorem C in the separator theorem note](../results/intermediate/20260902-diophantine-separator-theorems.md) gives
$$
\dim_{\mathrm{reg}}\bigl(C_w\cap\mathrm{ALA}_{A,c}\bigr)=0.
$$

[Theorem D, §4.2, in the BA--ALA intersection note](../results/intermediate/20260902-ba-ala-intersection-problem.md) gives, for every admissible $P$ and every $0\le c_{\mathrm{pot}}<d_w$, that neither $\mathrm{ALA}_P$ nor any projected compact tail $E_{j,P}$ is $c_{\mathrm{pot}}$-potential-winning in the compact Euclidean ambient $X_P$. [Corollary 4.1 in the same file](../results/intermediate/20260902-ba-ala-intersection-problem.md) gives the canonical-real-line relative conclusion: interpret a target $E\subset X_P$ as $E\cup(\mathbb R\setminus X_P)$ in the canonical splitting of $\mathbb R$. Then
$$
\tag{5.4}
\begin{aligned}
0\le c_{\mathrm{pot}}<d_w
&\Longrightarrow
\mathrm{ALA}_P\text{ and every }E_{j,P}
\text{ are not }c_{\mathrm{pot}}\text{-potential-winning in }X_P,\\[-1mm]
\varepsilon\in(1-d_w,1]
&\Longrightarrow
\mathrm{ALA}_P\cup(\mathbb R\setminus X_P)
\text{ and every }E_{j,P}\cup(\mathbb R\setminus X_P)\\[-1mm]
&\hspace{29mm}\text{are not }\varepsilon\text{-Cantor-winning in the canonical splitting of }\mathbb R.
\end{aligned}
$$
No BHNS splitting theorem for a “canonical symbolic splitting of $\Sigma_w$” is claimed. In particular, no conclusion for $\varepsilon\le1-d_w$ is obtained from Corollary 4.1. The game comparison is from \cite{BadziahinHarrap2017,BHNS2025}; the all-label obstruction is the file-qualified Theorem D above. The retained construction in [the BA--ALA intersection note, §4.7](../results/intermediate/20260902-ba-ala-intersection-problem.md) also has full-relative-dimension subfamilies with unbounded continued-fraction partial quotients and hence disjoint from $\mathrm{BA}$.

**What does not by itself imply P1-FD, P1-PD, or P1-NE.** Separate largeness theorems, almost-everywhere or residual statements, and conditional results do not by themselves imply a simultaneous intersection; that is the missing step. Constants tending to zero do not by themselves imply membership in $\mathrm{BA}$, although branch-dependent constants can count if the resulting BA union has the required dimension. One admissible counterexample completely disproves the corresponding universal proposition.

### P1$^{\prime}$. Sparse forced blocks in finite-type subshifts

For $b\in\mathbb N$ with $b\ge2$, let $\mathrm{SFT}_b$ be the set of one-sided SFTs in $\mathcal D_b^{\mathbb N_+}$, and define
$$
\mathrm{FBD}(b)
=
\left\{
((N_j,\ell_j,v_j))_{j\ge1}:
\begin{array}{l}
N_j\in\mathbb N_0,\ \ell_j\in\mathbb N_+,\ v_j\in\mathcal D_b^{\ell_j},\\[-1mm]
N_{j+1}\ge N_j+\ell_j\quad(\forall j\ge1)
\end{array}
\right\}.
$$
For $\Sigma\in\mathrm{SFT}_b$ and $\mathscr F\in\mathrm{FBD}(b)$, put
$$
\Sigma_{\mathscr F}
=
\left\{
 x\in\Sigma:
 x_{N_j+1}\cdots x_{N_j+\ell_j}=v_j
\quad\forall j\ge1
\right\},
$$
$$
K_{\Sigma,\mathscr F}=\pi_b(\Sigma_{\mathscr F}),
\qquad
F_{\mathscr F}=\bigcup_j\{N_j+1,\ldots,N_j+\ell_j\}.
$$
Call $\mathscr F$ *sparse and entropy-neutral for* $\Sigma$ if
$$
\Sigma_{\mathscr F}\ne\varnothing,
\qquad
\frac{|F_{\mathscr F}\cap\{1,\ldots,N\}|}{N}\longrightarrow0,
\qquad
\dim_HK_{\Sigma,\mathscr F}=\dim_H\pi_b(\Sigma).
$$
With $d_\Sigma=\dim_H\pi_b(\Sigma)$, the clean proposition is
$$
\tag{P1$'$}
\begin{aligned}
&\forall b\in\mathbb N,\ b\ge2,
\ \forall\Sigma\in\mathrm{SFT}_b
\ \forall\mathscr F\in\mathrm{FBD}(b)
\ \forall s\in\mathbb R,\\[-1mm]
&\bigl(
\Sigma\ne\varnothing
\land
\mathscr F\text{ is sparse and entropy-neutral for }\Sigma
\land
0<s<d_\Sigma
\bigr)\\[-1mm]
&\hspace{25mm}\Longrightarrow
\exists\kappa>0:
\quad
\dim_H\bigl(K_{\Sigma,\mathscr F}\cap\mathrm{BA}(\kappa)\bigr)\ge s.
\end{aligned}
$$
The strict lower bound excludes the vacuous $s=0$ case. Since
$$
\mathrm{BA}=\bigcup_{M\ge1}\mathrm{BA}(1/M),
$$
countable stability gives
$$
\dim_H\bigl(K_{\Sigma,\mathscr F}\cap\mathrm{BA}\bigr)=d_\Sigma
\iff
(\forall s<d_\Sigma)(\exists M\in\mathbb N_+)
\ \dim_H\bigl(K_{\Sigma,\mathscr F}\cap\mathrm{BA}(1/M)\bigr)\ge s.
\tag{5.5}
$$
Thus branch-dependent constants can count if full dimension of the BA union is proved; constants without fixed-level dimension control do not suffice.

The stationary literature covers supports satisfying its stated hypotheses: Federer/decay or friendliness in Kleinbock--Weiss, power-law/regularity assumptions in Kristensen--Thorn--Velani, and suitable fractal supports in Fishman's Schmidt-game framework \cite{KleinbockWeiss2005,KristensenThornVelani2006,Fishman2009}. Self-similar or graph-directed examples require the relevant separation, irreducibility, decay, Federer, or power-law conditions. None of these theorems covers every nonstationary absolute-position forced corridor in P1$^{\prime}$.

**What does not by itself imply P1$^{\prime}$.** One positive example, an Ahlfors-regular subclass theorem, or a random-packet theorem does not by itself imply the universal deterministic proposition; the missing step is the remaining quantifiers. One admissible failing datum is, conversely, a complete disproof.

### P2. The one-sided residue problems

For the Machin route, let
$$
S_N(x)=\sum_{j=0}^{N}\frac{(-1)^jx^{2j+1}}{2j+1},
$$
$$
L_m=8S_{2m+1}(1/3)+4S_{2m+1}(1/7),
\qquad
U_m=8S_{2m}(1/3)+4S_{2m}(1/7),
$$
so $L_m<\pi<U_m$, and define
$$
D_m^{\mathrm M}
=\operatorname{lcm}\bigl(\operatorname{den}L_m,\operatorname{den}U_m\bigr),
$$
$$
R_{m,n}^{\mathrm M}
=[10^nD_m^{\mathrm M}L_m]_{D_m^{\mathrm M}},
\qquad
\Delta_m=D_m^{\mathrm M}(U_m-L_m).
$$
Then
$$
\tag{MC0}
(\forall k\in\mathbb N_+)(\exists m,n\in\mathbb N_0)
\quad
10^kR_{m,n}^{\mathrm M}+10^{n+k}\Delta_m<D_m^{\mathrm M},
$$
and
$$
\tag{SOH$_{3/7}$}
\begin{aligned}
(\forall k,M\in\mathbb N_+)(\exists m,n\in\mathbb N_0)
\quad& m\ge M\\[-1mm]
&{}\land 10^kR_{m,n}^{\mathrm M}+10^{n+k}\Delta_m<D_m^{\mathrm M}.
\end{aligned}
$$
The inequality puts the whole scaled bracket inside $[0,10^{-k})$; conversely, an interior CW0 hit permits arbitrarily accurate brackets. Thus
$$
\boxed{\mathrm{SOH}_{3/7}\iff\mathrm{MC0}\iff\mathrm{CW0}.}
\tag{5.6}
$$

For the BBP route \cite{BBP1997}, set
$$
\mathcal R(j)
=\frac4{8j+1}-\frac2{8j+4}-\frac1{8j+5}-\frac1{8j+6},
$$
$$
B_n=\sum_{j=0}^{n}\frac{\mathcal R(j)}{16^j}
=\frac{P_n}{D_n^{\mathrm B}}
$$
in lowest terms, and for $n\ge2$ define
$$
a=51-16\pi\in(0,1),
\qquad
E_n=(10^n-16)(\pi-B_n),
$$
$$
r_n=[(10^n-16)P_n]_{D_n^{\mathrm B}},
\qquad
q_n=\frac{(10^n-16)P_n-r_n}{D_n^{\mathrm B}}\in\mathbb Z.
$$
Then
$$
10^n\pi
=q_n+51+
\left(\frac{r_n}{D_n^{\mathrm B}}+E_n-a\right),
\tag{5.7}
$$
and the frozen one-sided reopening is
$$
\tag{SOH$_{\mathrm{BBP},10}^{0}$}
\begin{aligned}
(\forall k,N\in\mathbb N_+)(\exists n\in\mathbb N_0)
\quad& n\ge\max\{N,2\},\\[-1mm]
&0<\frac{r_n}{D_n^{\mathrm B}}+E_n-a<10^{-k}.
\end{aligned}
$$
Equivalently,
$$
a-E_n<\frac{r_n}{D_n^{\mathrm B}}<a+10^{-k}-E_n.
$$
Put
$$
t_n=\frac{r_n}{D_n^{\mathrm B}}+E_n-a.
$$
The BBP tail estimate gives, for $n\ge2$,
$$
0<E_n<\eta_n,
\qquad
\eta_n=(5/8)^n,
$$
so $E_n\to0$. Hence, for all sufficiently large $n$, $0<E_n<a$, and therefore $-a<t_n<1$. Given $k,N$, a CW0 hit may be chosen with $n\ge N$ sufficiently large and
$$
0<\{10^n\pi\}<\min\{10^{-k},1-a\}.
$$
The alternative lift $t_n=\{10^n\pi\}-1$ would then give $t_n<-a$, which is impossible; hence $t_n=\{10^n\pi\}$. The reverse implication is immediate from (5.7). Thus
$$
\mathrm{SOH}_{\mathrm{BBP},10}^{0}\iff\mathrm{CW0};
$$
this is an oriented condition, not a symmetric proximity statement.

The stronger all-cylinder condition is separate. With the same $\eta_n$,
$$
d_{\mathbb T}\!\left(
\{(10^n-16)\pi\},
\frac{r_n}{D_n^{\mathrm B}}
\right)<\eta_n,
$$
and, for an oriented arc $J$, define
$$
J^{[-\eta]}
=\{x\in J:d_{\mathbb T}(x,\partial J)>\eta\},
\qquad
J(v)=I(v)-16\pi\pmod1.
$$
The separate problem is
$$
\tag{BBP--V1}
\begin{aligned}
&(\forall\ell\in\mathbb N_+)
(\forall v\in\mathcal D_{10}^{\ell})
(\forall N\in\mathbb N_+)
(\exists n\in\mathbb N_0)\\[-1mm]
&\qquad n\ge\max\{N,2\},
\qquad
2\eta_n<10^{-\ell},
\qquad
\frac{r_n}{D_n^{\mathrm B}}\in J(v)^{[-\eta_n]}.
\end{aligned}
$$
BBP--V1 implies arbitrary decimal-cylinder hitting and hence V1; it is not the frozen P2 slot.

Pigeonhole close pairs yield a small residue of
$$
10^ic(10^{j-i}-1),
$$
not an anchored hit by either orbit point. The route-compatible example with modulus $D=9$ and $c=1$ has $10^tc\equiv1\pmod9$ for all $t$, so differences vanish while a lower endpoint may be missed.

Likewise, use the involution
$$
\iota_D(r)=[-r]_D,
$$
not literal valuation preservation. It satisfies
$$
\gcd(r,D)=\gcd(\iota_D(r),D),
$$
or equivalently, with $\nu_p(0)=+\infty$,
$$
\min\{\nu_p(r),\nu_p(D)\}
=
\min\{\nu_p(\iota_D(r)),\nu_p(D)\}
\qquad(p\mid D).
\tag{5.8}
$$
Negation commutes with multiplication modulo $D$ but reverses the oriented Archimedean inequality.

**What does not by itself imply P2.** Two-sided distances, close pairs, orders, valuations, finite scans, and a result conditional on Hypothesis A do not by themselves imply the displayed oriented universal inequality; the missing steps are orientation, an anchored numerator-sensitive order relation, the full quantifiers, and proof of any hypothesis. Such tools may still be ingredients. Failure at one required outer datum disproves the relevant proposition: a $k$ for MC0; a pair $(k,M)$ for $\mathrm{SOH}_{3/7}$; a pair $(k,N)$ for $\mathrm{SOH}_{\mathrm{BBP},10}^{0}$; or a triple $(\ell,v,N)$ for BBP--V1.

### P3. The carry-certificate reformulation

The proposition is purely mathematical:
$$
\tag{P3}
\boxed{
\begin{aligned}
&\exists q,s,B\in\mathbb N_+
\ \exists Z\in\mathbb Z
\ \exists(a_m)_{m\ge1}\in\mathbb Z^{\mathbb N_+}\\[-1mm]
&\qquad
\exists(n_j,L_j,h_j)_{j\ge1}
\in(\mathbb N_+^3)^{\mathbb N_+}:\\[-1mm]
&\quad B=10^s,
\qquad
\frac\pi q=Z+\sum_{m\ge1}a_mB^{-m},
\qquad
\sum_{m\ge1}|a_m|B^{-m}<\infty,\\[-1mm]
&\quad n_1<n_2<\cdots,
\qquad
h_j\longrightarrow\infty,\\[-1mm]
&\quad(\forall j\in\mathbb N_+)
\qquad
B^{L_j}\mid\sum_{r=1}^{L_j}a_{n_j+r}B^{L_j-r}\\[-1mm]
&\hspace{36mm}{}
\land
0<\sum_{r>L_j}a_{n_j+r}B^{-r}<B^{-h_j}.
\end{aligned}
}
$$
Any unconditional proof or unconditional disproof of this display resolves P3 mathematically under the opening convention.

After multiplication by $B^{n_j}$, the weighted block is integral and
$$
0<\left\{B^{n_j}\frac\pi q\right\}<B^{-h_j}.
$$
For large $j$,
$$
0<\{B^{n_j}\pi\}<qB^{-h_j},
$$
giving at least
$$
h_j-\lceil\log_Bq\rceil
$$
leading base-$B$ zero digits. Since $B=10^s$, P3 implies CW0.

Conversely, assume CW0. Take $q=1$, $s=1$, $B=10$, $Z=3$, and let $a_m\in\{0,\ldots,9\}$ be the canonical decimal digits of $\pi$. Choose increasing positions $n_j$ at which zero runs of lengths $H_j\to\infty$ begin; such positions can be chosen increasing because $\pi$ is not eventually zero. Put $L_j=1$ and $h_j=H_j$. Then
$$
10^{L_j}\mid a_{n_j+1}=0,
$$
and
$$
0<\sum_{r>1}a_{n_j+r}10^{-r}<10^{-H_j}.
$$
Positivity follows because $\pi$ is irrational and hence not terminating. Strictness of the upper bound follows because the canonical expansion is not eventually $9$. Therefore P3 holds, and
$$
\boxed{\mathrm{P3}\iff\mathrm{CW0}.}
$$

**Remark (what would make P3 informative).** The equivalence permits a digit-read certificate and makes P3 a certificate reformulation of CW0. An arithmetically informative proof would instead derive the coefficients and blocks from a frozen arithmetic construction independently of the target decimal-cylinder claim. This is a non-normative methodological desideratum only; it does not restrict proof methods or the mathematical resolution rule.

Erdős's Lambert-series argument supplies this mechanism, not P3 for $\pi$: CRT gives a weighted integral block and positivity controls the tail \cite{Erdos1948}. For Ramanujan's series, let
$$
c_n=(6n+1)\binom{2n}{n}^3,
\qquad
F(z)=\sum_{n\ge0}c_nz^n,
\qquad
F(1/256)=\frac4\pi
$$
\cite{Ramanujan1914}. The formal reciprocal
$$
F(z)^{-1}=\sum_{n\ge0}\rho_nz^n
$$
has integer coefficients determined by
$$
\rho_0=1,
\qquad
\rho_n=-\sum_{k=1}^{n}c_k\rho_{n-k}.
\tag{5.9}
$$
Because
$$
|F(z)-1|\le\frac4\pi-1<1
\qquad(|z|\le1/256),
$$
the reciprocal converges there, and
$$
\frac\pi4
=\sum_{n\ge0}\rho_n256^{-n}
=1+\sum_{n\ge1}(\rho_n5^{8n})(10^8)^{-n}.
\tag{5.10}
$$
**Proposition (Ramanujan reciprocal coefficients), Section 1** *(cross-reference to be resolved at assembly)*—not Ramanujan's identity—gives
$$
\nu_2(\rho_n)=3s_2(n),
\qquad
\nu_{10}(\rho_n5^{8n})=3s_2(n)=O(\log n).
\tag{5.11}
$$
Any quantitative ramp must first establish
$$
|\rho_n|\le C\Lambda^n
\qquad(n\ge0),
\qquad
\Lambda<256.
\tag{5.12}
$$
The asymptotic
$$
c_n\asymp64^n/\sqrt n
$$
does not imply this bound for $\rho_n$. Assume $C>0$, $0<\Lambda<256$, and (5.12). For a tail beginning after coefficient index $N$ and a target bound $(10^8)^{-h}$, the direct absolute estimate requires
$$
L>
\frac{
N\log(5^8\Lambda)+h\log(10^8)+O(1)
}{
\log(256/\Lambda)
}.
\tag{5.13}
$$
For the benchmark $\Lambda=64$, which requires a separate proof, this is
$$
L>12.2877\ldots N+13.2877\ldots h+O(1),
\tag{5.14}
$$
not $3N+O(\log N)$. The signed reciprocal coefficients remove the automatic positive-tail mechanism; they do not prove that selected blocks or cancellations can never meet P3.

**What does not by itself imply P3.** Coefficientwise divisibility does not imply divisibility of the weighted aggregate; a small absolute tail lacks the required sign; bounded $h_j$ cannot yield unbounded runs; and a base-$256$ identity needs a valid power-of-ten transfer. These are gaps in a proposed arithmetic construction, not restrictions on other proofs. A proof of nonexistence disproves P3 and CW0, while any proof of CW0 proves P3. P3 does not yield CW9 without a separately formulated reflected certificate.

### P4. The constant-word problems

Let $a_n^{(10)}(\alpha)$ be the $n$-th digit after the radix point in the canonical decimal expansion. Define
$$
\mathrm{CW}_\delta(\alpha):
\quad
(\forall k\in\mathbb N_+)(\exists n\in\mathbb N_0)(\forall i\in\mathbb N_+)
\bigl(i\le k\Rightarrow a_{n+i}^{(10)}(\alpha)=\delta\bigr).
$$
Then
$$
\tag{P4}
\boxed{
\displaystyle
\bigwedge_{\alpha\in\{\pi,\sqrt2,e,\log 2\}}
\ \bigwedge_{\delta\in\{0,9\}}
\mathrm{CW}_\delta(\alpha).
}
$$
A proof of one component resolves only that component; a disproof of one component disproves P4. For irrational $\alpha$,
$$
\mathrm{CW}_0(\alpha)
\iff
\liminf_n\{10^n\alpha\}=0,
$$
$$
\mathrm{CW}_9(\alpha)
\iff
\limsup_n\{10^n\alpha\}=1.
\tag{5.15}
$$
Write
$$
\mathrm{CW0}=\mathrm{CW}_0(\pi),
\qquad
\mathrm{CW9}=\mathrm{CW}_9(\pi),
\qquad
\mathrm{CW}=\mathrm{CW0}\land\mathrm{CW9}.
$$
For
$$
\mathrm E:
\quad
\liminf_n\|10^n\pi\|_{\mathbb R/\mathbb Z}=0,
$$
the exact relation is
$$
\mathrm E\iff(\mathrm{CW0}\lor\mathrm{CW9}),
$$
not $\mathrm{CW}$.

Lagarias records the analogous binary zero-block problem for $\sqrt2$ as open \cite{Lagarias2001}; that does not certify all eight decimal components. The dated, inspectable search ledger in [`TARGET_SPECIFICATION_v1.md`, version 1.0-rc2, §5.4](TARGET_SPECIFICATION_v1.md) records that, to our knowledge as of 2026-09-02, no proof or disproof of any listed decimal component was found.

Using the conservative certified bound
$$
M_\pi:=7.103205334138,
\qquad
\mu(\pi)\le M_\pi,
$$
if $\ell_\delta^\pi(n)$ is the run length beginning after position $n$, then for every $\varepsilon>0$,
$$
\max\{\ell_0^\pi(n),\ell_9^\pi(n)\}
\le (M_\pi-1+\varepsilon)n
=(6.103205334138+\varepsilon)n
\quad\text{for all sufficiently large }n
\tag{5.16}
$$
\cite{ZeilbergerZudilin2020}. This bounds an existing run; it does not prove one exists. [Theorem A in the separator theorem note](../results/intermediate/20260902-diophantine-separator-theorems.md) gives full relative dimension $d_{0^k}$ in $C_{0^k}$, and $d_{9^k}$ in $C_{9^k}$, for transcendental badly approximable numbers of irrationality exponent $2$; these are not dimension-one claims.

**What does not by itself imply a P4 component.** Proving $\mathrm E$ yields only the disjunction and does not select a direction, whereas disproving $\mathrm E$ resolves both $\pi$ components negatively. A result in a multiplicatively independent base does not by itself settle a decimal component. Bases $10^r$ do transfer: zero digits give decimal zero blocks, the digit $10^r-1$ gives decimal nine blocks, and the converse loses only a bounded alignment offset. Finite records, almost-everywhere results, and conditional theorems still lack the quantified assertion for the named constant unless their hypotheses are proved.

### P5. The base-16 density problem

With $\mathcal R(n)$ as in P2, define
$$
y_0=0,
\qquad
y_{n+1}=\{16y_n+\mathcal R(n)\}
\quad(n\in\mathbb N_0).
\tag{5.17}
$$
The proposition is
$$
\tag{P5}
\boxed{
(\forall N\in\mathbb N_0)
\qquad
\overline{\{y_n:n\ge N\}}=[0,1].
}
$$
Equivalently, for every rational $0\le a<b\le1$ and every $N\in\mathbb N_0$, some $n\ge N$ satisfies $a<y_n<b$.

The represented seed is
$$
\theta=\sum_{n\ge0}\frac{\mathcal R(n)}{16^{n+1}}=\frac\pi{16},
\qquad
\tau_n=\sum_{j\ge0}\frac{\mathcal R(n+j)}{16^{j+1}}.
$$
Then
$$
\mathcal R(n)=16\tau_n-\tau_{n+1},
\qquad
\tau_n\longrightarrow0,
$$
and
$$
\{y_n+\tau_n\}=\{16^n\theta\}
\quad(n\ge0),
\qquad
\{16^n\theta\}=\{16^{n-1}\pi\}
\quad(n\ge1).
\tag{5.18}
$$
This exact vanishing-tail identity gives asymptotic shadowing, not a topological conjugacy. For any sequence $z=(z_n)_{n\ge0}\subset[0,1]$, let
$$
\omega(z)
=
\bigcap_{N\ge0}\overline{\{z_n:n\ge N\}}.
$$
Put $x_n=\{16^n\theta\}$, and let $p:[0,1]\to\mathbb T=\mathbb R/\mathbb Z$ be the quotient map. Lagarias's endpoint-qualified condition gives
$$
p(\omega(y))=p(\omega(x))
$$
\cite{Lagarias2001}. Thus the two tail limit sets agree after identifying $0$ and $1$. This suffices for equivalence of density and for equivalence of finiteness, although the literal Euclidean limit sets may differ at the endpoints. Hence P5 is equivalent to D16.

The equivalence
$$
\mathrm{D16}\Longleftrightarrow\mathrm{D2}
$$
follows from base-power invariance of disjunctivity, not from any generic dense-subsequence claim. A hexadecimal word is four binary digits; conversely, a finite binary superword containing a target encoding at all four offsets modulo four guarantees an aligned hexadecimal occurrence. Since $\pi$ is irrational, its binary and hexadecimal expansions have no terminating dual representation, so no expansion ambiguity enters this regrouping argument.

BBP gives the series \cite{BBP1997}; Bailey--Crandall and Lagarias give the orbit framework, tail identity, and finite/dense discussion \cite{BaileyCrandall2001,Lagarias2001}. Under their BBP-type hypotheses, finiteness of $\omega(y)$ is equivalent to rationality of the represented seed. Here $\theta=\pi/16$ is irrational \cite{Niven1947}, so $\omega(y)$ is infinite, which is weaker than density. Lagarias's Weak Dichotomy would upgrade finite-or-infinite to finite-or-dense, and Bailey--Crandall's Hypothesis A would give equidistribution; neither is proved for this orbit.

**What does not by itself imply P5.** Assuming either conjecture, proving only infinitely many limit points, finite computation, an almost-everywhere initial-condition theorem, or a replacement example does not by itself imply the displayed tail-density proposition; the missing step is the specific unconditional tail quantifier. One open interval missed by one tail is a complete disproof.

### Position in the target DAG

$$
\mathrm{AN}\Rightarrow\mathrm{N10}\Rightarrow\mathrm{V1}\Rightarrow\mathrm{CW},
$$
$$
\mathrm{CW}\Rightarrow\mathrm{CW0},
\qquad
\mathrm{CW}\Rightarrow\mathrm{CW9},
\qquad
\mathrm{CW0}\Rightarrow\mathrm E,
\qquad
\mathrm{CW9}\Rightarrow\mathrm E,
$$
with
$$
\mathrm E\iff(\mathrm{CW0}\lor\mathrm{CW9}),
$$
and
$$
\mathrm{HA}\Rightarrow\mathrm{N16}
\Longleftrightarrow\mathrm{N2}
\Rightarrow\mathrm{D16}
\Longleftrightarrow\mathrm{D2}.
$$
Moreover,
$$
\mathrm{P3}\Longleftrightarrow\mathrm{CW0}.
$$
BBP--V1 enters V1. The frozen P2 conditions enter CW0; P3 is equivalent to CW0 and gives no CW9 entrance without a separate reflected certificate. P4 names the endpoint components, P5 is the hexadecimal/binary density branch, and P1/P1$^{\prime}$ are separator problems rather than additional $\pi$-nodes. No further arrow beyond these placements and the frozen target DAG is asserted.
