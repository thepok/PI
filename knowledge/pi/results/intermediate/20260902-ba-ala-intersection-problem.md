Status: `proof sketch`, independently audited three times at proof level on
2026-09-02 (BHNS Thm 4.1 and 3.4 and Bénard–He–Zhang Thm A′
applications verified), revised to revision 7 on 2026-09-03 after a cross-document consistency audit (frozen ALA definition, notation), geometry re-audit fixes applied 2026-09-03, flow-audit edits 2026-09-03.
Date: 2026-09-02.
Provenance: produced by ChatGPT Pro runs from the repository's separator
theorems, revised after adversarial audits, reviewed by Claude.

# 4. The BA--ALA intersection problem

The problem considered in this section is whether the simultaneous arithmetic and digital constraints
$$
\mathrm{BA}\cap X\cap\mathrm{ALA}\neq\varnothing,
\qquad\text{or even}\qquad
\dim_H(\mathrm{BA}\cap X\cap\mathrm{ALA})=\dim_H X,
\tag{4.1}
$$
hold in general. They remain open, including the non-emptiness assertion. We prove instead a sharp obstruction to the standard potential/Cantor-winning route, construct full-dimensional descriptive subsets of $\mathrm{ALA}$ that avoid $\mathrm{BA}$, identify the exact square-root perturbation scale, prove finite-stage compatibility, and establish a sharp logarithmic law for continued-fraction partial quotients on a full-dimensional subset of $\mathrm{ALA}$.

## 4.1. Standing assumptions

Write $\mathbb N_0=\{0,1,\ldots\}$ and $\mathbb N_+=\{1,2,\ldots\}$. Let $m\in\mathbb N_+$ and let $w=w_1\cdots w_m\in\{0,\ldots,9\}^m$ be fixed. Let
$$
\Sigma_w\subset\{0,\ldots,9\}^{\mathbb N_+}
$$
be the compact subshift of one-sided decimal sequences avoiding $w$, and let
$$
\pi_{10}((a_j)_{j\ge1})=\sum_{j\ge1}a_j10^{-j}.
$$
The paper digits are one-based: for a real number $x$ with canonical decimal expansion,
$$
a_j(x)=d^{(10)}_{j-1}(x)\qquad(j\ge1),
$$
and, for $\pi$,
$$
a_j(\pi)=\operatorname{Nat}(\operatorname{piDigit}(j-1)).
$$
For an admissible symbolic prefix $R$, write $[R]_\Sigma$ for its symbolic cylinder and
$$
X_R:=\pi_{10}(\Sigma_w\cap[R]_\Sigma).
$$
Fix an admissible prefix $P$, and put
$$
K_w:=\pi_{10}(\Sigma_w),
\qquad
C_w:=\{x\in[0,1):\text{the canonical decimal expansion of $x$ avoids $w$}\},
$$
$$
X=X_P=\pi_{10}(\Sigma_w\cap[P]_\Sigma).
$$
The endpoint bridge is
$$
C_w\mathbin{\triangle}(K_w\cap[0,1))\quad\text{countable}.
$$
If $\rho_w$ is the Perron root of the prefix automaton for avoiding $w$, then
$$
d_w:=\dim_HC_w=\frac{\log\rho_w}{\log10},\qquad
\dim_HX=\dim_HK_w=d_w,\qquad s:=d_w.
\tag{4.2}
$$
The set $X$ is compact in the Euclidean metric, hence complete. All game and regularity assertions made relative to $X$ in this section use this compact Euclidean ambient; the canonical-real-line comparison in Corollary 4.1 is explicitly localized to a standard Euclidean splitting ball. Here $X\subset K_w$, while $(X\cap[0,1))\mathbin{\triangle}(X\cap C_w)$ is countable. The equality of dimensions in (4.2) follows because $X\subset K_w$, while appending the reset word introduced below after $P$ embeds an affine copy of $K_w$ into $X$; the equality with $\dim_HC_w$ then follows from the countable endpoint bridge. We write $\mathrm{Trans}$ for the set of transcendental real numbers.

Choose a digit $\beta$ such that
$$
\beta\in\{1,\ldots,8\}\setminus\{w_1,w_m\},
\tag{4.3}
$$
and write $g=\beta^m$. Then $g$ is a safe reset and guard. It contains no copy of $w$; an occurrence of $w$ cannot cross from a legal word into the right guard, because it would end in $\beta$, and cannot cross from the left guard into a legal word, because it would begin in $\beta$. Reading $g$ also returns every state of the prefix automaton to the reset state. Uniqueness for the repeatedly guarded attractors will be verified when $K_{L,P}$ is defined in Theorem D. No corresponding uniqueness assertion is made for full follower cylinders or for the induced countable-IFS attractor used later.

The label alphabet $A\subset\{0,\ldots,9\}$ has cardinality $9$ and omits a digit occurring in $w$. Consequently every word over $A$ avoids $w$. Fix
$$
c\in A\cap\{1,\ldots,8\},
$$
and choose
$$
a\in A\cap\bigl(\{1,\ldots,8\}\setminus\{\beta\}\bigr).
\tag{4.4}
$$
For the run argument only $a\neq\beta$ is needed; the interior-digit restriction removes endpoint distractions.

For $k\ge1$, let
$$
J_k:=\{n\in\mathbb N_0:10^k+1\le n<10^{k+1}\}
$$
be the frozen window of START positions. For a symbolic sequence $\mathbf a=(a_j)_{j\ge1}$, define
$$
\mathbf a\in\mathrm{ALA}^{\Sigma}_{A,c}
\Longleftrightarrow
(\exists k_0\in\mathbb N_+)(\forall k\ge k_0)(\forall u\in A^k)(\exists n\in J_k)
\quad a_{n+1}\cdots a_{n+k+1}=uc.
$$
Let $O_k^\Sigma\subset\Sigma_w\cap[P]_\Sigma$ be the finite-coordinate event
$$
O_k^\Sigma
:=\left\{\mathbf a\in\Sigma_w\cap[P]_\Sigma:
(\forall u\in A^k)(\exists n\in J_k)\quad a_{n+1}\cdots a_{n+k+1}=uc\right\}.
$$
Define
$$
E_j^\Sigma=\bigcap_{k\ge j}O_k^\Sigma,
\qquad
O_k=\pi_{10}(O_k^\Sigma),
\qquad
E_j=\pi_{10}(E_j^\Sigma),
\qquad
\mathrm{ALA}:=X\cap\mathrm{ALA}_{A,c}=\bigcup_{j\ge1}E_j.
\tag{4.5}
$$
Here the real set $\mathrm{ALA}_{A,c}$ is defined by the canonical decimal expansion. Because every sequence in $\mathrm{ALA}^{\Sigma}_{A,c}$ contains the interior digit $c$ at arbitrarily large positions, it is neither eventually $0$ nor eventually $9$. Hence its decimal coding is unique, and the exact projected identity is
$$
\pi_{10}\bigl(\Sigma_w\cap[P]_\Sigma\cap\mathrm{ALA}^{\Sigma}_{A,c}\bigr)
=X\cap\mathrm{ALA}_{A,c}.
$$
Each $O_k^\Sigma$ is clopen, each $E_j^\Sigma$ is compact, and therefore each projected tail $E_j$ is compact and $\mathrm{ALA}\subset X$ is $F_\sigma$. Finally,
$$
\mathrm{BA}(\kappa)
:=\left\{x:\left|x-\frac pq\right|\ge \frac{\kappa}{q^2}
\text{ for all }p\in\mathbb Z,\ q\ge1\right\},
\qquad
\mathrm{BA}=\bigcup_{M\ge1}\mathrm{BA}(1/M),
\quad \kappa>0.
\tag{4.6}
$$

## 4.2. The sharp potential-winning obstruction

Badziahin and Harrap prove in their Section 7.1 that $\mathrm{BA}\subset\mathbb R$ is $1$-Cantor-winning for the canonical splitting structure of $\mathbb R$; their Theorems 8 and 9 give, respectively, the full-dimension and countable-intersection properties of Cantor-winning sets \cite[Section 7.1 and Theorems 8--9]{BadziahinHarrap2017}. The missing premise in the naive intersection argument is that $\mathrm{ALA}$ is winning in a compatible structure. In fact it fails every potential-winning parameter below the ambient dimension.

**Theorem D (sharp potential-winning obstruction).** \label{thm:D} Under the standing assumptions of §4.1, let $X=X_P\ne\varnothing$, put $s=d_w$, and let $a$ be chosen as in (4.4). Then, for every $0\le c_0<s$, neither $\mathrm{ALA}$ nor any compact tail $E_j\subset X$ is $c_0$-potential-winning in $X$. More precisely, for every $c_0<s$ there exists a closed $d$-Ahlfors-regular set
$$
K\subset X\setminus\mathrm{ALA},
\qquad d>c_0.
\tag{4.7}
$$
The same $K$ is disjoint from every $E_j$.

*Proof.* Let $N_w(L)$ be the number of length-$L$ decimal words avoiding $w$. For every such word $u$, form
$$
B_u=gug=\beta^m u\beta^m.
\tag{4.8}
$$
Writing $T_R(t)=([R]_{10}+t)/10^{|R|}$, let $K_L$ be the attractor of the similarities
$$
t\longmapsto \frac{[B_u]_{10}+t}{10^{L+2m}}
\qquad (|u|=L,\ u\text{ avoids }w),
$$
and set $K_{L,P}=T_{Pg}(K_L)$. Thus every point of $K_{L,P}$ is represented by a sequence beginning with $Pg$ and followed by an arbitrary concatenation of the blocks $B_u$. These sequences remain $w$-free, so $K_{L,P}\subset X$. The maps have common ratio $10^{-(L+2m)}$, distinct decimal words give distinct similarities, and the open set condition holds. The interior guard occurs infinitely often, so all points have unique decimal expansions. Standard finite self-similar-set theory therefore gives that $K_{L,P}$ is compact and Ahlfors regular of dimension
$$
s_L=\frac{\log N_w(L)}{(L+2m)\log 10}.
\tag{4.9}
$$
If $h_w=\lim_{L\to\infty}L^{-1}\log N_w(L)$ is the entropy of the word-avoidance shift, then $s=h_w/\log 10$, and hence
$$
s_L\longrightarrow s.
\tag{4.10}
$$
No monotonicity in $L$ is asserted or needed.

Because $a\neq\beta$, every run of $a$'s in a point of $K_{L,P}$ is contained in one middle word $u$, apart from the fixed finite prefix. Thus there is a uniform finite bound $R_L$ on all $a$-run lengths in $K_{L,P}$. For every $k>R_L$, the level-$k$ obligation corresponding to the label $u=a^k$ fails, independently of the permitted start set $J_k$. Unique decimal coding then gives
$$
K_{L,P}\cap\mathrm{ALA}=\varnothing,
\qquad
K_{L,P}\cap E_j=\varnothing\quad(j\ge1).
\tag{4.11}
$$

We use the BHNS notation
$$
\dim_R E
:=\sup\left\{\delta>0:
\begin{array}{l}
\text{there exists a $\delta$-Ahlfors-regular probability measure $\mu$}\\[-1mm]
\text{with $\operatorname{supp}\mu\subset E$}
\end{array}\right\},
\qquad \sup\varnothing:=0.
$$
Their Theorem 4.1 states, in the direction used here, that every $c_0$-potential-winning set meets every closed set $K$ with $\dim_RK>c_0$; the Borel assumption is required only for the converse \cite[Theorem 4.1]{BHNS2025}. This forward implication uses the complete ambient required by the standing setup of their games and requires neither doubling nor Ahlfors regularity of that ambient. Here $X$ is compact and hence complete. Given $c_0<s$, choose $L$ with $s_L>c_0$. Since $K_{L,P}$ is $s_L$-Ahlfors regular, $\dim_RK_{L,P}=s_L$, and (4.11) gives disjointness. Therefore neither $\mathrm{ALA}$ nor any $E_j$ can be $c_0$-potential-winning. Taking $K=K_{L,P}$ proves the strengthened assertion. $\square$

**Corollary 4.1 (the proved Cantor-winning consequence).** \label{cor:canonical-cantor} Interpret winning relative to $X$ in the canonical splitting of $\mathbb R$ by replacing a target $E\subset X$ with $E\cup(\mathbb R\setminus X)$. Then $\mathrm{ALA}$ and every $E_j$ fail to be $\varepsilon$-Cantor-winning for every
$$
\varepsilon\in(1-s,1].
\tag{4.12}
$$

*Proof.* Fix such an $\varepsilon$ and let $K=K_{L,P}$ be the witness from Theorem D with $s_L>1-\varepsilon$. Choose a closed ball $B_0\subset\mathbb R$ in the standard real-line splitting structure that contains $K$, and put
$$
\widetilde E=(E\cup(\mathbb R\setminus X))\cap B_0,
$$
where $E$ is either $\mathrm{ALA}$ or $E_j$. If the ambient-relative target were $\varepsilon$-Cantor-winning, then it would be $\varepsilon$-Cantor-winning on $B_0$. BHNS Theorem 3.4, which is formulated for a splitting structure on a doubling metric space and a fixed splitting ball, applies here with $A_\infty(B_0)=B_0$ and splitting dimension $\delta=1$; it would make $\widetilde E$ $(1-\varepsilon)$-potential-winning on $B_0$ \cite[Theorem 3.4]{BHNS2025}. The ball $B_0$ is complete, and BHNS Theorem 4.1 would then force $\widetilde E$ to meet the closed set $K$, since $\dim_RK=s_L>1-\varepsilon$ \cite[Theorem 4.1]{BHNS2025}. But $K\subset X$ and $K\cap E=\varnothing$, a contradiction. $\square$

The unrestricted relative assertion is **not proved**. To rule out every $\varepsilon>0$ by BHNS Theorem 3.4 one would first have to construct a BHNS splitting structure whose limit set is exactly $X$ and whose splitting dimension is $s$. The state-dependent branching of the graph-directed coding does not by itself provide the required splitting axioms. BHNS Remark 4.8 warns more generally that even a complete doubling metric space need not admit a splitting structure with $A_\infty(B)=B$ for every ball; it does not itself analyse this decimal graph-directed system \cite[Remark 4.8]{BHNS2025}. Accordingly, no claim is made here for $0<\varepsilon\le1-s$, nor for every positive parameter in an unspecified ``natural'' splitting of $X$.

Theorem D is logically distinct from Theorem C. Theorem C is target-side: it gives $\dim_RY=0$ for every $Y\subset\mathrm{ALA}$, with the decisive requirement $\operatorname{supp}\mu\subset Y$. Proposition 4.2 asserts only $\nu(\mathrm{ALA})=1$, not $\operatorname{supp}\nu\subset\mathrm{ALA}$, so there is no conflict. BHNS Theorem 4.1 is instead complement-facing: the witnesses used in Theorem D are closed regular sets in $X\setminus\mathrm{ALA}$. Theorem C and BHNS Proposition 2.18, together with the ensuing identification of point-diffuseness and uniform perfectness, imply that $\mathrm{ALA}$ contains no nonempty compact diffuse or uniformly perfect subset \cite[Proposition 2.18]{BHNS2025}. This blocks the usual strategy of extracting a friendly, Ahlfors-regular, or diffuse support inside $\mathrm{ALA}$; it does not rule out a different arithmetic construction or a new game adapted to sparse unbounded symbolic blackouts.

## 4.3. The edge-Parry measure and the induced countable IFS

The next proposition supplies the measure input needed both for Theorem E and for Theorem B'. We use Bénard--He--Zhang, *Khintchine dichotomy for self-similar measures*, **J. Amer. Math. Soc.** 39 (2026), 587--623, Theorem A' (doi:10.1090/jams/1070) \cite[Theorem A']{BenardHeZhang2026}. The corresponding preprint is arXiv:2409.08061v4. The later multidimensional preprint arXiv:2508.09076v2 is not needed here. Theorem A' requires precisely a stationary probability measure for a law on $\operatorname{Aff}(\mathbb R)$ with finite exponential moment and no global fixed point; it imposes no additional separation, finite-support, symbolic-stationarity, or dimension hypothesis.

**Proposition 4.2 (Parry--Khintchine package).** \label{prop:parry-package} There are a subcylinder $Y\subset X$ with $\dim_HY=s$ and an $s$-Ahlfors-regular probability measure $\nu$ on $Y$ such that
$$
\nu(\mathrm{ALA})=1,
\qquad
\nu(\mathrm{BA})=0.
\tag{4.13}
$$
Moreover, $\nu$ is stationary for a countably supported probability law on $\operatorname{Aff}(\mathbb R)$ having finite exponential moment and no global fixed point, so it satisfies the full Khintchine dichotomy of Bénard--He--Zhang.

*Proof.* Use the deterministic prefix automaton for avoiding $w$, with states $0,\ldots,m-1$. State $j$ records that the longest suffix equal to a prefix of $w$ has length $j$. Let $M=(M_{ij})$, where $M_{ij}$ counts digit-labelled edges from $i$ to $j$. The graph is primitive: state $0$ reaches state $j<m$ by reading $w_1\cdots w_j$, the guard $g$ returns every state to $0$, and any digit different from $w_1$ gives a one-step loop at $0$. Let $\rho_w$ be the Perron root and let $r=(r_i)$ be a positive right Perron vector. Then
$$
s=\frac{\log\rho_w}{\log10}.
\tag{4.14}
$$

Define the Parry transition kernel on labelled edges, initialized at state $0$. For a digit edge $e:i\to j$, set
$$
\mathbb P(e\mid i)=\frac{r_j}{\rho_w r_i}.
\tag{4.15}
$$
Parallel digit edges are each assigned this probability, and normalization follows from $Mr=\rho_wr$. Let $\mu_0$ be the resulting one-sided symbolic path law started at state $0$, and denote its decimal pushforward by $\nu_0=(\pi_{10})_*\mu_0$. If a legal word $u$ of length $n$ ends at state $j$, telescoping gives
$$
\mu_0([u]_\Sigma)=\frac{r_j}{\rho_w^n r_0}\asymp\rho_w^{-n}=10^{-ns}.
\tag{4.16}
$$

Let $\mathcal R$ be the set of first-return words from state $0$ to state $0$, with no intermediate return. For $v\in\mathcal R$, its excursion probability is
$$
p_v=\prod_{e\text{ in }v}\frac{r_{t(e)}}{\rho_w r_{s(e)}}=\rho_w^{-|v|}.
\tag{4.17}
$$
The finite irreducible chain returns to $0$ almost surely, hence $\sum_{v\in\mathcal R}p_v=1$; by the strong Markov property successive excursions are i.i.d. with this law. Define
$$
\phi_v(t)=\frac{[v]_{10}+t}{10^{|v|}}.
\tag{4.18}
$$
Decomposition at the first return gives the exact stationarity identity
$$
\nu_0=\sum_{v\in\mathcal R}p_v(\phi_v)_*\nu_0.
\tag{4.19}
$$
Thus $\nu_0$ is stationary for $\lambda=\sum_vp_v\delta_{\phi_v}$.

Let $\tau$ be the first-return time. From every state, reading the fixed word $g$ reaches $0$ with probability bounded below uniformly over the finite state set. Applying this in successive blocks gives $\mathbb P(\tau>n)\le C\theta^n$ for some $\theta<1$, and therefore
$$
\sum_{v\in\mathcal R}p_v10^{\eta|v|}<\infty
\tag{4.20}
$$
for some $\eta>0$. Every $\phi_v(t)=r_vt+b_v$ has $r_v=10^{-|v|}\neq0$ and $0\le b_v\le1$. There is no global fixed point: every digit $d\neq w_1$ is a one-letter first return, and the maps $t\mapsto(d+t)/10$ have distinct fixed points $d/9$.

Append $g$ after $P$, write the resulting prefix as $Q$, and let
$$
T_Q(t)=\frac{[Q]_{10}+t}{10^{|Q|}}=\alpha_Qt+\beta_Q.
\tag{4.21}
$$
Then $Y=T_Q(\operatorname{supp}\nu_0)\subset X$ and $\nu=(T_Q)_*\nu_0$. The conjugated maps satisfy
$$
\widetilde\phi_v=T_Q\phi_vT_Q^{-1},
\qquad
\widetilde\phi_v(t)=r_vt+\widetilde b_v,
\qquad
\widetilde b_v=\alpha_Qb_v+(1-r_v)\beta_Q.
$$
Their translations are uniformly bounded, say $|\widetilde b_v|\le B_Q$. Hence the full three-term exponential moment after conjugation is
$$
\begin{aligned}
\int\bigl(|r_\phi|^\eta+|r_\phi|^{-\eta}+|b_\phi|^\eta\bigr)\,d\widetilde\lambda(\phi)
&=\sum_{v\in\mathcal R}p_v\bigl(10^{-\eta|v|}+10^{\eta|v|}+|\widetilde b_v|^\eta\bigr)\\
&\le 1+\sum_{v\in\mathcal R}p_v10^{\eta|v|}+B_Q^\eta<\infty,
\end{aligned}
$$
where $\widetilde\lambda=\sum_vp_v\delta_{\widetilde\phi_v}$. Conjugating (4.19) gives $\widetilde\lambda*\nu=\nu$, and affine conjugation preserves the absence of a global fixed point. Thus stationarity, finite exponential moment, and no global fixed point—the complete hypothesis list of Bénard--He--Zhang Theorem A'—hold for $\nu$.

We next record the Ahlfors estimates. Let $x\in\operatorname{supp}\nu_0$ and choose $n$ so that $10^{-(n+1)}<r\le10^{-n}$. A ball $B(x,r)$ meets only a uniformly bounded number of level-$n$ decimal cylinders. By (4.16), bounded endpoint overlap, and the fact that cylinder masses tend to zero, each has $\nu_0$-mass $\asymp\rho_w^{-n}$. Hence
$$
\nu_0(B(x,r))\le C_1\rho_w^{-n}=C_1 10^{-ns}\le C_2r^s.
$$
Conversely, for a fixed sufficiently large integer $C$, a level-$(n+C)$ cylinder along a coding of $x$ has diameter at most $10^{-(n+C)}<r$, lies inside $B(x,r)$, and has mass comparable with $\rho_w^{-(n+C)}$. Therefore
$$
\nu_0(B(x,r))\ge c_1\rho_w^{-(n+C)}\ge c_2r^s.
$$
After adjusting constants for large radii, $\nu_0$ is $s$-Ahlfors regular, and so is its affine image $\nu$. In particular, $\dim_HY=s$, $\nu$ is exact-dimensional, and every full-$\nu$-measure subset of $Y$ has Hausdorff dimension $s$.

It remains to verify abundance for this same measure. Let $\mu$ be the symbolic path law obtained by prefixing $Q$ to a $\mu_0$-distributed tail, so that $(\pi_{10})_*\mu=\nu$. For all sufficiently large $k$, the guarded trials chosen below lie beyond $Q$. Fix such a $k$ and $u\in A^k$, and define the interior start set
$$
J_k^\circ
:=\left\{n\in J_k:10^k+m+1\le n\le10^{k+1}-k-m-2\right\}.
$$
At a designated start $n\in J_k^\circ$, require the block
$$
gucg,
\tag{4.22}
$$
with $uc$ occupying the paper-digit positions $n+1,\ldots,n+k+1$, the left guard occupying $n-m+1,\ldots,n$, and the right guard occupying $n+k+2,\ldots,n+k+m+1$. Thus the designated start index is in $J_k$, while both guards are kept away from the two ends. The block is legal from every current state and returns to state $0$. By (4.15), its conditional probability, uniformly in the past and in $u$, is at least $C_0\rho_w^{-k}$.

One can choose $T_k\asymp10^k/k$ starts in $J_k^\circ$, separated by at least $k+2m+1$, so that the guarded trial packets are disjoint. Iterated conditioning, without any independence assumption, gives
$$
\begin{aligned}
&\mu\bigl(\text{there is no }n\in J_k\text{ with }a_{n+1}\cdots a_{n+k+1}=uc\bigr)\\
&\hspace{34mm}\le (1-C_0\rho_w^{-k})^{T_k}
\le \exp\!\left(-C_1\frac{10^k}{k\rho_w^k}\right).
\end{aligned}
\tag{4.23}
$$
The endpoint margins affect only the implicit constant in $T_k\asymp10^k/k$. Hence, after choosing $C_1>0$ sufficiently small, (4.23) holds uniformly in $u$ for all sufficiently large $k$.

Taking a union over the $9^k$ labels yields, for all sufficiently large $k$,
$$
\mu((O_k^\Sigma)^c)
\le 9^k\exp\!\left(-C_1\frac{(10/\rho_w)^k}{k}\right).
\tag{4.24}
$$
Indeed, $N_w(nm)\le(10^m-1)^n$, so $\rho_w\le(10^m-1)^{1/m}<10$; hence the right-hand side is summable. Borel--Cantelli on the symbolic path space gives $\mu(\bigcup_jE_j^\Sigma)=1$, and therefore $\nu(\mathrm{ALA})=1$. Also $\nu(O_k^c)\le\mu((O_k^\Sigma)^c)$, a fact used below.

Finally, Bénard--He--Zhang Theorem A' applies to $\nu$. Taking, after an irrelevant finite modification, $\psi(q)=1/(q\log q)$, the series $\sum_q\psi(q)$ diverges; hence for $\nu$-almost every $x$ there are infinitely many $(p,q)$ with
$$
|qx-p|<\frac1{q\log q},
\qquad\text{so}\qquad
q\lVert qx\rVert<\frac1{\log q}.
\tag{4.25}
$$
Thus $\inf_q q\lVert qx\rVert=0$ almost surely and $\nu(\mathrm{BA})=0$. $\square$

## 4.4. Descriptive counterexamples

The following sets are existential, not explicit: compact inner approximation and the denominator cutoffs used in the proof are non-effective choices.

**Theorem E (full-dimensional subsets of $\mathrm{ALA}$ avoiding $\mathrm{BA}$).** \label{thm:E} There exist sets $F,L\subset X\cap\mathrm{ALA}$ such that
$$
F\text{ is }F_\sigma,
\qquad
L=\liminf_{k\to\infty}U_k
\text{ for relatively open finite-coordinate/Diophantine events }U_k\subset X,
\tag{4.26}
$$
and
$$
F\cap\mathrm{BA}=L\cap\mathrm{BA}=\varnothing,
\qquad
\dim_HF=\dim_HL=s.
\tag{4.27}
$$
By Theorem C, both also have Ahlfors-regularity dimension zero.

*Proof.* Let $\nu$ be the measure from Proposition 4.2 and put $G=\mathrm{ALA}\setminus\mathrm{BA}$. Then $G$ is Borel and $\nu(G)=1$. Inner regularity gives compact sets $F_n\subset G$ with $\nu(F_n)>1-2^{-n}$. The union
$$
F=\bigcup_{n\ge1}F_n
\tag{4.28}
$$
is $F_\sigma$, has full $\nu$-measure, lies in $\mathrm{ALA}$, and is disjoint from $\mathrm{BA}$. Since $\nu$ is $s$-Ahlfors regular, $\dim_HF=s$.

For the liminf construction, retain the projected level events $O_k=\pi_{10}(O_k^\Sigma)$. Proposition 4.2 gives $\sum_k\nu(O_k^c)<\infty$. Since $\nu(\mathrm{BA})=0$, for every $k$ and every $Q$, almost every $x$ has some $q\ge Q$ with $q\lVert qx\rVert<1/k$. Choose recursively
$$
1\le Q_1<Q_2<\cdots
\tag{4.29}
$$
so that the open set
$$
V_k=\bigcup_{Q_k\le q<Q_{k+1}}
\{x:q\lVert qx\rVert<1/k\}
\tag{4.30}
$$
satisfies $\nu(V_k)>1-2^{-k}$.

Let
$$
N_k=10^{k+1}+k,
$$
the last paper-digit coordinate on which the frozen start-index event $O_k^\Sigma$ depends, and let
$$
D_k=X\cap\{j10^{-N_k}:0\le j\le10^{N_k}\}
$$
be the finite set of level-$N_k$ decimal boundaries in $X$. The change from $10^{k+1}-1$ to $10^{k+1}+k$ is the coordinate-cutoff change forced by allowing the largest start $n=10^{k+1}-1$, whose required block ends at coordinate $n+k+1$. Since $O_k^\Sigma$ is a union of level-$N_k$ symbolic cylinders, the relative boundary in $X$ of its projection $O_k$ is contained in $D_k$. Define
$$
\widehat O_k=\operatorname{int}_X(O_k)\setminus D_k,
\qquad
U_k=\widehat O_k\cap V_k,
\qquad
L=\liminf_{k\to\infty}U_k.
\tag{4.31}
$$
The set $\widehat O_k$ is relatively open, $\widehat O_k\subset O_k$, and $O_k\setminus\widehat O_k\subset D_k$. Since $\nu$ is non-atomic, $\nu(D_k)=0$, so all estimates for $O_k$ survive unchanged after replacement by $\widehat O_k$. Thus the complements in (4.31) have summable measures, and Borel--Cantelli gives $\nu(L)=1$.

If $x$ belongs to $\widehat O_k$ for all sufficiently large $k$, then it avoids $D_k$ for all sufficiently large $k$. Every double-coded decimal endpoint belongs to all $D_k$ once $N_k$ exceeds its terminating level, so such an $x$ has a unique decimal expansion. Membership in $O_k=\pi_{10}(O_k^\Sigma)$ then forces that unique expansion to lie in $O_k^\Sigma$. Hence eventual membership in $\widehat O_k$ puts $L$ in $\mathrm{ALA}$. Eventual membership in $V_k$ supplies $q_k\to\infty$ with $q_k\lVert q_kx\rVert<1/k$; hence $L\cap\mathrm{BA}=\varnothing$. Again $\dim_HL=s$. The regularity-dimension conclusion follows from Theorem C because $F,L\subset\mathrm{ALA}$. $\square$

Thus no theorem depending only on full Hausdorff dimension, $F_\sigma$ or liminf form, and regularity dimension zero can force intersection with $\mathrm{BA}$. Any positive result must use more of the specific combinatorics of $\mathrm{ALA}$.

## 4.5. Perturbation stability and the square-root scale

**Proposition 4.3 (two perturbation guarantees).** \label{prop:perturbation} Let $x\in\mathrm{BA}(\kappa)$, let $\delta>0$, and suppose that $|x-y|\le\delta$. The case $\delta=0$ is immediate.

1. For every rational $p/q$ with
   $$
   q\le\sqrt{\frac{\kappa}{2\delta}},
   \tag{4.32}
   $$
   one has
   $$
   \left|y-\frac pq\right|\ge\frac{\kappa}{2q^2}.
   \tag{4.33}
   $$
2. Let $I_n(x)$ be the continued-fraction cylinder determined by the first $n$ partial quotients of $x$, and let $q_n$ be the denominator of its $n$-th convergent. If
   $$
   \delta<\frac{\kappa}{4q_n^2},
   \tag{4.34}
   $$
   then $x$ and $y$ have the same first $n$ continued-fraction digits.

Consequently, if the first $N$ decimal digits are fixed, so that $\delta\le10^{-N}$, a bare closeness estimate uniformly guarantees either form of protection only up to denominator scale $O(10^{N/2})$.

*Proof.* The first statement is the triangle inequality:
$$
\left|y-\frac pq\right|
\ge \left|x-\frac pq\right|-|x-y|
\ge \frac{\kappa}{q^2}-\delta,
\tag{4.35}
$$
which is at least $\kappa/(2q^2)$ under (4.32).

The two endpoints of $I_n(x)$ are
$$
\frac{p_n}{q_n}
\quad\text{and}\quad
\frac{p_n+p_{n-1}}{q_n+q_{n-1}},
\tag{4.36}
$$
up to parity. Their denominators are at most $2q_n$. Since $x\in\mathrm{BA}(\kappa)$,
$$
\operatorname{dist}(x,\partial I_n(x))
\ge \frac{\kappa}{(q_n+q_{n-1})^2}
\ge \frac{\kappa}{4q_n^2}.
\tag{4.37}
$$
Condition (4.34) therefore keeps $y$ in the same cylinder, which is exactly preservation of the continued-fraction prefix. $\square$

The word *guarantees* is essential. A specially selected perturbation may remain badly approximable at every denominator. The order $\delta^{-1/2}$ is nevertheless sharp for a conclusion based only on closeness: a badly approximable $x$ has bounded partial quotients, hence bounded ratios $q_{n+1}/q_n$; choosing the first $q_n\ge\delta^{-1/2}$ gives $q_n\ll_x\delta^{-1/2}$ and $|x-p_n/q_n|<q_n^{-2}\le\delta$. Taking $y=p_n/q_n$ destroys the Diophantine lower bound at denominator $q_n$ and places $y$ on the boundary of the corresponding continued-fraction cylinder. Legendre's theorem gives a different, weaker test for one convergent: if
$$
\left|x-\frac{p_n}{q_n}\right|+\delta<\frac1{2q_n^2},
\tag{4.38}
$$
then $p_n/q_n$ is a convergent of $y$ \cite[Theorem 1.1]{HanclNguyen2024}. It neither preserves every convergent automatically nor proves equality of the whole prefix; (4.37), not cylinder length alone, is the relevant prefix argument.

## 4.6. Finite feasible stages and the failed diagonal

Call a finite family of finite-coordinate obligations supported after $|P|$ **feasible relative to $P$** if there exists one finite legal extension $R$ of $P$ satisfying all of those coordinate requirements. Appending the reset guard after the last constrained coordinate gives the legal reset extension $Rg$ and restores the full follower language.

**Theorem 4.4 (finite-stage compatibility).** \label{thm:finite-stage} There is $k_0=k_0(w,P)$ such that, for every finite set $S\subset\{k\ge k_0\}$, one can find an admissible finite prefix $Q$ extending $P$ and ending in a reset guard with the following properties:

1. every $x\in X_Q$ satisfies all abundance obligations at the levels $k\in S$; and
2. 
   $$
   \dim_H\bigl(X_Q\cap\mathrm{BA}\cap\mathrm{Trans}\bigr)=s.
   \tag{4.39}
   $$

More generally, the same conclusion holds for every finite family of future finite-coordinate obligations feasible relative to $P$. No assertion is made for a start-index window already fixed by $P$ in a way that violates its obligation.

*Proof.* For each $k$, linearize a de Bruijn cycle of order $k+1$ over $A$. The resulting word $D_k$ has length
$$
|D_k|=9^{k+1}+k
\tag{4.40}
$$
and contains every word of $A^{k+1}$, hence every $uc$ with $u\in A^k$. The guarded packet $gD_kg$ is $w$-free and is compatible with arbitrary legal surroundings. Since
$$
\frac{|gD_kg|}{|J_k|}
=\frac{9^{k+1}+k+2m}{9\cdot10^k-1}
=\left(\frac9{10}\right)^k+o(1),
\tag{4.41}
$$
the packet can be placed with all designated occurrence starts in $J_k$ for all sufficiently large $k$.

For an explicit interior placement, put the first digit of the left guard at paper position $10^k+2$. Then $D_k$ begins at position $10^k+m+2$. The de Bruijn occurrences start at paper positions
$$
10^k+m+2,\ldots,10^k+m+1+9^{k+1},
$$
so their associated frozen start indices are
$$
10^k+m+1,\ldots,10^k+m+9^{k+1}.
$$
For all sufficiently large $k$, every one of these indices lies in $J_k$, and the right guard ends before paper position $10^{k+1}$. Thus both guards fit away from the two ends, not merely the target words. The exact denominator in (4.41) changes from the old occupied-position length $9\cdot10^k$ to the start-set cardinality $|J_k|=9\cdot10^k-1$; the asymptotic ratio and every entropy or dimension estimate are unchanged.

Increase $k_0$ so that these packet intervals also lie beyond $P$. The chosen coordinate intervals are pairwise disjoint. For finite $S$ we append a reset, fill unused positions with $\beta$'s, place one guarded packet at the stated interior location for each required level, and finish with another reset. This produces $Q$, and every continuation satisfies the chosen finite obligations.

After the final reset, $Q$ is an admissible decimal prefix. Theorem A, applied to the real decimal cylinder $[Q]$ of Section 3, gives
$$
\dim_H\bigl(C_w\cap[Q]\cap\mathrm{BA}\cap\mathrm{Trans}\bigr)=s.
$$
This set is contained in $X_Q\cap\mathrm{BA}\cap\mathrm{Trans}$, while $\dim_HX_Q=s$; hence (4.39).

For a general feasible family, take a witnessing legal extension $R$ of $P$ satisfying all of its finite-coordinate requirements and append $g$ after the last constrained coordinate. Every continuation in $X_{Rg}$ still satisfies those requirements, while the reset restores the full follower language. The preceding dimension argument applies with $Q=Rg$. $\square$

The theorem has no infinite-stage diagonal consequence. To avoid confusion with the decimal digits $a_j$, write $\alpha_n(x)$ for the continued-fraction partial quotients of an irrational $x\in[0,1]$. Then
$$
\mathrm{BA}^{\mathrm{cf}}_M=\{x:\alpha_n(x)\le M\text{ for all }n\},
\qquad
\mathrm{BA}=\bigcup_{M\ge1}\mathrm{BA}^{\mathrm{cf}}_M.
\tag{4.42}
$$
Each $\mathrm{BA}^{\mathrm{cf}}_M$ is compact, and fixing $M$ is quantitatively equivalent to fixing a positive lower bound for $\inf_q q\lVert qx\rVert$. If nested projected decimal cylinders $X_{Q_r}$ force the first $r$ abundance stages, Theorem 4.4 gives $X_{Q_r}\cap\mathrm{BA}\neq\varnothing$ at every $r$, but it gives no single $M$ for which
$$
X_{Q_r}\cap\mathrm{BA}^{\mathrm{cf}}_M\neq\varnothing
\quad\text{for every }r.
\tag{4.43}
$$
The required bounds $M_r$ may tend to infinity, equivalently the available Markov constants may tend to zero. Compactness would apply to the nested compact sets $X_{Q_r}\cap\mathrm{BA}^{\mathrm{cf}}_M$ only after one $M$ had been fixed; it does not apply to $X_{Q_r}\cap\mathrm{BA}$, because $\mathrm{BA}$ is not closed. Indeed, if $x$ has unbounded partial quotients and $x_r$ agrees with $x$ through its first $r$ partial quotients and then has only $1$'s, then $x_r\in\mathrm{BA}$ while $x_r\to x\notin\mathrm{BA}$.

There is also no hidden fixed-$M$ dimension conclusion: from (4.39) and (4.42) one gets only
$$
\sup_M\dim_H(X_Q\cap\mathrm{BA}^{\mathrm{cf}}_M)=s.
\tag{4.44}
$$
Thus for every $\eta>0$ some $M$ gives dimension greater than $s-\eta$, but a single $M$ need not attain dimension exactly $s$, still less work uniformly through all packet stages.

## 4.7. The logarithmic partial-quotient law

Let $p_n(x)/q_n(x)$ be the convergents and $\alpha_{n+1}(x)$ the next continued-fraction partial quotient. Recall
$$
\frac1{(\alpha_{n+1}+2)q_n^2}
<\left|x-\frac{p_n}{q_n}\right|
<\frac1{\alpha_{n+1}q_n^2}.
\tag{4.45}
$$

**Theorem B' (sharp logarithmic law on a full-dimensional ALA set).** \label{thm:Bprime} Under the standing assumptions,
$$
\dim_H\left\{
 x\in X\cap\mathrm{ALA}\cap\mathrm{Trans}:
 \limsup_{n\to\infty}
 \frac{\log \alpha_{n+1}(x)}{\log\log q_n(x)}=1
\right\}=s.
\tag{4.46}
$$
The points supplied by this theorem are not badly approximable.

*Proof.* Let $\nu$ be the stationary, $s$-Ahlfors-regular measure from Proposition 4.2. For a nondecreasing function $F:[1,\infty)\to(2,\infty)$, put
$$
\psi(q)=\frac1{qF(q)}.
\tag{4.47}
$$
This is nonincreasing after an irrelevant finite modification. By Bénard--He--Zhang Theorem A' \cite[Theorem A']{BenardHeZhang2026},
$$
\nu(W(\psi))=
\begin{cases}
0,&\displaystyle\sum_q\frac1{qF(q)}<\infty,\\[4pt]
1,&\displaystyle\sum_q\frac1{qF(q)}=\infty,
\end{cases}
\tag{4.48}
$$
where $W(\psi)=\{x:|qx-p|<\psi(q)\text{ infinitely often}\}$.

In the convergence case, if $\alpha_{n+1}>F(q_n)$ infinitely often, the upper bound in (4.45) gives infinitely many solutions of $|q_nx-p_n|<\psi(q_n)$, contradicting (4.48). Hence
$$
\alpha_{n+1}(x)\le F(q_n(x))
\quad\text{eventually for }\nu\text{-a.e. }x.
\tag{4.49}
$$

In the divergence case, (4.48) gives infinitely many rational approximations
$$
\left|x-\frac pq\right|<\frac1{q^2F(q)}.
\tag{4.50}
$$
If $p/q=p'/q'$ is reduced, then $q'\le q$ and monotonicity of $F$ gives
$$
\frac1{q^2F(q)}\le\frac1{q'^2F(q')},
$$
so the reduced rational satisfies the same form of inequality. For irrational $x$, a fixed reduced rational $p'/q'$ can arise from only finitely many successful multiples: writing $(p,q)=(tp',tq')$, the original inequality $|qx-p|<1/(qF(q))$ becomes
$$
t|q'x-p'|<\frac1{tq'F(tq')},
$$
which is impossible for all sufficiently large $t$. Thus infinitely many original solutions yield infinitely many distinct reduced rationals. Since $F>2$, Legendre's theorem \cite[Theorem 1.1]{HanclNguyen2024} makes every sufficiently large reduced solution a convergent. The lower bound in (4.45) then implies
$$
\alpha_{n+1}(x)>F(q_n(x))-2
\quad\text{infinitely often for }\nu\text{-a.e. }x.
\tag{4.51}
$$

Take $F_\gamma(q)=(\log q)^\gamma$ for large $q$, modified near the origin to be nondecreasing and greater than $2$. The integral test gives convergence in (4.48) for $\gamma>1$ and divergence for $0<\gamma\le1$. Intersecting the conull upper events for $\gamma=1+1/r$, $r\ge1$, yields
$$
\limsup_n\frac{\log \alpha_{n+1}}{\log\log q_n}\le1,
\tag{4.52}
$$
while (4.51) with $\gamma=1$ gives $\alpha_{n+1}>\log q_n-2$ along an infinite subsequence. The corresponding denominators tend to infinity, and
$$
\frac{\log(\log q_n-2)}{\log\log q_n}\longrightarrow1,
$$
so the reverse limsup inequality follows. Thus the limsup equals $1$ for $\nu$-almost every point. Proposition 4.2 gives $\nu(\mathrm{ALA})=1$; the algebraic numbers are countable and $\nu$ is non-atomic. Since every full-$\nu$-measure set has Hausdorff dimension $s$, (4.46) follows. Finally, (4.51) with $F(q)=\log q$ makes the partial quotients unbounded, so these typical points do not lie in $\mathrm{BA}$. $\square$

## 4.8. Conclusion

The simultaneous BA--ALA problem remains open, including non-emptiness in full generality. The potential-winning strategy fails sharply: for every $c<s$, $\mathrm{ALA}$ and every compact tail $E_j$ are not $c$-potential-winning, as witnessed by closed guarded Ahlfors-regular subsets of the complement with dimensions tending to $s$. This yields only the canonical-$\mathbb R$ Cantor-winning exclusion $\varepsilon>1-s$; failure of every positive relative parameter is unproved without a BHNS splitting structure having limit set $X$ and splitting dimension $s$. Every finite feasible family of abundance obligations is compatible with a full-dimensional BA set, but the construction does not retain one fixed positive Markov constant through infinitely many stages. On the metric side, $\mathrm{ALA}$ does contain a full-dimensional set satisfying the sharp law (4.46), but those typical points are not badly approximable. The corresponding fixed-$\kappa$ reopening conditions are stated in P1 and P1′ below; a proof of (4.1) need not follow that route.
