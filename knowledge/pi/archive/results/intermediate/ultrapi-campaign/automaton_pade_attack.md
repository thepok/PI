# Automaton-adapted Padé and determinant attack

Audit date: **2026-08-12 UTC**  
Status: `literature-checked` bounded applicability audit with local
`proof sketch` separators  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

This attack found a genuine automaton-wide auxiliary form, but it does
**not** prove V1.

Fix a forbidden decimal word (w), put (q=10^n), and let
({\cal A}_n(w)) be the possible integers

\[
 p=3q+[u]_{10},\qquad u\in\{0,\ldots,9\}^n
 \text{ avoiding }w.
\]

Write (N_n=|{\cal A}_n(w)|).  If the fractional decimal expansion of
(\pi) avoids (w), then (p_n=\lfloor q\pi\rfloor\in{\cal A}_n(w)).
The integer polynomial

\[
 {\cal E}_{n,w}(Z)=\prod_{p\in{\cal A}_n(w)}(1+Z^p)\in\mathbb Z[Z]
                                                               \tag{1}
\]

is nonzero at (Z=e^{i/q}), and nevertheless

\[
 0<|{\cal E}_{n,w}(e^{i/q})|
 <q^{-1}\rho^{N_n-1},\qquad
 \rho=-2\cos 2=0.832293673\ldots<1.              \tag{2}
\]

Thus the finite-state language really does create exponentially small
forms.  This is stronger than the direct interpolation product previously
audited.  The exact size ledger, however, goes in the wrong direction:

\[
 \deg {\cal E}_{n,w}=\sum_{p\in{\cal A}_n(w)}p
       \in[3qN_n,4qN_n),\qquad
 L({\cal E}_{n,w})=2^{N_n}.                         \tag{3}
\]

The gain in (2) is only (O(N_n+\log q)), while known zero estimates pay
at least (N_n\log q) factorwise and vastly more after (1) is expanded as
a Lindemann--Weierstrass form.  The following exact separator survives
every batch size (s) and every multiplicity (t).  If
(\nu>\mu(\pi)>1) is any valid irrationality-exponent upper bound, the
upper and lower exponents for a batch containing (p_n) are

\[
 A=t\{\log q+(s-1)(-\log\rho)\},\qquad
 B=ts\{\nu\log q+\log(\pi/2)\}.                    \tag{4}
\]

Since (0<-\log\rho<\log q) for (q\ge10),

\[
 A\le ts\log q<B                                             \tag{5}
\]

for every (s,t\ge1).  Consequently the known lower bound is always
smaller than the constructed upper bound; increasing the automaton batch or
the zero multiplicity never reverses the inequality.

There are two further exact obstructions.

1. Exact Hermite interpolation at all language nodes needs degree at least
   (tN_n).  Moreover, any integer polynomial having multiplicity (t) at
   every node has coefficient height at least
   (q^{3t9^{n-1}}).  The (q^{-t}) proximity gain is paid once for each
   rational root when denominators are cleared.
2. Passing from the varying point (e^{i/q}) to the fixed special value
   (e^i) by a resultant removes the useful (q^{-1}) factor exactly.  If
   (g=(p_n,q)) and (x=q\pi-p_n\), its norm is

   \[
     |1-e^{-ix/g}|^g\le(x/g)^g,                    \tag{6}
   \]

   not (x/q).

The strongest outcome of this branch is therefore the explicit auxiliary
form (1) together with the parameter-free no-crossing inequality (5) and
the exact norm identity (6).  V1 remains a `conjecture`; this report is not
a candidate resolution.

## 1. Normalized target and negated hypothesis

Write

\[
 \pi=3+\sum_{j\ge1}d_j10^{-j},\qquad d_j\in\{0,\ldots,9\}.
\]

The canonical statement is

\[
 \forall m\ge1\ \forall w\in\{0,\ldots,9\}^m\ \exists k\ge1:
 d_kd_{k+1}\cdots d_{k+m-1}=w.                     \tag{7}
\]

Leading zeroes in (w) are significant, occurrences are in the
fractional stream, and irrationality of (\pi) removes terminating-decimal
ambiguity.  This branch assumes the negation for one fixed nonempty word:

\[
 d_k\cdots d_{k+m-1}\ne w\quad(k\ge1).             \tag{8}
\]

For (q=10^n), put

\[
 p_n=\lfloor q\pi\rfloor,\qquad x_n=q\pi-p_n\in(0,1).
                                                               \tag{9}
\]

Under (8), (p_n\in{\cal A}_n(w)) for every (n).  The goal is to turn
that membership, together with (e^{i\pi}=-1), into an arithmetic form
whose upper bound beats a nonvanishing lower bound.

## 2. Exact automaton dimension and entropy

Use the usual KMP prefix automaton with states (0,\ldots,m-1); the state
(m), which records an occurrence of (w), is deleted.  Let (M_w) be
the nonnegative integer transition matrix after summing over the ten digit
labels.  Then

\[
 N_n=e_0^{\mathsf T}M_w^n{\bf1}.                   \tag{10}
\]

This is an exact transfer-matrix count, not a statement about the selected
digit path of (\pi).

Two bounds are useful.  Choose any digit (c) appearing in (w).  Every
word over the other nine digits avoids (w), so

\[
 N_n\ge9^n.                                        \tag{11}
\]

On the other hand, splitting a word into aligned blocks of length (m)
gives

\[
 N_n\le10^m(10^m-1)^{n/m}=10^m\theta_w^n,
 \qquad \theta_w=(10^m-1)^{1/m}<10.                \tag{12}
\]

The exact Perron eigenvalue of (M_w) can improve (\theta_w), but the
only asymptotic feature used below is positive entropy:

\[
 9^n\le N_n=10^{\sigma_wn+O_w(1)},\qquad
 \log_{10}9\le\sigma_w<1.                          \tag{13}
\]

The exponentially many legal paths are the dimension cost of a universal
language assertion.  The matrix (M_w) compresses their **count**, but it
does not identify which path is (p_n).

## 3. Exact polynomial interpolation cost

Suppose (F\in\mathbb Z[X]\setminus\{0\}) has a zero of multiplicity at
least (t) at every rational point (p/q),
(p\in{\cal A}_n(w)).  Distinct zeros immediately give

\[
 D=\deg F\ge tN_n.                                  \tag{14}
\]

This is also the rank count for the confluent Vandermonde system: a scalar
degree-(D) Hermite ansatz has (D+1) coefficients and (tN_n)
independent value/derivative conditions.

There is a denominator-sensitive height bound which does not depend on a
genericity assumption.  Continue to use a digit (c) occurring in (w).
Among the (9^n) strings over digits other than (c), require the last
digit to lie in

\[
 \{1,3,7,9\}\setminus\{c\}.
\]

There are at least (3\cdot9^{n-1}) such strings.  Their corresponding
numerators (p=3q+[u]_{10}) are coprime to (q=10^n).  For each such
reduced root, Gauss's lemma makes the primitive factor (qX-p) divide
(F) in (\mathbb Z[X]).  Hence

\[
 \prod(qX-p)^t\mid F,
 \qquad
 H(F)\ge |\operatorname{lc}F|
       \ge q^{3t9^{n-1}}.                           \tag{15}
\]

Equations (14)--(15) are the exact dimension and coefficient-height costs
for language-uniform polynomial interpolation.

The minimal direct product makes the cancellation failure visible:

\[
 R_{n,t}(X)=\prod_{p\in{\cal A}_n(w)}(qX-p)^t.
                                                               \tag{16}
\]

It has degree (tN_n), leading coefficient (q^{tN_n}), and, under
(8), one factor (|q\pi-p_n|^t=x_n^t<1).  All other rational nodes lie
in ([3,4)), so with (\tau=4-\pi<1),

\[
 |R_{n,t}(\pi)|<(q\tau)^{t(N_n-1)}.                \tag{17}
\]

The right side grows because (q\tau>1).  Dividing (16) by (q^{tN_n})
produces the attractive analytic bound

\[
 \left|q^{-tN_n}R_{n,t}(\pi)\right|
 <q^{-t}\tau^{t(N_n-1)},                            \tag{18}
\]

but its common denominator is (q^{tN_n}).  Clearing it returns (17).
The language saves candidates relative to all (q) grid points; it does
not make the rational roots cheaper.

Status of this section: local `proof sketch`.  The divisibility and leading
coefficient arguments are exact; they have not been added to the
machine-checked track.

## 4. A stronger sine/exponential selector

The polynomial-root product loses the useful scale immediately.  Euler's
identity permits a better construction.  Let (S\subseteq{\cal A}_n(w))
be any batch of (s) candidates which contains (p_n), and let (t\ge1).
Define

\[
 E_{S,t}(Z)=\prod_{p\in S}(1+Z^p)^t\in\mathbb Z[Z].             \tag{19}
\]

All coefficients are nonnegative.  Consequently

\[
 \begin{aligned}
  3tqs&\le \deg E_{S,t}=t\sum_{p\in S}p<4tqs,\\
  L(E_{S,t})&=E_{S,t}(1)=2^{ts},\\
  H(E_{S,t})&\le2^{ts}.                              \tag{20}
 \end{aligned}
\]

The support contains the constant term and the (s) distinct one-factor
exponents (p\), so it has at least (s+1) monomials.  It also has at
least (t+1) monomials from the powers of any one factor.

Set (z_q=e^{i/q}).  Lindemann's theorem makes (z_q) transcendental, so
(E_{S,t}(z_q)\ne0).  For (y\in[3,4]),

\[
 |1+e^{iy}|=2|\cos(y/2)|\le\rho,
 \qquad \rho=-2\cos2<1.                             \tag{21}
\]

The maximum is at (y=4).  For completeness, the alternating cosine
series gives the rigorous enclosure

\[
 -{19\over45}<\cos2<-{131\over315},\qquad
 {262\over315}<\rho<{38\over45}<1.                 \tag{22}
\]

At the selected prefix,

\[
 1+e^{ip_n/q}=1-e^{-ix_n/q},\qquad
 |1-e^{-ix_n/q}|=2\sin(x_n/(2q))<q^{-1}.            \tag{23}
\]

Equations (21)--(23) prove

\[
 0<|E_{S,t}(z_q)|
 <q^{-t}\rho^{t(s-1)}.                              \tag{24}
\]

Taking (S={\cal A}_n(w)) gives (1)--(3).  This is the one material
positive finding of the branch: the whole language can be encoded in a
nonzero integer auxiliary polynomial whose value is exponentially small
in the automaton count.

Status of this section: local `proof sketch`.  No finite digit evidence is
used.

## 5. Optimization against the strongest simple zero estimate

The current peer-reviewed bound is

\[
 \mu(\pi)\le7.103205334137\ldots                    \tag{25}
\]

by Zeilberger--Zudilin.  More generally, fix any
(\nu>\mu(\pi)).  For all sufficiently large (q), uniformly in integers
(p),

\[
 |\pi-p/q|\ge q^{-\nu}.                             \tag{26}
\]

For (p/q\in[3,4]), concavity of sine on ([0,\pi/2]) gives

\[
 |1+e^{ip/q}|
 =2\sin\left({|p/q-\pi|\over2}\right)
 \ge {2\over\pi}|p/q-\pi|
 \ge {2\over\pi}q^{-\nu}.                         \tag{27}
\]

Multiplication over a batch gives the applicable lower bound

\[
 |E_{S,t}(z_q)|
 \ge\left({2\over\pi}q^{-\nu}\right)^{ts}.         \tag{28}
\]

Put (c=-\log\rho>0) and (b=\log(\pi/2)>0).  The upper bound (24) is
(e^{-A}) and the lower bound (28) is (e^{-B}), with (A,B) as in
(4).  Since (22) implies (\rho>1/10\),

\[
 0<c<\log10\le\log q.                              \tag{29}
\]

Therefore, for every possible choice (1\le s\le N_n) and (t\ge1),

\[
 A=t\{\log q+(s-1)c\}
 \le ts\log q
 <ts\{\nu\log q+b\}=B.                             \tag{30}
\]

A contradiction would require (A\ge B).  Equation (30) proves that no
parameter regime closes.  In particular:

- (s=1) is just the ordinary decimal rational approximation;
- increasing (s) earns the constant (c) per candidate but the lower
  bound pays (\nu\log q+b) per candidate;
- increasing (t) multiplies both sides and cancels from the comparison;
- taking (s=N_n\) uses all automaton entropy but does not change the sign.

Even the conjecturally optimal scalar value (\mu(\pi)=2) would leave the
strict inequality in (30).  Closing (24) would require a genuinely
language-sensitive joint lower bound, not a stronger ordinary irrationality
exponent.

Status of this section: `literature-checked` for (25), with a local exact
`proof sketch` comparison in (26)--(30).

## 6. Expanded Lindemann--Weierstrass parameters

One might hope that a joint linear-form theorem sees more than the product
of scalar bounds.  Expand the full product

\[
 {\cal E}_{n,w}(Z)=\sum_{k\in K}c_kZ^k,
 \qquad c_k\in\mathbb Z_{>0}.                       \tag{31}
\]

At (Z=e^{i/q}) this is a linear form in exponentials of the distinct
algebraic numbers (ik/q).  Let (M=|K|) and
(D=\deg{\cal E}_{n,w}).  The exact size bounds are

\[
 N_n+1\le M\le D+1,qquad
 3qN_n\le D<4qN_n,qquad
 \max_k\log c_k\le N_n\log2.                       \tag{32}
\]

The exponents have algebraic degree at most (2) and Weil height at most
(\log D).  Thus Huang's Theorem 1.2 applies with

\[
 m=M,quad d=2,quad
 h\le h_0=\max\{\log D,N_n\log2\}.                 \tag{33}
\]

For inspection, Huang's explicit lower bound is

\[
 \log|\Lambda|\ge-B_H,
\]

\[
 B_H=e^{8\delta\zeta}
 +r_Hm^\delta e^{6\delta^2\zeta}
   \left(mh+{39\over164}\zeta+e^{R_H}\right),       \tag{34}
\]

where

\[
 \begin{aligned}
 \delta&=d^{2m},\\
 \zeta&=md^{6m}(2h/d+3),\\
 r_H&=82(9/2)^\delta\delta^{3\delta+2},\\
 R_H&=r'_Hm^\delta e^{6\delta^2\zeta}
 +r''_Hm^\delta e^{6\delta^2\zeta}(\log m+6\delta\zeta)
 +72e^{2\delta\zeta},\\
 r'_H&=12(9/2)^\delta\delta^{3\delta+2}
 +16(1+6\delta^2)(9/2)^\delta\delta^{3\delta}\log(9\delta^3)\\
 &\quad+80(9/2)^\delta\delta^{3\delta+4}(1+6\delta)\zeta,\\
 r''_H&=16(1+6\delta^2)(9/2)^\delta\delta^{3\delta}.
                                                               \tag{35}
 \end{aligned}
\]

There is no hidden numerical contest here.  Already (h\ge0), (d=2),
and (M\ge N_n+1) give

\[
 B_H\ge e^{8\delta\zeta}
 \ge\exp\!\left(24M2^{8M}\right),                  \tag{36}
\]

whereas (2) has upper exponent

\[
 \log q+(N_n-1)c<2N_n                              \tag{37}
\]

for (n\ge1), using (\log q=n\log10\le9^n\le N_n) and (c<1).
The theorem's lower bound is therefore astronomically below the constructed
upper bound.  The exact automaton saving (N_n<q) does not help because the
expanded form has (M\ge N_n+1) terms and degree (\Theta(qN_n)).

Cijsouw's Theorem 1 gives the cleaner fixed-α shape

\[
 \log|P(e^\alpha)|
 >-C(\alpha)D^2(D+\log H),                          \tag{38}
\]

but here (\alpha=i/q) varies with (n), and its constant is not uniform.
Even disregarding that problem, substituting (3) produces a complexity
scale at least cubic in (qN_n), not the (O(N_n)) exponent in (2).

Status of this section: `literature-checked` applicability audit.  The
explicit substitutions are deliberately pessimistic in favor of the
published lower bounds; they still do not approach (2).

## 7. The fixed-(e^i) resultant removes the decimal gain

The dependence (z_q=e^{i/q}) is not cosmetic.  It is tempting to descend
(1) to a polynomial at the fixed transcendental number (e^i).  The exact
resultant shows what is lost.

For integers (p,q\ge1), let (g=(p,q)) and (r=q/g).  Directly from the
(q) roots of (Y^q-X),

\[
 \operatorname{Res}_Y(Y^q-X,1+Y^p)
 =\left(1-(-1)^rX^{p/g}\right)^g.                  \tag{39}
\]

By multiplicativity,

\[
 {\cal R}_{n,w}(X)
 :=\operatorname{Res}_Y(Y^q-X,{\cal E}_{n,w}(Y))
 =\prod_{p\in{\cal A}_n(w)}
   \left(1-(-1)^{q/g_p}X^{p/g_p}\right)^{g_p},      \tag{40}
\]

where (g_p=(p,q)).

For the selected (p_n=q\pi-x_n),

\[
 e^{ip_n/g_{p_n}}
 =(-1)^{q/g_{p_n}}e^{-ix_n/g_{p_n}}.
\]

Consequently its factor in ({\cal R}_{n,w}(e^i)) is exactly

\[
 \left(1-e^{-ix_n/g_{p_n}}\right)^{g_{p_n}},        \tag{41}
\]

whose modulus is at most ((x_n/g_{p_n})^{g_{p_n}}).  For the generic
case (g_{p_n}=1), the smallness is only (x_n<1): the (q^{-1}) from
(23) has disappeared.  A large gcd would mean special terminal divisibility
of the actual prefix; omission of an arbitrary word supplies no such gcd.

The coefficient ledger also remains large.  Since length is
submultiplicative,

\[
 L({\cal R}_{n,w})\le2^{\sum_{p\in{\cal A}_n(w)}g_p}.             \tag{42}
\]

For all residues, the exact divisor sum is

\[
 \sum_{a=0}^{q-1}(a,q)
 =\sum_{d\mid q}d\,\varphi(q/d)
 ={q\over10}(n+2)(4n+5),\qquad q=10^n.             \tag{43}
\]

Thus (42) can still cost (\exp(O(qn^2))).  More importantly, (41)
proves that an exact norm to the fixed value (e^i) cannot preserve the
only (q)-scale small factor.

Status of this section: local `proof sketch`; identities (39) and (43) are
checked exactly by the companion script.

## 8. Why transfer matrices and determinants do not compress the OR

There is a simple algebraic model of the selection problem.  Let
(Y_1,\ldots,Y_s) stand for the (s) candidate small forms.  If a
polynomial

\[
 \Phi(Y_1,\ldots,Y_s)
\]

vanishes whenever **any one** coordinate is zero, then every (Y_j)
divides (\Phi), hence

\[
 Y_1Y_2\cdots Y_s\mid\Phi,qquad\deg\Phi\ge s.       \tag{44}
\]

This is the exact algebraic cost of turning the unknown statement “one of
these (s) candidates is selected” into a universal polynomial zero.  A
determinant may provide a small arithmetic circuit for the same expression,
but degree, height, and the number of exponential terms used by zero
estimates do not measure circuit description length.

There are two possible loopholes, both audited above.

1. The actual sine samples are not algebraically independent variables:
   they are powers of (e^{i/q}).  Formula (19) exploits that
   specialization exactly.  Its intrinsic degree and length are (20), and
   its best simple lower-bound comparison is blocked by (30).
2. One can try to compress the powers by adjoining a (q)-th root of
   (e^i).  The exact norm (39)--(41) then removes the decimal-scale gain.

A standard Siegel-lemma Padé construction has a related mismatch.  Formal
Taylor conditions at (0) have rational coefficients and can be imposed
arithmetically, but they contain no forbidden-language information.
Conditions at the rational points (p/q) involve the transcendental values
(e^{ip/q}), so they are not integer linear equations to which Siegel's
lemma applies.  Enforcing the nodes through rational polynomial roots gives
(14)--(18); enforcing them through powers of one exponential gives
(19)--(43).

Rivoal's simultaneous Padé construction for Euler, exponential, and
logarithmic functions does not alter this accounting: it creates high
formal multiplicity for fixed analytic functions, not a low-height
disjunction over (N_n) finite-state paths.

## 9. Exact checker

Companion:
[`automaton_pade_attack_check.py`](automaton_pade_attack_check.py)

It checks, without reading any digits of (\pi):

- KMP automaton counts against exhaustive enumeration for several words;
- (N_n\ge9^n) and the (3\cdot9^{n-1}) coprime-node lower bound;
- the exact degree and length of a finite instance of (19);
- the resultant identity (39) for a grid of (p,q);
- the divisor sum (43) for (n=1,\ldots,5);
- the rational sign pattern behind the no-crossing inequality (30).

Exact run:

```text
PASS: automaton counts, selector size, resultants, gcd sums, and separator inequalities
```

These finite checks are labeled `experiment`.  They validate formulas in
the report; they are not evidence that V1 holds.

## 10. Primary-source audit

Status: `literature-checked` through **2026-08-12 UTC** for the bounded
search below.  This is not a claim that all relevant literature has been
exhausted.

| Source | Exact use here | Applicability boundary |
|---|---|---|
| [Guibas--Odlyzko, *String overlaps, pattern matching, and nontransitive games* (1981)](https://doi.org/10.1016/0097-3165(81)90005-4) | Finite automata and rational transfer functions for one-word avoidance. | Counts all paths; does not select the (\pi) path. |
| [Cijsouw, *Transcendence measures of exponentials and logarithms of algebraic numbers* (1974)](https://www.numdam.org/item/CM_1974__28_2_163_0.pdf), Theorem 1, printed p. 164 | Bound (38) for a polynomial at (e^\alpha). | The constant depends on (\alpha=i/q); degree (\Theta(qN_n)) already overwhelms (2). |
| [Huang, *Explicit Bounds for Linear Forms in the Exponentials of Algebraic Numbers* (2022)](https://arxiv.org/abs/2112.05004), Theorem 1.2 | Fully explicit variable-height bound (34)--(35). | Exact substitution (32)--(37) is vastly too weak. |
| [Zeilberger--Zudilin, *The Irrationality Measure of Pi is at most 7.103205334137...* (2020)](https://doi.org/10.2140/moscow.2020.9.407) | Peer-reviewed scalar estimate (25). | Its factorwise consequence has the exact wrong-sign inequality (30); even exponent (2) would not close it. |
| [Rivoal, *Simultaneous Padé approximants to the Euler, exponential and logarithmic functions* (2015)](https://doi.org/10.5802/jtnb.914) | Representative arithmetic simultaneous-Padé construction. | Supplies fixed-function multiplicity, not a language-sensitive selected-path form. |

An exact-title arXiv query for *irrationality measure of pi*, dated
2026-08-12 UTC, returned the peer-reviewed Zeilberger--Zudilin paper plus
later unrefereed claims and applications, but no independently validated
replacement used in this audit.  The numerical value (25) is not essential:
the separator (30) holds for every exponent (\nu>1).

PDF pins fetched on 2026-08-12 UTC:

| Source | SHA-256 |
|---|---|
| Cijsouw 1974 | `fc31f7cf4ce0177a46966c0ef41b05c6252c0d4f3abb762d50c2e43e7f48a46a` |
| Huang, arXiv:2112.05004v2 | `050006233128531e25866579b13f599abb0d4e486b1a3959aad0b3c35fad95f2` |
| Zeilberger--Zudilin, arXiv:1912.06345v2 | `b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f` |

Search phrases covered combinations of *regular language Hermite Padé*,
*finite automaton exponential polynomial*, *effective
Lindemann--Weierstrass*, *restricted numerator transcendence measure*,
*integer Chebyshev arc*, and *irrationality measure of pi*.  No primary
theorem was found whose lower bound improves because the numerator belongs
to a one-word-avoidance language.

## 11. Exact missing theorem

The new construction reduces the remaining gap to a particularly concrete
statement.  A successful version of this route would need, for every fixed
forbidden word (w), a **joint**, language-sensitive lower bound of the form

\[
 \left|\prod_{p\in{\cal A}_n(w)}
       (1+e^{ip/10^n})\right|
 \ge \exp(-C_wN_n)                                  \tag{45}
\]

with a constant (C_w<-\log\rho), or a different auxiliary form with a
strictly better evaluation/degree/height ratio.  Ordinary irrationality
measures give (C_w\) growing like (\nu\log q); explicit
Lindemann--Weierstrass gives much worse dependence; the fixed-(e^i) norm
loses (q^{-1}).

Bound (45) would have to use the distribution of the entire regular-language
set relative to the particular zero (\pi), rather than only the height of
its elements.  No such theorem is known from the dated search.  Without it,
the automaton-adapted Padé/determinant route stops at the exact separators
(30), (36), and (41), and V1 does not follow.
