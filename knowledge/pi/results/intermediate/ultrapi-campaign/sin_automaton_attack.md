# Sine, Padé, and finite-state interpolation attack

Audit date: **2026-08-12 UTC**  
Status: `literature-checked` bounded applicability audit with local `proof sketch`
lemmas  
Canonical target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict

This route does **not** prove that every finite decimal word occurs in
\(\pi\).  Two exact deductions sharpen the obstruction.

First, if

\[
 q_n=10^n,\qquad p_n=\lfloor q_n\pi\rfloor,\qquad
 x_n=q_n\pi-p_n=\{10^n\pi\},
\]

then, for every \(n\geq1\),

\[
 \sin(p_n/q_n)=\sin(x_n/q_n),\qquad
 x_n=q_n\arcsin\!\bigl(\sin(p_n/q_n)\bigr),          \tag{1}
\]

where \(\arcsin\) is the principal real branch.  Thus the normalized sine
sample recovers the original decimal tail **exactly**.  In particular,

\[
 0\leq x_n-q_n\sin(p_n/q_n)\leq {1\over6q_n^2}.     \tag{2}
\]

The apparent small value of sine is only the universal truncation error
\(q_n^{-1}\); after the natural rescaling it is the same unproved
base-10 orbit again.  Padé approximation of sine or the exponential does not
create a new quantity to control.

Second, fix a word \(w\).  Let \(S_w\) be the set of **all** possible
numerators \(3\cdot10^n+\operatorname{val}(u)\), where \(u\) is an
\(n\)-digit string avoiding \(w\).  There is a nonzero entire function

\[
 E_w(z)=\prod_{a\in S_w}\left(1-{z\over a}\right)  \tag{3}
\]

of order strictly less than one which vanishes at every point of \(S_w\).
The product converges because \(\sum_{a\in S_w}a^{-1}<\infty\).  Hence even
the complete set of admissible truncation numerators is not a uniqueness set
for entire functions of very small growth.  Carlson, Pólya, and interpolation
arguments cannot identify an auxiliary function merely from vanishing on
these nodes.

The finite-state language does yield an exact matrix Mahler system, but that
system sums over **all** admissible paths.  It does not generate the one path
formed by the digits of \(\pi\).  No inspected theorem couples the special
zero \(\sin\pi=0\) to that path strongly enough to exclude it from a
positive-entropy forbidden-word subshift.

The target remains a `conjecture`.  This report contains no candidate
resolution and makes no inference from finite digit computations.

## 1. Exact target and the negated hypothesis

Write the canonical nonterminating decimal expansion

\[
 \pi=3+\sum_{j\geq1}d_j10^{-j},\qquad
 d_j\in\{0,\ldots,9\}.
\]

The target quantifiers are

\[
 \forall m\geq1\ \forall w\in\{0,\ldots,9\}^m\
 \exists k\geq1:\quad d_kd_{k+1}\cdots d_{k+m-1}=w. \tag{4}
\]

Leading zeroes in \(w\) are significant.  Occurrences are confined to the
fractional digit stream.  Since \(\pi\) is irrational, the two-expansion
ambiguity at terminating decimals is absent.

For a word \(w\) with value \(a\in\{0,\ldots,10^m-1\}\), put

\[
 I_w=[a10^{-m},(a+1)10^{-m}).                       \tag{5}
\]

The negation relevant to one word is

\[
 d_k\cdots d_{k+m-1}\neq w\quad\hbox{for every }k\geq1,
                                                               \tag{6}
\]

equivalently

\[
 x_n=\{10^n\pi\}\notin I_w\quad\hbox{for every }n\geq0.       \tag{7}
\]

This is the pointwise survivor condition that every proposed analytic
argument must actually contradict.

## 2. What \(\sin\pi=0\) says at decimal truncations

Let \(q_n,p_n,x_n\) be as in the verdict.  Then

\[
 {p_n\over q_n}=\pi-{x_n\over q_n}.                 \tag{8}
\]

Because \(0\leq x_n/q_n<1/10<\pi/2\),

\[
 \sin(p_n/q_n)
 =\sin(\pi-x_n/q_n)
 =\sin(x_n/q_n),                                    \tag{9}
\]

and the principal inverse sine gives (1).  Taylor's alternating bound
\(t-t^3/6\leq\sin t\leq t\), valid here for
\(0\leq t\leq1/10\), gives (2).

There are two other exact forms worth recording.  Since \(10^n\) is even
for \(n\geq1\),

\[
 \sin x_n=-\sin p_n,
 \qquad x_n=\arcsin(-\sin p_n),                     \tag{10}
\]

because \(0\leq x_n<1<\pi/2\).  Euler's identity gives

\[
 e^{ip_n/q_n}+1=1-e^{-ix_n/q_n}.                    \tag{11}
\]

In particular,

\[
 q_n\bigl(e^{ip_n/q_n}+1\bigr)=ix_n+O(q_n^{-1})     \tag{12}
\]

uniformly in \(n\).  For example, the elementary exponential remainder
bound gives

\[
 \left|q_n(1-e^{-ix_n/q_n})-ix_n\right|
 \leq {e^{1/10}\over2q_n}.                          \tag{13}
\]

Equations (1), (10), and (12) locate the precise normalization issue.
Unscaled sine and exponential values are small for every decimal truncation
of every real zero under consideration.  At the scale where their leading
term has content, that leading term is \(x_n\), the original decimal shift.
Consequently, proving from (9) or (11) that a prescribed interval is hit is
not a softer approximation problem: by (1), it is exactly (7) again.

Status of this section: `proof sketch`; every displayed identity follows
from elementary trigonometry and Taylor's theorem, but it has not been added
to the machine-checked track.

## 3. The automaton gives controlled dynamics, not a recurrence

The truncations satisfy

\[
 p_{n+1}=10p_n+d_{n+1},\qquad
 x_{n+1}=10x_n-d_{n+1}.                             \tag{14}
\]

If \(w\) is absent, a KMP prefix automaton constrains which digit
\(d_{n+1}\) may follow the current suffix state.  It does not determine that
digit.  Thus (14) is a finite-state **controlled** recurrence, not a scalar
linear recurrence and not a finite decimation kernel.

The branching cannot be treated as a small technical defect.  Choose one
digit \(c\) occurring in \(w\) and let

\[
 A=\{0,\ldots,9\}\setminus\{c\}.
\]

Every infinite sequence over the nine-symbol alphabet \(A\) avoids \(w\).
Hence the survivor automaton contains a full nine-symbol subsystem and can
carry arbitrary path complexity.  A finite automaton recognizing all legal
prefixes is therefore categorically different from an automaton outputting
the \(n\)-th digit of one sequence from the base-10 digits of \(n\).

The same point appears in the exponential notation.  From (10), put
\(z_n=e^{ip_n}=e^{-ix_n}\).  Then (14) gives

\[
 z_{n+1}=e^{id_{n+1}}z_n^{10}.                      \tag{15}
\]

The multiplier in (15) is selected by the uncontrolled next digit.  The
finite-state constraint does not turn (15) into iteration of one rational,
algebraic, or Mahler map.

## 4. The exact all-path Mahler system

It is useful to write down what the automaton **does** provide.  Let \(Q\)
be its non-forbidden states, let \(s\) be the initial state, and let \(T_d\)
be the zero-one transition matrix for reading digit \(d\), with a transition
to the deleted forbidden state represented by zero.  For a finite word
\(u=u_1\cdots u_n\), let

\[
 [u]_{10}=\sum_{j=1}^n u_j10^{n-j}.
\]

Define the row-vector polynomial

\[
 V_n(z)=\sum_{\substack{u\in\{0,\ldots,9\}^n\\u\text{ avoids }w}}
       z^{[u]_{10}}e_{\operatorname{state}(u)}.       \tag{16}
\]

Appending a digit gives the exact recursion

\[
 V_0(z)=e_s,\qquad
 V_{n+1}(z)=\sum_{d=0}^9 z^dV_n(z^{10})T_d.          \tag{17}
\]

Consequently the bivariate generating function

\[
 G(t,z)=\sum_{n\geq0}t^nV_n(z)                      \tag{18}
\]

satisfies the genuine 10-Mahler system

\[
 G(t,z)=e_s+t\sum_{d=0}^9 z^dG(t,z^{10})T_d.        \tag{19}
\]

For \(z=e^{i/10^n}\), the components of \(V_n(z)\) aggregate the values
\(e^{i[u]_{10}/10^n}\) over all legal words.  Their imaginary parts
aggregate the corresponding sine samples.  Nothing in (17)--(19) bounds the
one summand indexed by the actual prefix of \(\pi\).  Cancellation in the
sum may coexist with a distinguished summand of any permitted phase.

This is the exact point at which a regular-language generating function is
often mistaken for a generating function of the selected digit path.  The
former has (19); the latter would need a fixed decimation relation which
word avoidance does not supply.

Status of this section: local `proof sketch`.  Formula (17) is checked by
the identity \([ud]_{10}=10[u]_{10}+d\); no distributional claim is made.

## 5. Admissible numerators are not an entire-function uniqueness set

This section gives a sharper obstruction than merely noting that the
language has positive entropy.

Let \({\cal L}_n(w)\) be the set of length-\(n\) strings which avoid \(w\),
with leading zeroes retained, and define

\[
 S_w=
 \left\{3\cdot10^n+[u]_{10}:n\geq1,
           \ u\in{\cal L}_n(w)\right\}.             \tag{20}
\]

If the fractional digits of \(\pi\) avoid \(w\), then

\[
 p_n\in S_w\qquad(n\geq1).                          \tag{21}
\]

Let \(m=|w|\) and

\[
 \theta_m=(10^m-1)^{1/m}<10,qquad
 \sigma_m={\log\theta_m\over\log10}<1.             \tag{22}
\]

Partition a length-\(n\) word into disjoint aligned blocks of length \(m\)
and one remainder.  Each full block has at most \(10^m-1\) choices, since it
cannot equal \(w\).  Therefore there is a constant \(C_m\) such that

\[
 |{\cal L}_n(w)|\leq C_m\theta_m^n.                 \tag{23}
\]

Every element of the \(n\)-th shell of (20) is at least \(3\cdot10^n\), so

\[
 \sum_{a\in S_w}{1\over a}
 \leq {C_m\over3}\sum_{n\geq1}
       \left({\theta_m\over10}\right)^n
 <\infty.                                           \tag{24}
\]

The shells \([3\cdot10^n,4\cdot10^n)\) are disjoint.  It follows from
(24), directly by uniform convergence on compact sets, that

\[
 E_w(z)=\prod_{a\in S_w}\left(1-{z\over a}\right)  \tag{25}
\]

is a nonzero entire function, \(E_w(0)=1\), and vanishes on every
admissible numerator.

There is also a quantitative growth statement.  Equation (23) gives

\[
 \#(S_w\cap[0,R])=O_w(R^{\sigma_m}).                 \tag{26}
\]

Splitting \(\log|E_w(z)|\) into zeros below \(2|z|\) and the tail above
\(2|z|\), and using (24) by dyadic summation, gives, for every
\(\varepsilon>0\),

\[
 \log\max_{|z|\leq R}|E_w(z)|
 =O_{w,\varepsilon}(R^{\sigma_m+\varepsilon}).       \tag{27}
\]

Thus \(E_w\) has order at most \(\sigma_m<1\) (the harmless
\(\varepsilon\) formulation already suffices).  In particular it has
exponential type zero.

Equations (24)--(27) are an explicit separator for a Carlson-style plan.
Vanishing on all nonnegative integers can force a sufficiently small entire
function to vanish identically; vanishing on the regular-language node set
\(S_w\) cannot.  A nonzero function of order below one already vanishes on
all of it.  Modern density theorems for Bernstein-space interpolation make
the same density dependence explicit, but (25) is enough here and requires
no black-box sampling theorem.

Notice that the rational nodes \(a/10^n\) have accumulation points in the
survivor set.  This does not revive the identity theorem: the numbers
\(\sin(a/10^n)\) are not zero.  Along the selected prefixes they merely tend
to zero at the universal rate (9).  Continuity then recovers the already
known zero \(\sin\pi=0\), not a contradiction.

Status of this section: `proof sketch`.  It is an exact analytic
construction, not a finite experiment and not a machine-checked claim.

## 6. Why polynomial interpolation and Padé size estimates do not close

At level \(n\), let \(N_n=|{\cal L}_n(w)|\) and consider the most direct
integer interpolation polynomial

\[
 B_n(X)=\prod_{u\in{\cal L}_n(w)}
 \left(q_nX-3q_n-[u]_{10}\right)\in\mathbb Z[X].    \tag{28}
\]

Its degree is \(N_n\), and its leading coefficient is exactly
\(q_n^{N_n}\), so

\[
 \log H(B_n)\geq N_n\log q_n.                       \tag{29}
\]

If the actual prefix avoids \(w\), one factor of \(B_n(\pi)\) is
\(x_n<1\); every other factor can have size comparable with \(q_n\).  The
elementary upper bound is only

\[
 |B_n(\pi)|\leq q_n^{N_n-1},                        \tag{30}
\]

which is enormous.  Dividing each factor by \(q_n\) makes a normalized
product potentially small, but introduces the denominator \(q_n^{N_n}\);
clearing it returns (28).  The entropy saving \(N_n\ll q_n^{\sigma_m}\)
does not create a small nonzero integer polynomial value.

The same accounting governs a Padé auxiliary form.  Classical Padé
approximants to \(e^z\), \(\sin z\), or \(\log(1-z)\) exploit a high-order
zero of a fixed analytic remainder.  Evaluating at \(p_n/q_n\) and clearing
denominators charges powers of \(q_n\).  Standard effective
Lindemann--Weierstrass or logarithm measures see the algebraic degree and
height of \(p_n/q_n\), not whether its decimal numerator lies in one regular
language.

In the present case the exact small exponential form is

\[
 \left|e^{ip_n/q_n}+1\right|
 =2\sin\left({x_n\over2q_n}\right)<q_n^{-1}.        \tag{31}
\]

This exponent one is universal.  Cijsouw's polynomial measure for
\(\log(-1)=i\pi\), Huang's effective lower bounds for linear forms in
exponentials of algebraic numbers, and the current scalar irrationality
measure for \(\pi\) all permit values vastly smaller than (31).  A
height-only application therefore cannot contradict it.

Rivoal's restricted-denominator work is an especially direct audit of the
Padé hope.  At applicable positive rational logarithms it turns a sharp
bound for denominators \(B^n\) into lower bounds on the number of nonzero
base-\(B\) digits.  It does not give occurrence of an arbitrary word, and
its hypotheses do not include the branch \(\log(-1)=i\pi\).  The later
simultaneous Padé construction for the exponential and logarithm likewise
does not add a regular-language numerator condition.

A Padé theorem strong enough for this route would have to use the language
membership, not merely the height, to prove a bound which excludes every
\(p\in S_w\) from the unit interval around \(q_n\pi\).  But that exclusion
is precisely the assertion that the decimal prefix of \(\pi\) cannot remain
in \({\cal L}_n(w)\).  No such digit-sensitive auxiliary form was found.

## 7. Pólya--Carlson, D-finiteness, and E-function zeros

There are three distinct analytic series which should not be conflated.

1. The length generating function
   \(\sum_n|{\cal L}_n(w)|t^n\) is rational by finite-state transfer
   matrices (and has the more precise Guibas--Odlyzko correlation formula).
2. The all-path value generating system \(G(t,z)\) satisfies the Mahler
   equation (19).
3. The selected digit series
   \(D_\pi(z)=\sum_{n\geq1}d_nz^n\) is not supplied by either of the first
   two objects.

If \(D_\pi\) were D-finite, Bell--Chen's finite-coefficient theorem would
make it rational.  Evaluating at \(z=1/10\) would then make
\(D_\pi(1/10)=\pi-3\) algebraic, impossible.  Thus the actual digit series
is not D-finite.  The finite-coefficient Pólya--Carlson/Szegő dichotomy puts
it on the natural-boundary side rather than yielding a contradiction.
Forbidden-word paths can have the same natural-boundary behavior.

The current theory of zeros of E-functions and exponential polynomials
studies multiplicity, common zeros, and factorization.  It does not state
that a zero has a disjunctive base expansion.  Even the broad class “zero of
an E-function” cannot imply digit coverage: a nonzero rational with a
terminating or periodic decimal is a zero of a polynomial, hence of an
E-function.  The special arithmetic fact for \(\pi\) is not merely that it is
an E-function zero, but that it is the particular nonzero zero of sine.
No inspected zero theorem turns that distinction into a decimal cylinder
hit.

## 8. Positive-entropy separators and the remaining fixed-point gap

The nine-symbol subsystem from Section 3 gives an exact separator for every
argument that uses only the forbidden-word automaton.  It contains
uncountably many paths, including paths with exponential factor complexity,
non-D-finite digit series, and natural boundaries.  Transfer-matrix and
regular-language Fourier estimates average over these paths and do not
select one of them.

Here are explicit separators, one for every proposed forbidden word.  Choose
a digit \(c\) occurring in \(w\).

1. Choose \(a\in\{1,\ldots,8\}\) with \(w\neq a^{|w|}\).  Then
   \(a/9=0.\overline a\) avoids \(w\) and is a zero of the polynomial
   \(9X-a\), hence a zero of an E-function.  Therefore the bare property
   “is a zero of an E-function” cannot imply digit coverage.
2. Let \((t_n)_{n\geq0}\) be the Thue--Morse sequence, choose distinct
   decimal digits \(a,b\neq c\), and put

   \[
    \eta_{w}=
    \sum_{n\geq0}\bigl(a+(b-a)t_n\bigr)10^{-n-1}.    \tag{32}
   \]

   Its digits lie in \(\{a,b\}\), so it avoids \(c\), hence \(w\).
   Equation (32) is a nonconstant rational affine image of the decimal
   Thue--Morse number.  Bugeaud's theorem therefore gives
   \(\mu(\eta_w)=2\), and the number is transcendental; its digit series is
   automatic and satisfies a Mahler equation.  Thus transcendence, optimal
   scalar irrationality exponent, and genuine selected-path Mahler structure
   coexist with membership in every \(K_w\).
3. There also exists \(\zeta_w\in K_w\) which obeys a polynomial
   degree--height lower bound of the same functional strength class as the
   Cijsouw bound used for \(\pi\).  Indeed, let \(A\) be the nine decimal
   digits other than \(c\), let \(K_A\) carry its uniform self-similar
   measure \(\nu\), and put \(s=\log9/\log10\).  The level-cylinder estimate
   gives \(\nu(B(x,r))\leq C_Ar^s\).  For every degree \(D\geq1\) and
   dyadic height shell \(2^{k-1}<H\leq2^k\), delete radius

   \[
     r_{D,k}=\left(
       {2^{-D-k-4}\over C_AD(2^{k+1}+1)^{D+1}}
     \right)^{1/s}                                  \tag{33}
   \]

   around each root of each nonzero integer polynomial of degree at most
   \(D\) and height at most \(2^k\).  The total deleted \(\nu\)-measure is
   at most \(1/8\).  Any \(\zeta_w\) in the remainder is transcendental,
   avoids \(w\), and factorization of \(P\) gives, after enlarging a constant
   depending only on \(A\),

   \[
    |P(\zeta_w)|\geq
    \exp\!\left[-C_A'D^2(D+\log H)(1+\log D)^2\right]           \tag{34}
   \]

   for every nonconstant \(P\in\mathbb Z[X]\) of degree \(D\) and height
   \(H\).  Constants are not claimed to equal Cijsouw's.  The separator is
   about the logical output and its degree--height shape: even that strong a
   generic polynomial nonapproximation property does not force one digit,
   much less every word.

Items 1--3 are `proof sketch` separators.  They deliberately stop short of
the property that is genuinely special to \(\pi\): none is asserted to
satisfy \(e^{i\eta}=-1\), or even to have an algebraic exponential.

This does **not** erase the one genuinely \(\pi\)-specific datum:
\(e^{i\pi}=-1\).  Rather, equations (1) and (11) show exactly how that datum
enters.  It converts the selected truncation into a small exponential form,
but the leading coefficient of that form is the selected tail \(x_n\).  The
finite-state hypothesis constrains the same tail.  Hence the two inputs meet
in a tautological encoding, not in two independent estimates.

The first non-generic implication in the hoped-for proof chain is now
visible line by line:

\[
 \begin{array}{rcll}
 w\text{ omitted from }\pi
   &\Longrightarrow& p_n\in S_w &\text{(finite-state information)},\\[2mm]
 e^{i\pi}=-1
   &\Longrightarrow& |e^{ip_n/q_n}+1|<q_n^{-1}
       &\text{(information unique to }\pi\text{ here)},\\[2mm]
 p\in S_w\cap[3q_n,4q_n)
   &\centernot\Longrightarrow&
     |e^{ip/q_n}+1|\geq q_n^{-1}
       &\text{(the missing digit-sensitive theorem).}
 \end{array}                                             \tag{35}
\]

Effective Lindemann--Weierstrass applies to each algebraic exponent
\(ip_n/q_n\), but its lower bound depends on ordinary degree and height and
is far below \(q_n^{-1}\).  Membership in \(S_w\) is invisible to that
theorem.  Thus \(e^{i\pi}=-1\) is the first input not shared by the explicit
survivor separators, while the first **unproved** implication is the final
line of (35): turning regular-language membership into a stronger
exponential separation estimate.

One can phrase the missing bridge in any of the following equivalent useful
ways.

- **Digit-sensitive exponential separation:** prove that for every
  forbidden word \(w\), all sufficiently large \(n\), and every
  \(p\in S_w\), the value \(|e^{ip/10^n}+1|\) is too large for \(p\) to be
  \(\lfloor10^n\pi\rfloor\).  Known bounds depend on height, not membership
  in \(S_w\).
- **Selected-path transfer:** derive a fixed functional or decimation
  equation for the one path \((d_n)\) from the all-path system (19).
  Positive entropy shows that avoidance alone cannot do this.
- **Normalized sine orbit:** prove that the exact values
  \(q_n\arcsin(\sin(p_n/q_n))=x_n\) enter every decimal cylinder.  This is
  exactly V1 in analytic notation.
- **Language-adapted Padé form:** construct integer auxiliary forms whose
  extra smallness follows from the whole regular-language constraint while
  their degree and height remain below the applicable transcendence lower
  bound.  The direct product (28) fails the height accounting.

The first three are restatements or sufficient conditions at essentially the
same pointwise strength as the target.  The fourth is the only potentially
different route isolated here, and no construction meeting its size
requirements is known.

## 9. Literature audit

Status: `literature-checked` through **2026-08-12 UTC** for the bounded search
described below.  This is not a claim that all relevant literature has been
exhausted.

- Guibas--Odlyzko, *String overlaps, pattern matching, and nontransitive
  games* (1981), gives the exact rational generating functions which count
  strings avoiding prescribed patterns.  It counts all strings and does not
  select a path:
  <https://doi.org/10.1016/0097-3165(81)90005-4>.
- Cijsouw, *Transcendence measures of exponentials and logarithms of
  algebraic numbers* (1974), Theorems 1--2, gives degree--height measures for
  \(e^\alpha\) and a fixed \(\log\alpha\), including \(i\pi=\log(-1)\):
  <https://www.numdam.org/item/CM_1974__28_2_163_0.pdf>.
- Huang, *Explicit Bounds for Linear Forms in the Exponentials of Algebraic
  Numbers* (2022), treats forms such as the left side of (31), but its
  explicit parameters are algebraic degrees and heights, not decimal
  automaton states: <https://arxiv.org/abs/2112.05004>.
- Rivoal, *Convergents and irrationality measures of logarithms* (2007),
  derives nonzero-digit consequences from Padé estimates with restricted
  denominators; its logarithms and conclusion do not cover (4):
  <https://doi.org/10.4171/RMI/519>.
- Rivoal, *Simultaneous Padé approximants to the Euler, exponential and
  logarithmic functions* (2015), supplies a modern simultaneous Padé
  construction but no forbidden-language numerator theorem:
  <https://doi.org/10.5802/jtnb.914>.
- Bell--Chen, *Power Series with Coefficients from a Finite Set* (2017),
  proves the D-finite/rational dichotomy used in Section 7:
  <https://arxiv.org/abs/1606.04986>.
- Bugeaud, *On the rational approximation to the Thue--Morse--Mahler
  numbers* (2011), proves irrationality exponent two for the decimal
  Thue--Morse value used in (32): <https://doi.org/10.5802/aif.2666>.
- Ortega-Cerdà--Seip, *Multipliers for Entire Functions and an Interpolation
  Problem of Beurling* (1999), characterizes interpolation and sampling in
  Bernstein spaces using density and separation.  The elementary product
  (25) is already a direct non-uniqueness certificate for the present sparse
  nodes: <https://doi.org/10.1006/jfan.1998.3357>.
- Khabibullin, *The Malliavin--Rubel theorem on small entire functions of
  exponential type with given zeros: 60 years later* (2022), surveys and
  strengthens the zero-set/interpolation side; it supplies no mechanism for
  selecting \(p_n\): <https://arxiv.org/abs/2204.11603>.
- Fischler--Rivoal, *Zeros of E-functions and of exponential polynomials
  defined over* \(\overline{\mathbb Q}\) (2025), is the closest current
  primary source on the arithmetic structure of E-function zeros.  Its
  results and conjectures concern factorization, common zeros, and
  multiplicity, not base-expansion disjunctivity:
  <https://arxiv.org/abs/2503.20345>.
- Chow--Varjú--Yu, *Counting rationals and Diophantine approximation in
  missing-digit Cantor sets* (published 2026), proves counting and metric
  approximation results over missing-digit sets.  It does not exclude the
  fixed point \(\pi\): <https://doi.org/10.1016/j.aim.2026.110807>.

Search phrases included combinations of *zeros of E-functions*, *sine and
decimal expansion*, *Padé restricted denominators*, *logarithms of algebraic
numbers and digits*, *regular-language rational approximation*, *entire
interpolation sparse zeros*, *Carlson uniqueness*, and *missing-digit Cantor
sets*.  No primary theorem was found which places a nonzero zero of sine
outside every base-10 one-word survivor set.

## Bottom line

The sine identity does reveal the decimal tail, but it reveals it by an exact
inverse formula: \(x_n=q_n\arcsin(\sin(p_n/q_n))\).  At leading order,
Padé or exponential approximation sees precisely the same tail.  Meanwhile,
the union of all regular-language numerator candidates is so sparse that a
nonzero entire function of order below one can vanish on all of it.  The
finite-state aggregate has a Mahler equation; the selected \(\pi\) path does
not.

Accordingly this branch supplies a sharper obstruction and an exact analytic
reduction, but no complete proof of V1.
