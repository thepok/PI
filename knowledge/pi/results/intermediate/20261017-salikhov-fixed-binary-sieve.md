# A fixed binary progression with an explicit sparse exception sieve

Date: 2026-10-17. Labels: proof sketch and exact experiment.
No Lean verification or priority claim.

An exact coefficient expansion controls three consecutive original
Salikhov multipliers on a fixed binary progression, after deleting an
explicit sparse union of residue classes. The deletion estimate is
uniform inside the short low-digit progressions used in the
positive-density application. The full consecutive-index argument is
included below.

Keep the actual modified Salikhov normalization

\[
 I_n=a_n+b_n\pi,\qquad
 q_n=2^{2-\lfloor5n/2\rfloor}b_n,\qquad
 c_n=2^{2-\lfloor5n/2\rfloor}a_n,\qquad
 -a_n/b_n=P_n/Q_n,
\]

where the last pair is reduced and \(Q_n>0\). The
[local-pair note](20260906-salikhov-mod5-support.md) proves the
integrality of \(q_n\), positivity of \(b_n\), and the companion
bound used in the reduction below. Write \(s_2\) for binary digit sum.

## 1. The fixed progression and its exceptional classes

For a positive integer \(m\equiv31\pmod{64}\), put

\[
 t=32m,\qquad w=s_2(3m).
\]

Define

\[
 \mathcal E=
 \bigcup_{a=33,97,161,\ldots}
 \{m\ge1:m\equiv-a\pmod{2^{32a-7}}\}.
 \tag{1}
\]

Every residue class in this union is contained in
\(m\equiv31\pmod{64}\). The first class has modulus
\(2^{1049}\); the exponents of the subsequent moduli increase by
\(2048\).

For every \(m\equiv31\pmod{64}\) outside \(\mathcal E\), with
no height restriction, the three original multipliers satisfy

\[
 \boxed{
 v_2(q_{64m-3})=w+2,\qquad
 v_2(q_{64m-2})=w,\qquad
 v_2(q_{64m-1})=w.
 }
 \tag{2}
\]

Consequently, at all three indices \(n\),

\[
 \boxed{
 Q_n\text{ is odd},\qquad
 v_2(P_n)\ge2n-1-2\lfloor\log_2n\rfloor.
 }
 \tag{3}
\]

Membership in \(\mathcal E\) does not assert that (2) fails. These
classes are a sufficient deletion set for the proof below.

### 1.1. Literal all-index extraction and shell normalization

We use the all-index extraction in the
[odd-multiplier note, pinned at PR #14's head](https://github.com/thepok/PI/blob/8aac5e0c13e7e3b08ef44f71754e00c27e69a1a7/knowledge/pi/results/intermediate/20261017-salikhov-odd-multiplier.md#exact-finite-precision-evaluator).
The formula and the needed derivation are included here, so this note
and its audit do not require a checkout of that branch. For every
\(n\ge1\),
\[
 q_n=2^{-\lfloor5n/2\rfloor}[z^{3n}]
 (1+z)^{n-1/2}(32+56z+25z^2)^{2n}.
 \tag{4a}
\]
Indeed, in the source rational integrand
\[
 {\cal R}_n(x)=
 \frac{5x^{2n}(x^4+6x^2+25)^{2n}}{(25-x^2)^{3n+1}},
\]
the local change \(x=5\sqrt{1+z}\) at \(x=5\) gives
\[
 {\cal R}_n(x)\,dx
 =\frac{(-1)^{n+1}}2\,
 z^{-3n-1}(1+z)^{n-1/2}(32+56z+25z^2)^{2n}\,dz.
\]
Its residue is \(-A_{n,0}\), whereas the source normalization is
\(b_n=(-1)^nA_{n,0}/2\). Equating residues gives (4a).

For any integer \(n\) and integer \(h\ge0\), define
\[
 u_{n,h}=
 \frac{\prod_{i=0}^{h-1}(2n-1-2i)}{h!/2^{v_2(h!)}}.
 \tag{4b}
\]
The empty product is one. The numerator factors and denominator are
odd and nonzero, including for negative \(n\); hence \(u_{n,h}\)
is a rational two-adic unit. Legendre's factorial formula gives
\[
 \binom{n-1/2}{h}=2^{-2h+s_2(h)}u_{n,h}.
\]
In (4a), group the polynomial factors by the number \(s\) choosing
a constant or linear term, and then by the number \(b\) choosing
the linear term. The remaining binomial-series index is
\(h=2s-b-n\). The literal resulting expansion is
\[
 q_n=\sum_{s=\lceil n/2\rceil}^{2n}
 \binom{2n}{s}25^{2n-s}
 \sum_{b=0}^{\min(s,2s-n)}
 \binom{s}{b}7^b
 2^{s-\lfloor n/2\rfloor+s_2(2s-n-b)}u_{n,2s-n-b}.
 \tag{4c}
\]

Now let \(j\ge5\), \(t=2^jm\) with \(m\equiv31\pmod{64}\),
and \(w=s_2(3m)\). For \(R\in\{1,2,3\}\), put
\(n=2t-R\), \(A=\lceil R/2\rceil\), and \(s=t+k\). Then
\[
 q_n=\sum_{k=-\lfloor R/2\rfloor}^{3t-2R}
 \binom{4t-2R}{t+k}25^{3t-2R-k}T_{R,k}(t),
 \tag{4d}
\]
where
\[
 T_{R,k}(t)=
 \sum_{b=0}^{\min(t+k,2k+R)}
 \binom{t+k}{b}7^b
 2^{k+A+s_2(2k+R-b)}u_{2t-R,2k+R-b}.
 \tag{4e}
\]
Every term of the inner sum has valuation at least \(k+A\).
The power of 25 is a two-adic unit. These formulas include the even
offset \(R=2\).

### 1.2. The unique leading shell and every bounded competitor

Binary factorial valuations give
\[
 v_2\binom{4t}{t}=w,\qquad
 v_2\binom{4t-2R}{t}=w-2.
 \tag{4f}
\]
For the second equality, the ratio to the first binomial is
\[
 \frac34\,
 \frac{\prod_{i=1}^{2R-1}(3t-i)}
      {\prod_{i=1}^{2R-1}(4t-i)}.
\]
Each nonzero fixed offset has valuation below \(j\), so its
valuation is unchanged when subtracted from \(3t\) or \(4t\).
The same argument gives, for \(0\le k\le4\),
\[
 v_2\binom{4t-2R}{t+k}-w
 =-2+v_2\binom{2R+k-1}{k}.
 \tag{4g}
\]
All fixed offsets here are at most \(2R+k-1\le9<2^j\).

For these nonnegative \(k\), define \(T_{R,k}(0)\) by substituting
\(t=0\) in (4e), using (4b) at \(n=-R\). Equivalently, retain
\(0\le b\le k\); the terms with \(b>k\) vanish. Put \(H=2k+R\).
Vandermonde's identity gives, for \(b\ge1\),
\[
 \binom{t+k}{b}-\binom{k}{b}
 =\sum_{i=1}^{b}\binom{t}{i}\binom{k}{b-i},\qquad
 v_2\binom{t}{i}\ge j-v_2(i).
\]
Thus this difference has valuation at least
\(j-\lfloor\log_2 b\rfloor\). In addition,
\[
 v_2(u_{2t-R,h}-u_{-R,h})\ge j+2,
\]
because each numerator factor in (4b) changes by \(4t\) and the
denominator is odd. Extend both sums to \(b=0,\ldots,H\), with
the zero binomial coefficients understood. Applying these bounds
term by term proves
\[
 v_2(T_{R,k}(t)-T_{R,k}(0))
 \ge j-\lfloor\log_2 H\rfloor+k+A.
 \tag{4h}
\]
For \(b=0\), the stronger bound for the unit difference suffices.

Only five exact inner values are needed:

| \(R\) | \(k\) | \(T_{R,k}(0)\) | \(v_2(T_{R,k}(0))\) | Lower bound in (4h) at \(j=5\) |
|---|---|---:|---:|---:|
| 1 | 0 | \(-12\) | 2 | 6 |
| 2 | 0 | \(140\) | 2 | 5 |
| 3 | 0 | \(-3696\) | 4 | 6 |
| 3 | 1 | \(48048\) | 4 | 6 |
| 3 | 2 | \(-247104\) | 6 | 7 |

These are finite rational evaluations of (4b) and (4e), checked
exactly by the audit. Each substitution bound is strictly larger
than the listed valuation. Equations (4f)--(4h) show that the
\(k=0\) shell has valuation \(w,w,w+2\), respectively for
\(R=1,2,3\).

For \(R=1\), the crude lower bounds from (4e) and (4g) at
\(k=1,2,3,4\), after subtracting \(w\), are \(1,1,4,3\).
For \(R=2\), they are \(2,2,4,3\).
For \(R=3\), the exact \(k=1,2\) valuations are \(w+3,w+4\),
and the crude \(k=3,4\) bounds are \(w+6,w+5\).
All exceed the corresponding leader.

The only negative shell is \(k=-1\), for \(R=2,3\). Its outer
binomial is the anchor in (4f) multiplied by
\(t/(3t-2R+1)\), giving valuation \(w+j-2\).
Its inner valuation is at least \(0\) for \(R=2\) and at least
\(1\) for \(R=3\). Both exceed the leader for \(j\ge5\).

### 1.3. The interval bound controls all remaining shells

For \(k\ge1\) in the allowed shell range, the ratio to the anchor is
\[
 \frac{\binom{4t-2R}{t+k}}{\binom{4t-2R}{t}}
 =\prod_{i=1}^{k}\frac{3t-2R-i+1}{t+i}.
\]
Both products range over positive integer intervals of length \(k\).
At every power of two, the count of multiples in the numerator
interval is at least the denominator count minus one. If
\(M_k=\max_{1\le i\le k}v_2(t+i)\), the denominator contributes
no multiples at levels above \(M_k\). Summing the level counts
therefore loses at most \(M_k\), giving
\(v_2\binom{4t-2R}{t+k}\ge w-2-M_k\).
Together with (4e), this proves, for every \(k\ge5\),

\[
 v_2(\text{shell }k)\ge w+k+A-2-M_k,
 \qquad
 M_k=\max_{1\le i\le k}v_2(t+i).
 \tag{4}
\]

No bound on the index height has been used. With \(d=2^j\),
if \(5\le k<d\), then \(M_k=\lfloor\log_2k\rfloor\), so
\(k-2-M_k\ge1\). If \(d\le k\le3d+1\), the only indices
\(i\) divisible by \(d\) are \(d,2d,3d\); the respective
valuations of \(m+1,m+2,m+3\) are \(5,0,1\). Consequently
\(M_k\le j+5\) and
\(k-2-M_k\ge d-j-7\ge1\).

In particular, at the fixed value \(j=5\), every shell through
\(k=97\) is already above the leader, except for the unique
\(k=0\) shell identified above. It remains to treat \(k\ge98\).

We show that

\[
 M_k\le k-3\qquad(k\ge98)
 \tag{5}
\]

whenever \(m\notin\mathcal E\). Suppose otherwise. Some
\(1\le i\le k\) has \(v_2(t+i)\ge k-2\). If \(32\nmid i\),
then \(v_2(t+i)=v_2(i)<5\), which contradicts \(k-2\ge96\).
Hence \(i=32a\) for a positive integer \(a\), and

\[
 v_2(m+a)\ge k-7
 \ge\max\{98,32a\}-7.
 \tag{6}
\]

The cases \(a=1,2,3\) are impossible, since
\(m\equiv31\pmod{64}\) gives their valuations exactly
\(5,0,1\). For \(a\ge4\), (6) gives

\[
 v_2(m+a)\ge32a-7\ge121.
\]

In particular \(m+a\equiv0\pmod{64}\), so
\(a\equiv33\pmod{64}\). This is one of the classes in (1), a
contradiction. Thus (5) holds. Every remaining shell in (4) lies at
valuation at least \(w+A+1\), strictly above the appropriate
leader. This proves (2).

### 1.4. Precision after reducing the rational approximant

For any of the three indices, put \(h=\lfloor\log_2n\rfloor\).
Since \(n=64m-R<2^{h+1}\) and \(1\le R\le3\),
\(m<2^{h-5}+1\). The integer \(m\) is odd while \(2^{h-5}\)
is even, so \(m<2^{h-5}\), giving \(w=s_2(3m)\le h-3\).
Thus (2) implies \(v_2(q_n)\le h\). The source companion bound is
\[
 v_2(c_n)\ge2n+1-\lfloor\log_2(4n+1)\rfloor
 =2n-1-h,
\]
where the floor identity holds for every positive integer \(n\).
As \(n\ge1981\), the difference \(2n-1-2h\) is positive.
Reduction of \(-c_n/q_n=P_n/Q_n\) therefore gives
\(v_2(Q_n)=0\) and
\(v_2(P_n)=v_2(c_n)-v_2(q_n)\ge2n-1-2h\), proving (3).

## 2. Uniform counting inside each low-digit progression

Put

\[
 \Delta=\sum_{a=33,97,161,\ldots}2^{-(32a-13)}
 =\frac{2^{-1043}}{1-2^{-2048}}<2^{-1042}.
 \tag{7}
\]

Let \(m_0\equiv31\pmod{64}\), let \(K\ge1\), and suppose
all \(K\) integers

\[
 m_u=m_0+8000u,\qquad0\le u<K,
 \tag{8}
\]

are positive and at most a real number \(Y\ge1\). Then

\[
 \boxed{
 \#\{0\le u<K:m_u\in\mathcal E\}
 \le\Delta K+J(Y),\qquad
 J(Y)=1+\lfloor\log_2(2Y)\rfloor.
 }
 \tag{9}
\]

The constants and the error term are independent of \(m_0\).

To prove this, fix a possible \(a\) in (1). Since
\(8000=64\cdot125\), division of its congruence by \(64\)
gives

\[
 \frac{m_0+a}{64}+125u
 \equiv0\pmod{2^{32a-13}}.
 \tag{10}
\]

The integer 125 is invertible modulo that power of two, so this is
exactly one residue class in \(u\), containing at most
\(K/2^{32a-13}+1\) members of the interval in (8).

Only \(O(\log Y)\) choices of \(a\) can meet the interval. In
fact \(2^{32a-7}>2a\) for every \(a\ge33\). If
\(2^{32a-7}\mid m_u+a\), positivity gives
\(m_u+a\ge2^{32a-7}>2a\), whence \(a<m_u\le Y\) and
\(m_u+a<2Y\). Therefore

\[
 32a-7\le\lfloor\log_2(2Y)\rfloor.
 \tag{11}
\]

In particular the number of possible choices is at most \(J(Y)\).
Summing their main terms, even over all \(a\) in (1), gives
\(\Delta K\); summing the unit errors proves (9).

For comparison, the same argument in the unconditioned interval
\(1\le m\le Y\) gives

\[
 \#(\mathcal E\cap[1,Y])
 \le\frac{2^{-1049}}{1-2^{-2048}}Y+J(Y).
 \tag{12}
\]

## 3. Application to a free block of base-five digits

The fixed binary base progression is

\[
 n\equiv1981\pmod{4096},\qquad n=64m-3.
 \tag{13}
\]

For an index family \(n=n_0+125U\), restricting (13) puts
\(U\) in one residue class modulo \(4096\). Consecutive
retained values of \(n\) differ by \(125\cdot4096\), so their
corresponding \(m\)'s differ by 8000 exactly, as in (8).

At a base-five height \(L\), reserve
\(k=\lceil2\log_5 L\rceil\) unrestricted low digits. For each
fixed choice of all higher digits, the retained low progression has

\[
 K=\frac{5^k}{4096}+O(1)\asymp L^2.
 \tag{14}
\]

Its indices, and hence its \(m\)'s, are bounded by \(5^L\).
Taking \(Y=5^L\) in (9) gives

\[
 \frac{\#\{\text{deleted low choices}\}}K
 \le\Delta+O(1/L),
 \tag{15}
\]

uniformly over all higher digits. Thus any two fixed phase intervals
that each occupy more than \(2/5\) of the retained low progression
still each occupy at least \(K/3\) after deletion, once \(L\) is
large. The phase distribution itself is a separate analytic input;
(15) only bounds the arithmetic deletion.

This fixed-modulus sieve supplies an input to a positive-density
population argument. It proves no ordered decimal residue, prescribed
word, or V1 conclusion.

## 4. Exact audit

The [self-contained audit](../../../../workflows/experiments/salikhov_fixed_binary_sieve_20261017/audit.py)
checks the five exact inner identities, thirty substitution comparisons,
and 102 short-shell comparisons, including integers with 1,049 binary
digits. It independently compares the original partial-fraction
coefficient with the root-coordinate coefficient at every index from
zero through twelve. It also checks the interval-valuation lower bound,
the logical passage from a failing shell to an explicit exceptional
residue, and the congruence/counting normalization in (10). It imports
only the Python standard library.
The deterministic [certificate](../../../../workflows/experiments/salikhov_fixed_binary_sieve_20261017/certificate.json)
records 13,854 outer-interval valuation bounds, 220,296 tail checks,
6,390 local-congruence comparisons, and the other stated finite
identities. Twelve sampled failing tail bounds are successfully
classified; the largest tested integer has 5,147 binary digits.

From the repository root:

    python3 workflows/experiments/salikhov_fixed_binary_sieve_20261017/audit.py --json workflows/experiments/salikhov_fixed_binary_sieve_20261017/certificate.json

These tests verify the stated finite identities. The all-shell proof
and the geometric-series estimate establish the unbounded result.
