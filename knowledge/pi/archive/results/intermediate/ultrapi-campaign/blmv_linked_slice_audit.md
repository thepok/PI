# BLMV on the linked decimal/three-primary exponent slice

Audit date: **2026-08-12 UTC**

Status: source statements are `literature-checked`; the deductions below are a
`proof sketch` and are not in the verified Lean track.

Scope: no claim about the actual value of \(\pi\) is proved here.

## 1. Question and normalized slice

For \(j\ge 1\), let \(a_j\) be the unique integer such that

\[
 3^{a_j}\le 12j+3<3^{a_j+1},
 \qquad t_j:=a_j-1.
\]

Thus the exact T52 three-primary factor is \(D_j=3^{t_j}\), with
\(t_j=\log_3 j+O(1)\).  For a fixed integer \(C\), the exponent region relevant
to the current resonance route is

\[
 \mathcal L_C(\alpha)
 =\left\{10^s3^{t_j}\alpha\pmod 1:
     j\ge1,\ j\le s\le3j+C\right\}.                 \tag{1}
\]

The upper endpoint \(3j+C\) represents \(s=j+v\) with
\(0\le v\le2j+O(1)\).  A theorem useful for the present route would have to
control the prescribed horizontal slice \(t=t_j\), preferably within each
\(j\)-block and for the actual point \(\alpha=\pi\).  Density of a surrounding
two-parameter box, or existence of one good exponent \(t\le t_j\), has the
wrong quantifiers.  Pointwise signed cancellation is stronger still and is
not a stated conclusion of any BLMV theorem audited below.

## 2. Primary sources

### BLMV09

J. Bourgain, E. Lindenstrauss, P. Michel, and A. Venkatesh, *Some
effective results for \(\times a\times b\)*, Ergodic Theory and Dynamical
Systems 29 (2009), 1705--1722,
[DOI](https://doi.org/10.1017/S0143385708000898).

Local pinned PDF:
`work/theory/pi-lacunary-near-return-sparsity/library/t86/blmv-2009.pdf`

SHA-256:
`372d251b5c7c4936ab4e6b9cc6fb3af2ded2c8fe81020ad3e467843c20878e3b`.

Exact locators:

- Theorem 1.4, printed p. 1706/PDF p. 2;
- Theorem 1.8, printed p. 1707/PDF p. 3;
- Theorem 3.2, printed p. 1711/PDF p. 7;
- Proposition 3.8 and equations (3.8a)--(3.8c), printed pp. 1713--1714/PDF
  pp. 9--10;
- proof of Theorem 1.4, printed p. 1719/PDF p. 15;
- Proposition 5.2 and its proof, printed pp. 1719--1721/PDF pp. 15--17.

### BFK11

R. Broderick, L. Fishman, and D. Kleinbock, *Schmidt's game, fractals, and
orbits of toral endomorphisms*, Ergodic Theory and Dynamical Systems 31
(2011), 1095--1107,
[arXiv:1001.0318v3](https://arxiv.org/abs/1001.0318v3),
[DOI](https://doi.org/10.1017/S0143385710000374).

Local pinned PDF:
`work/theory/pi-lacunary-near-return-sparsity/library/t116/broderick-fishman-kleinbock-1001.0318v3.pdf`

SHA-256:
`af22faa5bd33c9bf719c0c6fbfdf3c173d35ea7bee71368cffd0da0c0f0c9b36`.

Exact locators:

- Theorem 1.3, printed p. 3;
- Proposition 3.1, printed p. 7;
- Theorem 4.1 and its proof, printed pp. 8--9.

Only these primary papers are used for the applicability verdict.

## 3. What BLMV actually quantifies

Set \(a=10\), \(b=3\).

BLMV Theorem 1.8 says that, if \(\alpha\) is irrational and there is a fixed
\(k\) with

\[
 |\alpha-p/q|\ge q^{-k}\quad(q\ge2),                \tag{2}
\]

then the full exponent square

\[
 \{10^s3^t\alpha:0\le s,t\le X\}                  \tag{3}
\]

is \((\log\log X)^{-\kappa_6}\)-dense for all sufficiently large \(X\).
The selected pair \((s,t)\) may be anywhere in the square.  There is no
subsequence clause, no prescribed relation between \(s\) and \(t\), no count
of visits, and no signed character-sum estimate.

BLMV Theorem 1.4 starts from a measure satisfying

\[
 H_\mu(\mathcal P^X)\ge\rho\log X                  \tag{4}
\]

and produces one multiplier \(m=10^s3^t<X\).  Although the numerical cutoff
implies \(t<\log_3X\), it does not concentrate \(t\) near \(\log_3\log X\).
For the numerical size of (1), \(X\) is roughly \(10^{3j}\) up to a
polynomial factor, so the theorem permits \(t=\Theta(j)\), whereas the required
exponent is \(t_j=\Theta(\log j)\).

The relatively-prime refinement, Theorem 3.2, is the closest statement.  Its
parameters obey

\[
 {10\over\log_{10}T}\le\delta\le{\rho\over20},
 \qquad
 10^{20/\delta}\le T\le {\delta\over4}\log_3X,     \tag{5}
\]

and its conclusion selects

\[
 0\le s\le(1-\delta)\log_{10}X,
 \qquad 0\le t\le T.                              \tag{6}
\]

Pre-pushing the input measure by \(10^j3^L\) translates this to the rectangle

\[
 j\le s_{\rm total}\le j+(1-\delta)\log_{10}X,
 \qquad L\le t_{\rm total}\le L+T.                \tag{7}
\]

Consequently one can put the decimal coordinate inside \([j,3j]\), and by
taking \(L=t_j-T\), put the three-adic coordinate in a strip ending at
\(t_j\).  The theorem still returns an unspecified member of that strip, not
its endpoint \(t_j\).  Conditions (5) prohibit taking \(T=0\), or even taking
it small relative to the source constants.

## 4. Why the proof cannot be reindexed onto the endpoint

The selector in Proposition 3.8 does not hide a fixed-exponent conclusion.
The proof puts

\[
 \ell=\lfloor\log_{10}T\rfloor
\]

and lets \(T_0\) be the order of \(3\) in
\((\mathbb Z/10^\ell\mathbb Z)^\times\).  Lemma 3.5 averages over the whole
cycle \(0\le t<T_0\); equation (3.8c) then proves that at least one member of
that cycle is good.  The entropy-selected decimal shift \(s\) is also
existential.

At Fourier frequency \(\xi\), the source orthogonality controls an average of
terms of the form

\[
       |\widehat\nu(\xi3^t)|^2.                   \tag{8}
\]

Trying to compensate an output \(t<t_j\) by changing the test frequency to
\(\xi_t=3^{t_j-t}\) destroys the exact mechanism: every term becomes

\[
       |\widehat\nu(\xi_t3^t)|^2
       =|\widehat\nu(3^{t_j})|^2.                 \tag{9}
\]

The character no longer varies around the multiplicative subgroup, so the
orthogonality in equations (3.5a)--(3.5b) supplies no saving.  Thus a bounded
offset cannot be absorbed into a varying harmonic while retaining the BLMV
estimate.  This is a proof-level, not merely statement-level, obstruction.

## 5. A sharp entropy obstruction for the actual selected grids

Let \(\mu_j\) be uniform on a \(D_j\)-point selected grid, where
\(D_j=3^{t_j}\).  For every partition,

\[
 H_{\mu_j}(\mathcal P^X)\le\log D_j.              \tag{10}
\]

Suppose Theorem 3.2 could reach the required exponent without a preliminary
three-adic collapse.  Then \(T\ge t_j\).  Its upper bound in (5) gives

\[
 \log X\ge {4\over\delta}\,t_j\log3
          ={4\over\delta}\log D_j.               \tag{11}
\]

Combining (4), (10), and (11) yields \(\rho\le\delta/4\).  But (5) also
requires \(\rho\ge20\delta\).  These inequalities are incompatible for every
\(\delta>0\).  Therefore Theorem 3.2 cannot be applied to the uniform
three-primary grid at parameters that reach \(t_j\).

Pre-pushing that grid by \(3^{t_j-T}\) does not evade the obstruction.  The
map collapses its \(D_j=3^{t_j}\) points to at most \(3^T\) points, removing
the growing entropy that was supposed to drive the theorem.

There is a parallel obstruction for an empirical actual-orbit measure on the
\(O(j)\) points \(10^{j+v}\pi\), \(0\le v\le2j+O(1)\).  At the natural
decimal resolution \(X=10^{\Theta(j)}\), its entropy is at most \(O(\log j)\),
so necessarily \(\rho=O(\log j/j)\).  The lower two inequalities in (5) then
force

\[
 T\ge10^{\Omega(j/\log j)},                       \tag{12}
\]

while the upper inequality forces \(T=O(\log j)\).  Hence even maximal
cardinality of the empirical orbit cannot meet the BLMV parameter window at
the required cylinder resolution.  Missing a word supplies no additional
lower entropy for the one actual orbit.

## 6. The missing-word maximal-entropy support does not select \(\pi\)

For a nonempty forbidden word \(w\), choose one digit \(d\) occurring in
\(w\), and put the uniform Bernoulli measure on the other nine decimal
digits.  Its circle image is \(\times10\)-invariant, is supported on the
word-avoidance set, and has entropy \(\log9\).  Thus it supplies the positive
entropy needed by Theorem 3.2.

For this measure, however, the selected decimal multiplier disappears:
\(10^s.\mu=\mu\).  The conclusion merely says that for some \(t\) in the
allowed range, some point of \(3^t\operatorname{supp}\mu\) reaches the test
interval.  It does not say that \(3^t10^s\pi\) does so.  If \(\pi\) avoided
\(w\), the point mass \(\delta_\pi\) would have zero entropy, and no known
argument upgrades it to this Bernoulli measure.  A growing finite union of
sets \(3^tK_w\) may be dense at the tested coarse scale while every statement
about the selected actual path remains open.  The support argument is
therefore tautological for the present purpose.

## 7. Countermodel: the linked multiplier set is itself lacunary

There is a stronger quantifier obstruction.  It shows that Theorem 1.8 cannot
be inherited by the linked slice even for a Diophantine-generic point which
itself omits a decimal digit.

For an integer \(s\), the indices contributing to (1) satisfy

\[
 \left\lceil{s-C\over3}\right\rceil\le j\le s.    \tag{13}
\]

The function \(t_j\) is nondecreasing.  For all sufficiently large \(s\),

\[
 {12s+3\over
  12\lceil(s-C)/3\rceil+3}<9.                    \tag{14}
\]

If the largest and smallest \(a_j\) in (13) differed by at least three, the
ratio of the corresponding values \(12j+3\) would be strictly greater than
nine, contradicting (14).  Hence, for a fixed large \(s\), the possible
values of \(t_j\) span at most two integers.  The least possible \(t_j\) is
nondecreasing with \(s\).

Take two distinct linked multipliers \(10^{s_1}3^{u_1}\) and
\(10^{s_2}3^{u_2}\), with \(s_2>s_1\).  The preceding facts give
\(u_2-u_1\ge-2\), and therefore

\[
 {10^{s_2}3^{u_2}\over10^{s_1}3^{u_1}}
 \ge {10\over9}>1.                               \tag{15}
\]

At equal \(s\), distinct multipliers have ratio at least three.  Unique
factorization rules out duplicates with different exponent pairs.  The
finitely many terms before (14) have a positive minimum adjacent ratio.
Thus, after arranging the distinct multipliers in increasing order
\(M_1<M_2<\cdots\),

\[
             \inf_k {M_{k+1}\over M_k}>1.         \tag{16}
\]

So the entire linked region, despite containing \(O(j)\) labels at stage
\(j\), is a Hadamard-lacunary multiplier sequence.

Fix a target \(y\in\mathbb R/\mathbb Z\).  Apply BFK Theorem 1.3 (equivalently
Theorem 4.1) to the one-by-one matrices \([M_k]\) and uniformly discrete
targets \(Z_k=y+\mathbb Z\).  It gives a winning set of \(\alpha\) satisfying

\[
       \inf_k d(M_k\alpha,y+\mathbb Z)>0.         \tag{17}
\]

One may play the game on the standard deleted-digit Cantor set \(K_d\).  Its
uniform self-similar measure satisfies a power law, hence is absolutely
decaying and Federer in dimension one; BFK Proposition 3.1 then gives
positive (indeed full relative) Hausdorff dimension for the intersection.
The Liouville numbers have Hausdorff dimension zero: for each \(K>2\), cover
the infinitely-often inequalities
\(|x-p/q|<q^{-K}\) by \(O(q)\) intervals of length \(O(q^{-K})\), and let
\(K\to\infty\).  We may consequently choose an irrational
\(\alpha\in K_d\) satisfying (17) which is not Liouville.  Increasing a finite
Diophantine exponent if necessary makes this \(\alpha\) satisfy (2).

For that same \(\alpha\):

1. its decimal expansion omits \(d\);
2. BLMV Theorem 1.8 makes its full \(\times10,\times3\) orbit effectively
   dense;
3. every point of the linked slice (1) avoids one fixed open neighborhood of
   \(y\).

In particular the linked slice is not dense and misses a decimal cylinder
contained in that neighborhood.  This is a countermodel to any attempted
logical reparameterization of BLMV's full-box conclusion onto (1).  It does
not assert that \(\pi\) is such a point; it proves that the BLMV hypotheses
alone cannot distinguish \(\pi\) from such points.

## 8. Applicability verdict

| candidate input | exact useful output | first fatal mismatch | verdict |
|---|---|---|---|
| BLMV Theorem 1.8 | density in the full square \(0\le s,t\le X\) | prescribed lacunary slice can avoid an open arc for a Diophantine-generic point | **DOES NOT APPLY** |
| BLMV Theorem 1.4 | one multiplier \(10^s3^t<X\) from a positive-entropy measure | no lower bound or prescribed value of \(t\); no pointwise signed sum | **DOES NOT APPLY** |
| BLMV Theorem 3.2 | one \((s,t)\) in an alignable rectangle | subgroup average selects an unspecified \(t\); grid and empirical-orbit entropy parameters are incompatible | **DOES NOT APPLY** |
| missing-word invariant measure | positive entropy supported on avoiders | selects some support point, not the actual \(\pi\) path | **DOES NOT APPLY** |

The narrow positive finding is that Theorem 3.2 can align its *decimal*
coordinate and can localize the three-adic coordinate to a translated strip.
Its proof has no mechanism to select the boundary \(t=t_j\), and the exact
measures arising from the current Machin grids cannot satisfy its parameter
window.  The BFK countermodel shows this is a genuine quantifier boundary,
not merely a missing manipulation of BLMV's notation.
