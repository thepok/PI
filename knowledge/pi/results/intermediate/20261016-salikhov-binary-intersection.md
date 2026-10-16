# Salikhov binary family: identified local class and both approximation signs

Date: 2026-10-16. Labels: `proof sketch` and exact finite-state `experiment`.
No Lean verification or novelty claim. This is arithmetic progress on the
intersection gap in the [preceding note](20260906-salikhov-mod5-support.md),
not an admitted decimal-digit candidate and not a resolution of E, CW0, CW9,
or V1.

## Result

Retain the preceding note's rational sequences
\(I_n=a_n+b_n\pi\), \(q_n=2^{2-\lfloor5n/2\rfloor}b_n\),
\(c_n=2^{2-\lfloor5n/2\rfloor}a_n\), and
\[
 Z(n)=\left(q_n\bmod5,\;5^{\lfloor\log_5(4n)\rfloor}c_n\bmod5\right).
\]
Let
\[
 \mathcal F_k=\{2^km:1\le m<2^{k-1},\ m\text{ odd}\},\qquad
 \mathcal F=\bigcup_{k\ge2}\mathcal F_k,\qquad M_k=2^{k-2}.
\]
The union is disjoint because \(v_2(n)=k\) on \(\mathcal F_k\).
Write \(\lambda\) for the root in \((4,5)\) of
\(X^3-4X^2-X+2\), and put
\(\delta=\log_5\lambda\approx0.8804553636<1\).

The following statements are `proof sketch`, with their graph input
exhaustively reproduced by the accompanying `experiment`.

1. Uniformly in positive integers \(a,d,M\) with \(5\nmid d\),
   \[
   \#\{0\le j<M:Z(a+dj)\ne(0,0)\}=O(M^\delta).
   \]
   The constant is independent of the progression's offset and step.
2. Consequently,
   \[
   \#\{n\in\mathcal F\cap[1,N]:Z(n)\ne(0,0)\}
      =O(N^{\delta/2}),\qquad
   \#(\mathcal F\cap[1,N])\asymp\sqrt N.
   \]
   Thus the identified class \(Z=(0,0)\) has relative density one in the
   entire binary family, with exceptional proportion
   \(O(N^{-(1-\delta)/2})\), approximately \(O(N^{-0.0597723})\).
3. There is an increasing sequence \(k_j\to\infty\), computable in
   principle from the algebraic recurrence roots by the selector below,
   on which the
   actual approximation errors \(\varepsilon_n=\pi+a_n/b_n\) satisfy
   \[
   \#\{n\in\mathcal F_{k_j}:Z(n)=(0,0),\ \varepsilon_n>0\}
       =(\tfrac12+o(1))M_{k_j},
   \]
   \[
   \#\{n\in\mathcal F_{k_j}:Z(n)=(0,0),\ \varepsilon_n<0\}
       =(\tfrac12+o(1))M_{k_j}.
   \]
   In particular, both signs occur infinitely often in this same explicitly
   identified local class while the established linear two-adic precision
   survives reduction of the rational approximant.

At \(N_j=2^{2k_j-1}\), the selected block alone also gives
\[
 \#\{n\in\mathcal F\cap[1,N_j]:Z(n)=(0,0),\ \pm\varepsilon_n>0\}
 \ge\left(\frac1{4\sqrt2}+o(1)\right)\sqrt{N_j}
\]
for each sign. This follows from \(M_{k_j}/2=2^{k_j-3}\).

For every one of these indices, write \(-a_n/b_n=P_n/Q_n\) in lowest
terms, with \(Q_n>0\). The preceding all-index arithmetic bound gives
\[
 v_2(P_n)\ge2n-1-2\lfloor\log_2n\rfloor,\qquad Q_n\text{ odd}.
\]
The new argument synchronizes this bound with a known local class and
both actual-pi approximation signs. Neither synchronization was supplied
by the preceding note's pigeonhole observation.

## 1. The absorbing state gives a uniform progression bound

The preceding 145-state full-pair automaton reads base-five digits from
least to most significant. Its exact graph has these three properties:

- the zero state is absorbing;
- an output is \((0,0)\) if and only if the current state is that absorbing
  state; in every other state, the first output coordinate is nonzero;
- appending leading zero digits preserves the output.

The second property is essential. Sparsity of final outputs alone would
not imply sparsity of permissible low-digit prefixes in a general automaton.
Here every nonzero output requires every preceding state to remain live.
The checker verifies these properties at every reachable state and edge,
after reproducing the exact coefficient-section construction.

Let \(R_r\subseteq\mathbb Z/5^r\mathbb Z\) consist of the length-\(r\)
digit strings whose state remains live. By the preceding properties,
\[
 |R_r|=h_r=\#\{0\le n<5^r:Z(n)\ne(0,0)\}.
\]
The auxiliary convention \(Z(0)=(1,0)\) is harmless here. The graph's
componentwise vector identity gives, for every length,
\[
 \sum_{r\ge0}h_rz^r
  =\frac{1-z-z^2}{1-5z+3z^2+3z^3-2z^4},
 \qquad(h_0,h_1,h_2)=(1,4,16).
\]
The denominator factors as
\((1-z)(1-4z-z^2+2z^3)\). The cubic's other characteristic roots lie
in \((-1,0)\) and \((0,1)\), so this exact generating function implies
\(h_r=O(\lambda^r)\). No fitted finite-range growth law is used.

For every nonnegative integer \(n\), absorption gives
\[
 Z(n)\ne(0,0)\ \Longrightarrow\ n\bmod5^r\in R_r.
\]
If \(5\nmid d\), the map \(j\mapsto a+dj\bmod5^r\) is a permutation
over each complete run of \(5^r\) consecutive indices. Each permissible
residue is therefore encountered at most \(\lceil M/5^r\rceil\) times.
This proves the useful exact inequality
\[
 \boxed{\#\{0\le j<M:Z(a+dj)\ne(0,0)\}
       \le h_r\lceil M/5^r\rceil\quad(r\ge0).}
\]
Choose \(r=\lfloor\log_5 M\rfloor\). Then
\(\lceil M/5^r\rceil\le5\) and \(\lambda^r\le M^\delta\), proving
the claimed uniform bound.

## 2. Density one in the binary family

The block \(\mathcal F_k\) is an arithmetic progression with first term
\(2^k\), step \(2^{k+1}\), and length \(M_k=2^{k-2}\). Its step is
coprime to five. Hence
\[
 \#\{n\in\mathcal F_k:Z(n)\ne(0,0)\}=O(M_k^\delta).
\]
This already identifies the zero class in every sufficiently long block.

For the full truncated family the exact block length is
\[
 M_k(N)=\min\left(2^{k-2},
       \left\lfloor\frac{\lfloor N/2^k\rfloor+1}{2}\right\rfloor\right).
\]
Whenever it is nonzero,
\(M_k(N)\le\min(2^{k-2},N/2^k)\). Split the sum over \(k\) at
\(K=\lfloor\tfrac12\log_2N\rfloor\). Two geometric sums give
\[
 \sum_k M_k(N)^\delta
 \le\sum_{k\le K}2^{\delta(k-2)}
       +N^\delta\sum_{k>K}2^{-k\delta}
 =O(N^{\delta/2}).
\]
The same calculation with exponent one gives the upper bound
\(\#(\mathcal F\cap[1,N])=O(\sqrt N)\). All blocks through \(K\)
are complete, and their total size is \(2^{K-1}-1\); this gives the
matching lower bound for sufficiently large \(N\).

## 3. A subsequence of dyadic blocks is phase-equidistributed

The needed fact holds for every irrational \(x\), not just the phase
arising from the Salikhov integral:

> For \(\mathcal F_k\) as above, there is an increasing sequence \(k_j\)
> such that \(\{nx\}:n\in\mathcal F_{k_j}\) is equidistributed modulo one
> as \(j\to\infty\).

This means equidistribution of the finite empirical measures of those
blocks. It does not mean all dyadic blocks have a common limiting law.

First, the doubling orbit \(x_k=\{2^kx\}\) of an irrational \(x\) has
an infinite omega-limit set \(\Omega\). Here is the elementary detail
that prevents a hidden recurrence assumption. If \(\Omega\) were finite,
doubling would permute it. Once the orbit is sufficiently close to this
finite set, separation of its points forces the closest points to follow
that same permutation. The signed circle errors then satisfy
\(e_{k+1}=2e_k\) without wrapping, while remaining bounded for every future
index. Therefore all those errors are zero. The orbit is eventually
periodic, making \(x\) rational, a contradiction. For a singleton
omega-limit the identical expanding-error argument applies directly.

For a fixed integer \(H\), remove the finite resonance set
\[
 E_H=\{t\in\mathbb R/\mathbb Z:\exists\,1\le\ell\le H,
                                            \ 2\ell t\in\mathbb Z\}.
\]
Because \(\Omega\) is infinite, choose \(t_H\in\Omega\setminus E_H\).
Then there are a constant \(\eta_H>0\) and arbitrarily large \(k\) with
\[
 \min_{1\le\ell\le H}\|2\ell x_k\|\ge\eta_H.
\]
There is no assumption that \(\Omega\) contains an irrational point;
that stronger assertion need not hold.

Write \(e(t)=e^{2\pi it}\). Since \(n=2^k(2j+1)\) in the block,
the geometric-sum formula gives
\[
 \left|\frac1{M_k}\sum_{n\in\mathcal F_k}e(\ell nx)\right|
 \le\min\left(1,\frac1{2M_k\|2^{k+1}\ell x\|}\right).
\]
For each \(H\), select an increasing good index \(k_H\) sufficiently
large that \(M_{k_H}\eta_H\ge H\). All the first \(H\) nonzero Fourier
coefficients then have modulus at most \(1/(2H)\). A diagonal argument
and Weyl's criterion prove the asserted block equidistribution.

Deleting \(O(M_k^\delta)=o(M_k)\) nonzero-local-class indices leaves
the same limiting empirical distribution. Thus the subsequence may also
be restricted to \(\mathcal F_{k_j}\cap\{Z=(0,0)\}\).

## 4. Actual-pi signs and surviving reduced numerator precision

The preceding signed-asymptotic argument uses the published integral,
its recurrence, and its actual nonzero pi connection constant to obtain
\[
 \varepsilon_n=K(\rho/\Lambda)^n
       \left(\cos(n\theta+\varphi)+O(1/n)\right),\qquad K>0,
 \qquad \theta/\pi\notin\mathbb Q.
\]
Its proof and precise normalization remain prerequisites of this extension;
the new graph experiment does not independently prove the source integral
or this analytic asymptotic.

Apply the previous section with \(x=\theta/(2\pi)\). For every fixed
\(\eta>0\), sufficiently late selected blocks have the sign of
\(\varepsilon_n\) equal to the sign of the cosine whenever the latter's
absolute value exceeds \(\eta\), since \(\min\mathcal F_k=2^k\to\infty\).
Equidistribution makes the exceptional near-zero-cosine proportion tend to
its circle measure; that measure tends to zero as \(\eta\downarrow0\).
Both half-circle signs therefore have proportions \(1/2+o(1)\), including
after restriction to \(Z=(0,0)\).

### Explicit computable selection of the blocks

The selected indices need not remain merely existential. Let \(\alpha\)
be the root in the upper half-plane of
\[
 108X^3-2359989X^2+138304X-2048,
\]
and put \(\zeta=\alpha/\bar\alpha=e^{2i\theta}\). This is an explicitly
specified algebraic number. Starting with \(k_0=1\), define \(k_j\) to
be the least integer \(k>k_{j-1}\), \(k\ge j+2\), such that
\[
 \boxed{M_k^2\left|1-\zeta^{h2^k}\right|^2>4j^2
                    \quad\text{for every }1\le h\le j.}
\]
The infinite-omega-limit argument above gives arbitrarily large indices
where all these finitely many denominators stay bounded away from zero.
Since \(M_k\to\infty\), the strict test eventually succeeds at each
stage. The block's geometric sums then satisfy
\[
 \left|\frac1{M_k}\sum_{n\in\mathcal F_k}e^{ihn\theta}\right|
 \le\frac2{M_k|1-\zeta^{h2^k}|}<\frac1j
 \qquad(1\le h\le j).
\]
Every test is a decidable real-algebraic comparison: its squared modulus
is \(2-\zeta^{h2^k}-\zeta^{-h2^k}\). Exact algebraic arithmetic therefore
makes the selector computable in principle, with termination proved for
each stage. It uses neither \(\varphi\) nor evaluations of pi's digits.
No useful bound on the search length or computational complexity is supplied.

The surviving two-adic numerator bound was already proved at every index
of \(\mathcal F\), so it automatically holds on these selected positive
and negative subsets. This is the promised synchronization.

## Verification and limits

Run:

```sh
python3 workflows/experiments/salikhov_mod5_support_20260906/salikhov_intersection.py --max-k 18
```

The checker reconstructs the full coefficient-section automaton; certifies
the absorbing-state, output and padding facts at every state; reproduces
the componentwise support-count recurrence; exhausts the residue-occupancy
inequality over every offset and invertible step modulo 125 at six lengths;
and evaluates the exact local pairs on the binary blocks. For example:

| k | Block size | Z=(0,0) | Nonzero local pair |
|---:|---:|---:|---:|
| 10 | 256 | 210 | 46 |
| 14 | 4,096 | 3,696 | 400 |
| 18 | 65,536 | 62,105 | 3,431 |

The finite census illustrates the theorem. It does not establish its
asymptotic, the phase equidistribution, or the actual-pi sign law.

This removes the preceding note's inability to identify a fixed output
class with both signs on the binary family. It does **not** establish a
relative sign law for every \(k\), for the full family at every cutoff,
or inside any of the sixteen nonzero output classes. The dyadic indices
are computable by the explicit selector, but no useful search or complexity
bound is supplied. In particular, it selects the zero
local class, not a five-adic unit class; compatible growing five-adic
precision remains open.

The actual-pi sign input cannot be replaced by an arbitrary constant: for
the explicit word-avoider \(x=4/9=0.444\ldots\),
\(x+a_n/b_n\to x-\pi<0\), so the simultaneous two-sign conclusion
fails. Nevertheless, two-sided rational approximation and two-adic
numerator divisibility do not specify ordered decimal residues. The odd
denominator factors remain uncontrolled, so the three admission tests for
a decimal-digit candidate are not all met. No closed digit route is reopened.

Sources: the preceding repository note and its exact checker at baseline
commit `2ab024737878cd9f1567cc296ef53f051a5ff10b`;
[Zeilberger–Zudilin, Part II](https://arxiv.org/html/1912.06345v2);
the [published recurrence](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
