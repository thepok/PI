# Moving-mesh collision control implies Haar block limits

Status: `proof sketch`

Audited: 2026-08-23 UTC

## Statement

Let \(x_n\in\mathbb T=\mathbb R/\mathbb Z\), let \(Sx=10x\), and let
\(L_j,q_j\to\infty\).  On the block \([L_j,2L_j)\), write

\[
 \mu_j={1\over L_j}\sum_{n=L_j}^{2L_j-1}\delta_{x_n},\qquad
 n_j(a)=\#\{n:x_n\in[a/q_j,(a+1)/q_j)\}.
\]

Assume \(\sup_j q_j/L_j<\infty\),

\[
 \sum_{a<q_j}n_j(a)^2\le
 C\left({L_j^2\over q_j}+L_j\right),
 \tag{1}
\]

and the averaged pseudo-orbit defect tends to zero:

\[
 {1\over L_j}\sum_{n=L_j}^{2L_j-1}
 d_{\mathbb T}(x_{n+1},Sx_n)\longrightarrow0.
 \tag{2}
\]

Then \(\mu_j\) converges weakly to Haar measure on \(\mathbb T\).  Consequently,
every fixed open interval, and in particular the interior of every fixed
base-ten cylinder, meets every sufficiently late selected block.

Neither decimal-power meshes nor nested partitions are needed.  The statement
is generic and conditional; (1) has not been proved for the sampled BBP orbit
or the decimal orbit of \(\pi\).

## Proof sketch

Let \(g_j\) be constant with value \(q_j\mu_j(I_{j,a})\) on the equal cell
\(I_{j,a}=[a/q_j,(a+1)/q_j)\).  Then

\[
 \|g_j\|_2^2=q_j\sum_a\mu_j(I_{j,a})^2
 \le C(1+q_j/L_j).
\]

For every continuous \(\varphi\), coupling each atom to its cell gives

\[
 \left|\int\varphi g_j\,dx-\int\varphi\,d\mu_j\right|
 \le\omega_\varphi(1/q_j).
\]

Thus every weak subsequential limit of \(\mu_j\) has an \(L^2\) density.
Condition (2), uniform continuity, and the two block endpoints imply that each
such limit is \(S\)-invariant.  If \(d\mu=f\,dx\), invariance gives
\(\widehat f(h)=\widehat f(10h)\).  Since \(\widehat f\in\ell^2(\mathbb Z)\),
every nonzero Fourier coefficient vanishes along its infinite times-ten ray;
hence \(f=1\) almost everywhere.  Compactness then upgrades the unique
subsequential limit to \(\mu_j\Rightarrow dx\).  Portmanteau applied to the
open interior of a fixed cylinder makes its block occupancy eventually
positive.

The displayed hypotheses apply to every selected block, so the conclusion is
convergence of the full selected sequence.  If instead (1) is known only as a
liminf statement, one must first choose an unbounded subsequence with one
slightly enlarged common constant; only that good subsequence is then covered.
It is still sufficient for arbitrarily late open-cell hits.

## Claim boundary and direction

This supplies an exact consumer for a moving-mesh collision estimate; it does
not supply that estimate.  For the sampled BBP orbit, expanding (1) leads back
to the archived Fejér/self-return and long-lag collision frontier.  Those
terms contain the solution-scale arithmetic difficulty, so this note must not
be cited as a new route around that frontier or as progress on the missing
fixed-\(\pi\) premise.  No quantitative convergence rate is claimed.

V1 remains open.

## Provenance and review

- ChatGPT Pro creative-direction answer SHA-256:
  `751a379da6ff53f75a3ababfdd60b88142660c8b9203f2a66bf5250e6f124434`.
- Sandboxed Ox/OxZen audit wave:
  `workflows/state/runs/odc-haar-consumer-wave-a-20260823`; 15 of 16 calls
  delivered contract-valid memos, while one OpenRouter referee call had a
  delivery failure.  Sandbox image SHA-256:
  `458e58fafe9c54b5a93f3d03ee57047cbdeb8c69b8884eb0ff543ed07a1bf400`.
- Wave results-ledger SHA-256:
  `b105835c7a503ae8dccc793dd6f5f71870a53272f34c6427929854d5ff09affb`.
- Independent integration and direction reviews retained only the theorem
  above.  They rejected unnecessary decimal-refinement assumptions,
  unsupported quantitative claims, and the proposed Fejér successor as a
  duplicate of the archived long-lag frontier.
