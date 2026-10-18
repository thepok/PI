# An elementary square-root tail for the Salikhov digit score

Date: 2026-10-17. Labels: proof sketch and exact experiment.
No Lean verification or priority claim.

The [refined contour bound](20261017-salikhov-shifted-contour-kummer.md)
assigns the six base-five interval states the score

\[
 g=(0,0,1,-1,0,0).
\]

This note proves that a fixed positive fraction of all digit words
has score of square-root size. An explicit reflection then turns
those words into positive-score paths that return to state 1.
The estimate holds for every word length and uses only rational
conditional moments and Cauchy--Schwarz.

## Result

Start at state 0, append \(N\ge1\) independent uniform base-five
digits, and let \(X_t\) be the state after \(t\) digits. Put

\[
 S_N=\sum_{t=1}^N g(X_t).
\]

Then

\[
 \boxed{
 \mathbb P\left(|S_N|\ge\frac{\sqrt N}{4}\right)
 \ge\frac1{32}.
 }
 \tag{1}
\]

Equivalently, at least \(5^N/32\) distinct \(N\)-digit words
have the stated score magnitude. There is an explicit injection
from these words into \((N+4)\)-digit words that, from any
initial state, return to state 1 with score at least

\[
 \boxed{\frac{\sqrt N}{4}+1.}
 \tag{2}
\]

The score theorem itself is independent of \(\pi\). Its role
in the subsequent arithmetic application is to supply many
indices to the actual Salikhov contour inequality. Actual error
signs and simultaneous reduced prime precision require the
separate arithmetic and phase arguments.

## 1. The exact state map and one-step moments

Use the six open subintervals

\[
 (0,\tfrac14),\quad(\tfrac14,\tfrac13),\quad
 (\tfrac13,\tfrac12),\quad(\tfrac12,\tfrac23),\quad
 (\tfrac23,\tfrac34),\quad(\tfrac34,1),
\]

and number them from 0 through 5. Appending a new high base-five
digit \(a\) sends \(x\) to \((x+a)/5\). Direct comparison of
the rational interval endpoints shows that each of the thirty
images lies wholly inside one listed interval. This defines the
following transition table; the exact audit checks all thirty
endpoint inclusions.

| State | Digit 0 | Digit 1 | Digit 2 | Digit 3 | Digit 4 |
|---|---:|---:|---:|---:|---:|
| 0 | 0 | 0 | 2 | 3 | 5 |
| 1 | 0 | 1 | 2 | 3 | 5 |
| 2 | 0 | 1 | 2 | 4 | 5 |
| 3 | 0 | 1 | 3 | 4 | 5 |
| 4 | 0 | 2 | 3 | 4 | 5 |
| 5 | 0 | 2 | 3 | 5 | 5 |

Writing \(P\) for the transition operator, direct averaging gives

\[
 Pg=\frac15g.
 \tag{3}
\]

Let \(\mathcal F_t\) record the first \(t\) digits and define

\[
 D_t=\frac{5g(X_t)-g(X_{t-1})}{4},\qquad
 M_N=\sum_{t=1}^N D_t.
 \tag{4}
\]

Equation (3) implies
\(\mathbb E(D_t\mid\mathcal F_{t-1})=0\), so \(M_N\) is a
martingale. Telescoping gives

\[
 M_N=S_N+\frac{g(X_N)-g(X_0)}4
     =S_N+\frac{g(X_N)}4,
 \qquad |S_N-M_N|\le\frac14.
 \tag{5}
\]

Every conditional increment distribution depends only on the
current value \(z=g(X_{t-1})\), not on the full state:

| \(z\) | Distribution of \(D_t\) |
|---|---|
| \(0\) | \(0\) with probability \(3/5\); each of \(5/4,-5/4\) with probability \(1/5\) |
| \(1\) | \(1\) with probability \(1/5\); \(-1/4\) with probability \(4/5\) |
| \(-1\) | \(-1\) with probability \(1/5\); \(1/4\) with probability \(4/5\) |

Consequently the exact conditional moments are

| \(z\) | \(\mathbb E(D_t^2\mid z)\) | \(\mathbb E(D_t^3\mid z)\) | \(\mathbb E(D_t^4\mid z)\) |
|---|---:|---:|---:|
| \(0\) | \(5/8\) | \(0\) | \(125/128\) |
| \(1\) | \(1/4\) | \(3/16\) | \(13/64\) |
| \(-1\) | \(1/4\) | \(-3/16\) | \(13/64\) |

These finite identities are checked by the accompanying exact
audit directly from all six transition rows.

## 2. The exact second moment

Put \(p_t=\mathbb P(g(X_t)\ne0)\). From a zero-score state,
the next score is nonzero with probability \(2/5\); from
either nonzero-score state, that probability is \(1/5\).
Because \(p_0=0\),

\[
 p_{t+1}=\frac25-\frac15p_t,
 \qquad
 p_t=\frac{1-(-1/5)^t}{3}.
 \tag{6}
\]

Martingale differences are orthogonal in the second moment.
Using the table above,

\[
 \begin{aligned}
 \mathbb E M_N^2
 &=\sum_{t=0}^{N-1}
   \left(\frac58-\frac38p_t\right)\\
 &=\boxed{\frac N2+\frac5{48}\bigl(1-(-1/5)^N\bigr).}
 \end{aligned}
 \tag{7}
\]

In particular,

\[
 \frac N2\le\mathbb E M_N^2\le\frac{5N}{8}.
 \tag{8}
\]

The upper bound also follows immediately by summing the largest
conditional variance \(5/8\).

## 3. A fourth-moment bound

Write \(V_t=\mathbb E M_t^2\) and \(A_t=\mathbb E M_t^4\).
Expand \((M_t+D_{t+1})^4\), condition on \(\mathcal F_t\),
and use the zero conditional mean. The moment table gives

\[
 \begin{aligned}
 A_{t+1}-A_t
 &\le \frac{15}{4}V_t
       +\frac34\mathbb E\bigl[M_tg(X_t)\bigr]
       +\frac{125}{128}\\
 &\le \frac{15}{4}V_t
       +\frac34\sqrt{V_t}
       +\frac{125}{128}.
 \end{aligned}
 \tag{9}
\]

The last inequality is Cauchy--Schwarz and \(|g|\le1\).
Since \(\sqrt{x}\le(x+1)/2\) for \(x\ge0\),

\[
 A_{t+1}-A_t
 \le\frac{33}{8}V_t+\frac{173}{128}
 \le\frac{165}{64}t+\frac{173}{128}.
 \tag{10}
\]

Summing from \(t=0\) to \(N-1\) proves

\[
 \boxed{
 \mathbb E M_N^4
 \le\frac{165N^2+8N}{128}
 <2N^2\qquad(N\ge1).
 }
 \tag{11}
\]

Thus the second moment grows linearly while the fourth moment
grows at most quadratically, with constants independent of
the word length.

## 4. A fixed positive fraction has square-root score

For a nonnegative random variable \(Z\) with
\(m=\mathbb E Z>0\),

\[
 \mathbb E\bigl[Z\mathbf1_{\{Z\ge m/2\}}\bigr]\ge m/2.
\]

Cauchy--Schwarz therefore gives the elementary second-moment
inequality

\[
 \mathbb P(Z\ge m/2)
 \ge\frac{m^2}{4\mathbb E Z^2}.
 \tag{12}
\]

Apply (12) to \(Z=M_N^2\). Equations (8) and (11) show

\[
 \mathbb P\left(|M_N|\ge\frac{\sqrt N}{2}\right)
 \ge\frac1{32}.
 \tag{13}
\]

On this event, (5) yields

\[
 |S_N|\ge\frac{\sqrt N}{2}-\frac14
          \ge\frac{\sqrt N}{4},
 \qquad N\ge1.
\]

This proves (1), with no limit theorem or asymptotic error.

## 5. An injective positive-score return construction

Reflection sends state \(u\) to \(5-u\), complements each
digit \(a\) to \(4-a\), and reverses the score. Digit 0
resets every initial state to state 0; digit 4 resets every
initial state to state 5. Both reset steps have score zero.

For a raw word \(w\) counted in (1), let \(\bar w\) be its
digitwise complement and define

\[
 T(w)=
 \begin{cases}
 [0,w,0,2,1],&S_N(w)\ge0,\\
 [4,\bar w,0,2,1],&S_N(w)<0.
 \end{cases}
 \tag{14}
\]

The reset step makes the raw score independent of the prior
state. The middle word has score \(|S_N(w)|\). Finally,
\([0,2,1]\) passes through states \(0,2,1\), returns to
state 1, and adds exactly one. Thus the complete score is
\(|S_N(w)|+1\), proving (2).

The map \(T\) is injective. Its first digit identifies the
choice in (14), and the middle digits then recover \(w\)
uniquely. The selected returning family therefore contains
at least \(5^N/32\) distinct words.

One useful consequence for the contour application is that
a large positive total score also controls the shallow branch.
The carry indicator in the refined contour estimate has state values
\(\chi=(1,0,0,1,1,0)\). Since \(g(u)\le1-\chi(u)\) in
each state, any digit path satisfies

\[
 \sum g\le\#\{\text{carry-zero steps}\}.
 \tag{15}
\]

For an index with the fixed three-digit prefix, this implies
\(L-K_{\rm free}\ge3+\sum g\). A positive square-root score
eventually dominates the logarithmic shallow-denominator
budget in the refined contour bound.

## 6. Exact reproduction and scope

The [audit](../../../../workflows/experiments/salikhov_score_moments_20261017/audit.py)
checks all thirty rational interval inclusions, the conditional
moments as rational numbers, the exact
second-moment identity and fourth-moment bound through 100
word lengths by complete state/score counting, and the tail
count using the integer inequality \(16S_N^2\ge N\).
It also exhausts the raw words through length six to check
the return injection directly. The
[certificate](../../../../workflows/experiments/salikhov_score_moments_20261017/certificate.json)
is deterministic.

From the repository root:

    python3 workflows/experiments/salikhov_score_moments_20261017/audit.py --json workflows/experiments/salikhov_score_moments_20261017/certificate.json

The infinite moment argument proves the statement for every
\(N\ge1\); finite counting only verifies the specified
identities and sample consequences. A separate application
must still provide the binary progression, actual-pi phase
information, and cutoff transfer. This note alone proves no
decimal occurrence.
