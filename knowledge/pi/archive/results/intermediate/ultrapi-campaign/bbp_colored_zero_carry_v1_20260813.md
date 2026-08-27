# Colored zero-carry blocks: an exact V1 criterion and the BBP color recurrence

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Frozen inputs:

- [bbp_fixed_period_carry_attack_20260813.md](bbp_fixed_period_carry_attack_20260813.md),
  SHA-256
  bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55;
- [bbp_centered_carry_recurrence_20260813.md](bbp_centered_carry_recurrence_20260813.md),
  SHA-256
  3a357c5b1932b76357259613c338dc6ca49f4bf68baef96730ad31b2a13e69e6;
- [bbp_centered_carry_recurrence_20260813_check.py](bbp_centered_carry_recurrence_20260813_check.py),
  SHA-256
  b83276cc2aceb61e903e8764424e2a3b9dddec8a5ac16ffff4b8370200316fff.

## Outcome and claim boundary

Canonical V1 remains a 'conjecture'. No colored zero-carry existence theorem
for pi is obtained here.

There is nevertheless a material exact reduction, recorded as a
'proof sketch'.

1. V1 is equivalent to the following statement: for every \(P\geq1\), every
   residue \(k\pmod {10^P-1}\), every block length \(H\geq1\), and every
   onset \(N\geq0\), some \(n\geq N\) begins \(H\) consecutive true zero
   centered carries and has nearest integer \(z_{n,P}\equiv k\pmod{10^P-1}\).
2. The zero residue merges the all-zero and all-nine periodic words. This
   does not invalidate the residue criterion, because nonzero interior
   residues alone imply V1 after appending one digit to a target word. A
   literal “every periodic word” formulation must retain a split color in
   \(\{0,\ldots,10^P-1\}\).
3. The audited eventual identity between true and sevenfold-BBP nearest
   integers transfers the criterion to the exact rational quantities
   \(\widehat z_{n,P}\) and \(\widehat\gamma_{n,P}\).
4. All periods share one exact, \(P\)-independent rational phase \(r_n/D_n\).
   Its recurrence and every color/carry are explicit below. The color is an
   Archimedean partition of that phase, not a fixed-modulus residue.
5. Indeed \(10^P-1\mid D_n\) eventually. The congruence
   \(D_n\widehat z_{n,P}\equiv-S_{n,P}\pmod{10^P-1}\) then becomes
   \(0\equiv0\), while the colors continue to vary.

The bounded replay has label 'experiment'. The surrounding BBP and
irrationality-measure source audit inherited from the frozen inputs is
'literature-checked'; no separate novelty claim is made for the elementary
equivalence. Nothing here is 'machine-checked', a 'candidate resolution', or
a 'verified resolution'.

## 1. Normalized target and all quantifiers

For an irrational real number \(x\), let

\[
y_n=\{10^nx\}\in(0,1).
\]

Use its unique nonterminating decimal expansion. Say \(x\) is
decimal-disjunctive when every finite word over \(\{0,\ldots,9\}\), including
words with leading zeroes, occurs contiguously. The empty word is vacuous.
Canonical V1 says that \(x=\pi\) is decimal-disjunctive.

Fix \(P\geq1\), put \(q=q_P=10^P-1\), and define

\[
\begin{aligned}
z_{n,P}&=\left\lfloor q10^nx+\frac12\right\rfloor,\\
e_{n,P}&=q10^nx-z_{n,P},\\
\gamma_{n,P}&=z_{n+1,P}-10z_{n,P}.
\end{aligned}                                                     \tag{1}
\]

Irrationality excludes half-integer boundaries, so

\[
-\frac12<e_{n,P}<\frac12,\qquad
e_{n+1,P}=10e_{n,P}-\gamma_{n,P}.                    \tag{2}
\]

The proposed colored condition must retain every quantifier:

\[
\begin{split}
\mathcal C_{\rm res}(x):\quad
&\forall P\geq1\ \forall k\in\{0,\ldots,q_P-1\}\
\forall H\geq1\ \forall N\geq0\ \exists n\geq N:\\
&z_{n,P}\equiv k\pmod {q_P},\qquad
\gamma_{n,P}=\cdots=\gamma_{n+H-1,P}=0.
\end{split}                                                       \tag{3}
\]

One period, one color, some long block, or any finite replay is not (3).

## 2. Zero blocks are shrinking torsion-point visits

Iteration of (2) gives

\[
\boxed{
\gamma_{n,P}=\cdots=\gamma_{n+H-1,P}=0
\iff
|e_{n,P}|<{1\over2\,10^H}.}                          \tag{4}
\]

Forward, \(e_{n+H,P}=10^He_{n,P}\). Conversely, the displayed bound keeps
every \(10^te_{n,P}\), \(0\leq t\leq H\), in the nearest-integer cell around
\(10^tz_{n,P}\), so \(z_{n+t,P}=10^tz_{n,P}\).

Define the split color

\[
c_{n,P}=\left\lfloor qy_n+\frac12\right\rfloor
\in\{0,1,\ldots,q\}.                                  \tag{5}
\]

For \(I_n=\lfloor10^nx\rfloor\),

\[
z_{n,P}=qI_n+c_{n,P},\quad e_{n,P}=qy_n-c_{n,P},\quad
z_{n,P}\bmod q=c_{n,P}\bmod q.                       \tag{6}
\]

An interior color \(1\leq k\leq q-1\) and an \(H\)-zero block therefore mean

\[
\left|y_n-{k\over q}\right|<{1\over2q10^H}.          \tag{7}
\]

For residue zero there are two one-sided cases:

\[
c_{n,P}=0:\ 0<y_n<{1\over2q10^H},\qquad
c_{n,P}=q:\ 0<1-y_n<{1\over2q10^H}.                  \tag{8}
\]

This is the endpoint information discarded modulo \(q\).

## 3. Periodic words and the exact V1 equivalence

For \(1\leq k\leq q-1\), write \(k\) as a \(P\)-digit word, padding with
leading zeroes. Then

\[
{k\over10^P-1}=0.\overline{\operatorname{digits}_P(k)}.           \tag{9}
\]

Its reduced denominator is coprime to 10 and greater than one, so its decimal
expansion is uniquely purely periodic. If

\[
k_{t+1}\equiv10k_t\pmod q,\quad1\leq k_t\leq q-1,
\]

then

\[
d_t={10k_t-k_{t+1}\over q}\in\{0,\ldots,9\}          \tag{10}
\]

emits its digits, and \(k_P=k_0\). If \(10^Hk=Aq+k_H\), then the distances
from \(k/q\) to the endpoints of its length-\(H\) cylinder are

\[
{k_H\over q10^H},\qquad {q-k_H\over q10^H},          \tag{11}
\]

both at least \(1/(q10^H)\). Thus (7), whose radius is half as large,
forces the first \(H\) periodic digits. The two sides in (8) force \(H\)
zeroes or \(H\) nines.

Let \(\mathcal C_{\rm split}(x)\) replace the residue in (3) by every exact
split color \(c\in\{0,\ldots,q\}\). Let
\(\mathcal C_{\rm int}(x)\) ask only for every \(1\leq k\leq q-1\). Then

\[
\boxed{
x\hbox{ is decimal-disjunctive}
\iff\mathcal C_{\rm split}(x)
\iff\mathcal C_{\rm res}(x)
\iff\mathcal C_{\rm int}(x).}                       \tag{12}
\]

The quantifiers and boundary cases are checked next.

### Decimal-disjunctivity implies every split color

Every finite word occurs arbitrarily late: apply decimal-disjunctivity to
\(0^Nw\); its suffix \(w\) begins at a position at least \(N\).

Fix \(P,c,H,N\). For interior \(c\), request a late occurrence of the first

\[
L=H+P+1                                               \tag{13}
\]

digits of the periodic expansion \(c/q\). The resulting \(y_n\) lies in the
same length-\(L\) cylinder, and

\[
\left|y_n-{c\over q}\right|<10^{-L}
<{1\over2q10^H}.                                     \tag{14}
\]

Equations (4)--(7) give the color and zero block. For \(c=0\), request
\(L\) zeroes; for \(c=q\), request \(L\) nines. Irrationality excludes the
terminating-cylinder endpoints. Hence decimal-disjunctivity implies
\(\mathcal C_{\rm split}\), which implies \(\mathcal C_{\rm res}\) after
reduction modulo \(q\).

### Interior colors already imply every finite word

The implication \(\mathcal C_{\rm res}\Rightarrow\mathcal C_{\rm int}\) is
immediate. Conversely, let \(w\) have length \(m\geq1\) and integer value
\(a\in\{0,\ldots,10^m-1\}\). Set \(P=m+1\), and append one digit:

\[
d=\begin{cases}1,&a=0,\\0,&a>0,\end{cases}
\qquad k=10a+d.                                      \tag{15}
\]

Then \(1\leq k\leq10^P-2=q-1\), so \(k\) is interior, and its \(P\)-digit
word begins with \(w\). Apply \(\mathcal C_{\rm int}\) with \(H=P\).
Equations (4) and (6) give

\[
\left|y_n-{k\over q}\right|<{1\over2q10^P}.          \tag{16}
\]

The left and right margins of \(k/q\) inside its \(P\)-digit cylinder are

\[
{k\over q10^P},\qquad {q-k\over q10^P},              \tag{17}
\]

both at least \(1/(q10^P)\). Hence \(y_n\) begins with \(w\).
Leading-zero words use the appended 1; all-nine words stay interior after
the appended 0. This proves (12).

Thus the residue version is exact. The phrase “every length-\(P\) periodic
word” is literally accurate only for the split version: \(0^P\) and \(9^P\)
are the two one-sided codes of the same circle point and both reduce to
residue zero.

## 4. Transfer to the eventual sevenfold-BBP shadows

The frozen fixed-period report defines

\[
\widehat z_{n,P}
=\left\lfloor q_P10^nB_{7n}+\frac12\right\rfloor,\qquad
\widehat\gamma_{n,P}
=\widehat z_{n+1,P}-10\widehat z_{n,P}.              \tag{18}
\]

Its irrationality-measure and BBP-tail comparison gives, as an inherited
'proof sketch', an onset \(n_0(P)\) such that

\[
\widehat z_{n,P}=z_{n,P},\qquad
\widehat\gamma_{n,P}=\gamma_{n,P}\quad(n\geq n_0(P)). \tag{19}
\]

The quantifier \(\forall N\,\exists n\geq N\) makes (3) invariant under a
finite prefix change: replace \(N\) by \(\max(N,n_0(P))\). Therefore

\[
\boxed{
\mathrm{V1}
\iff
\forall P\geq1\ \forall k\pmod {q_P}\ \forall H\geq1\
\forall N\geq0\ \exists n\geq N:\quad
\widehat z_{n,P}\equiv k\pmod {q_P},\quad
\widehat\gamma_{n,P}=\cdots=\widehat\gamma_{n+H-1,P}=0.}         \tag{20}
\]

Equation (20) is a reformulation, not a verification of its right-hand side.

## 5. One \(P\)-independent BBP phase controls every color

Use the exact integers from the frozen centered-carry report:

\[
\begin{aligned}
B_{7n}&={A_{7n}\over16^{7n}L_{7n}},&
D_n&=2^{27n}L_{7n},\\
R_n&={L_{7n+7}\over L_{7n}},&
\Lambda_n&=2^{27}R_n,\\
H_n&=A_{7n+7}-16^7R_nA_{7n}.&&
\end{aligned}                                                     \tag{21}
\]

Remove the repunit multiplier and define

\[
V_n=5^nA_{7n},\qquad
V_n=a_nD_n+r_n,\qquad0\leq r_n<D_n.                  \tag{22}
\]

Thus \(r_n/D_n=\{10^nB_{7n}\}\), independently of \(P\). Put
\(K_n=5^{n+1}H_n\). The sevenfold recurrence becomes

\[
V_{n+1}=10\Lambda_nV_n+K_n,\qquad
D_{n+1}=\Lambda_nD_n.                                \tag{23}
\]

Euclidean division of the part depending on \(r_n\) gives

\[
\begin{aligned}
b_n&=\left\lfloor{10\Lambda_nr_n+K_n\over D_{n+1}}\right\rfloor,\\
r_{n+1}&=10\Lambda_nr_n+K_n-b_nD_{n+1},\\
a_{n+1}&=10a_n+b_n.
\end{aligned}                                                     \tag{24}
\]

For each \(P\), define the exact rational split color

\[
\widehat c_{n,P}
=\left\lfloor{q_Pr_n\over D_n}+\frac12\right\rfloor
\in\{0,\ldots,q_P\}.                                  \tag{25}
\]

Since \(q_PV_n/D_n=q_Pa_n+q_Pr_n/D_n\),

\[
\boxed{
\widehat z_{n,P}=q_Pa_n+\widehat c_{n,P},\qquad
\widehat z_{n,P}\bmod q_P=\widehat c_{n,P}\bmod q_P,}              \tag{26}
\]

and (24) gives the exact carry factorization

\[
\boxed{
\widehat\gamma_{n,P}
=q_Pb_n+\widehat c_{n+1,P}-10\widehat c_{n,P}.}       \tag{27}
\]

In particular,

\[
\widehat\gamma_{n,P}=0
\iff q_Pb_n+\widehat c_{n+1,P}=10\widehat c_{n,P}.    \tag{28}
\]

If an \(H\)-zero block starts at interior color \(k\), then

\[
\widehat c_{n+t,P}\equiv10^tk\pmod {q_P},\qquad
b_{n+t}={10\widehat c_{n+t,P}-\widehat c_{n+t+1,P}\over q_P}.     \tag{29}
\]

The \(b\)'s therefore emit the periodic digits belonging to \(k\). Equations
(24)--(29) are an exact common-state version of (20): one changing rational
phase must shadow every periodic word for arbitrary lengths and late starts.

## 6. Why the color is not a fixed-modulus shortcut

The old centered numerator is

\[
S_{n,P}=q_PV_n-D_n\widehat z_{n,P},                  \tag{30}
\]

so

\[
D_n\widehat z_{n,P}\equiv-S_{n,P}\pmod {q_P}.        \tag{31}
\]

This congruence eventually loses all color information. Let \(q=q_P\) and
\(j=(q-1)/2\). The first factor in

\[
d_j=(2j+1)(4j+3)(8j+1)(8j+5)
\]

is \(q\). Hence

\[
n\geq\left\lceil{q-1\over14}\right\rceil
\Longrightarrow q\mid L_{7n}\mid D_n.               \tag{32}
\]

Since \(q\mid qV_n\), (30) also gives \(q\mid S_{n,P}\), and (31) is
\(0\equiv0\).

The color can be retained through a growing modulus:

\[
\widehat z_{n,P}\equiv k\pmod q
\iff qV_n-S_{n,P}-D_nk\equiv0\pmod {qD_n}.           \tag{33}
\]

But this is tautological: the left side is
\(D_n(\widehat z_{n,P}-k)\). The carry term
\(-\widehat\gamma_{n,P}D_{n+1}\) no longer vanishes modulo
\(qD_{n+1}\). Equations (24)--(28) say the same thing more cleanly: the
recurrence for \(r_n\) is carry-free, but the color is selected by the
Archimedean ratio \(r_n/D_n\). A fixed residue \(r_n\bmod q\) does not
determine that cell.

## 7. Two exact warnings against weaker targets

### Residue zero merges the boundary words

The certified decimal prefix and rational sevenfold replay agree at the five
zero carries \(n=761,\ldots,765\) for \(P=1\). At all six endpoint states,

\[
\widehat c_{n,1}=c_{n,1}=9,\qquad z_{n,1}\equiv0\pmod9
\quad(761\leq n\leq766).                              \tag{34}
\]

This observed residue-zero block lies on the all-nine side, not the all-zero
side. These bounded facts have label 'experiment'; the general split is
already exact in (8).

### Uncolored long zero blocks do not imply V1

Consider

\[
\xi=\sum_{j=2}^{\infty}10^{-j!}.                      \tag{35}
\]

Its decimal expansion has a 1 at each factorial position and zeroes
elsewhere, so it is irrational and not decimal-disjunctive; digit 2 never
occurs. Fix arbitrary \(P,H,N\), put \(q=10^P-1\), and choose \(j\) with
\(n=j!\geq N\) and \(G=(j+1)!-j!\) so large that

\[
q{10\over9}10^{-G}<{1\over2\,10^H}.                 \tag{36}
\]

Terms through \(j!\) become integers after multiplication by \(10^n\), while

\[
0<\{10^n\xi\}
=\sum_{\ell>j}10^{j!-\ell!}
\leq {10\over9}10^{-G}.                              \tag{37}
\]

Equations (4)--(8) give an \(H\)-zero block of split color zero. This works
for every \(P,H,N\), although \(\xi\) fails V1. Thus even arbitrarily late,
arbitrarily long, uncolored zero blocks for every period are insufficient.
The all-color quantifier in (3) is essential. This construction is a
'proof sketch'; the checker only samples its exact inequality.

## 8. Exact replay

The companion
[bbp_colored_zero_carry_v1_20260813_check.py](bbp_colored_zero_carry_v1_20260813_check.py)
has SHA-256
7fbce9df0a4a92831ce7cadc5c0343546be71dd771331f7b5f7270fd4150d916.
It uses only integers and Python Fraction. It:

- pins the canonical source, frozen BBP artifacts, and certified prefix;
- reconstructs \(L_{7n},A_{7n},D_n,V_n,r_n\) through \(n=800\);
- checks 3,200 instances of (23)--(28) for \(P=1,2,3,4\);
- exhaustively checks 11,102 residue/periodic-word correspondences;
- checks the absorption witnesses in (32), through \(P=4,n=715\);
- exhibits \(r_2\equiv r_4\equiv3\pmod9\) with colors 1 and 8;
- independently reencloses the true split colors in (34); and
- samples (36) at three factorial-gap witnesses.

Replay from the repository root:

    .venv/bin/python -m py_compile \
      work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_check.py
    .venv/bin/python \
      work/ultrapi-resume/bbp_colored_zero_carry_v1_20260813_check.py

The retained replay reports 'status: PASS',
'asserts_colored_condition_for_pi: false', and 'asserts_v1: false'.
Every bounded row has label 'experiment'.

## Sharp handoff

The direct target is exact and wholly rational: prove that the common phase
recurrence (24), through the partitions (25), realizes every interior
periodic color with arbitrarily late zero-carry blocks of every length. By
(20), this is neither stronger nor weaker than V1; it is V1 in centered-BBP
coordinates.

The reduction rules out three tempting weakenings. Uncolored long blocks are
insufficient by (35)--(37); ordinary residue zero loses the zero/nine side;
and each fixed color modulus is eventually absorbed into \(D_n\) by (32).
A viable continuation needs genuine Archimedean recurrence or density of
\(r_n/D_n\), not another congruence of \(S_{n,P}\) modulo a fixed factor. No
such theorem is obtained here, so canonical V1 remains a 'conjecture'.
