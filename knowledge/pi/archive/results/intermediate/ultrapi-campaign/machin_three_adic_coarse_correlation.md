# Three-adic leading units select the Machin coarse class

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local source contains no external source URL,
so none is invented here.  
Inputs: [T52](../../TheoryLib/PiQuantitativeBlockHitting/T52T52MachinSeedThreePrimaryPersistence.lean),
[T53](../../TheoryLib/PiQuantitativeBlockHitting/T53T53MachinQuotientCarry.lean),
and the exact finite Machin expansion recorded in
[`actual_numerator_phase_attack.md`](actual_numerator_phase_attack.md).

## Outcome and claim status

No proof that every finite decimal word occurs in \(\pi\) was obtained. The
canonical target remains a `conjecture`.

This note gives a new internal `proof sketch` lemma about the **actual**
reduced Machin seed. It has not been formalized in Lean and no literature
novelty is claimed. For every fixed \(k\), the residue

\[
             3^{a_j-1}10^jM_{3j}\pmod {3^k}
\]

eventually comes from a bounded, self-similar window of fewer than \(3^k\)
renormalized Taylor exponents. Combined with the exact fine remainder, this
residue selects the actual coarse quotient modulo \(3^k\). Modulo nine the
formula is an explicit three-step staircase in each three-primary epoch.

Together with the **actual fine remainder**, this feeds the shifted-grid
attack: it replaces the full \(D_j\)-grid by a nested-in-\(k\) coset grid of
size \(D_j/3^k\) which still contains the actual Machin point. The leading
formula alone does not identify that coset. This is not an ASR estimate. For
fixed \(k\), the saving is only the constant factor \(3^k\), while the
surviving Fourier lattice becomes denser. Taking \(k\) comparable to \(a_j\)
merely restores the full numerator problem in another form.

The companion checker is an `experiment`. It uses exact rational and modular
integer arithmetic only; finite evidence is never used as proof.

## 1. Normalized target and seed

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^m\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.              \tag{1}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed, and
\(m=0\) is vacuous. This is contiguous finite occurrence, not subsequence
occurrence and not normality.

For \(j\ge1\), put

\[
 y_j=10^jM_{3j},\qquad d_j=12j+3,
 \qquad 3^{a_j}\le d_j<3^{a_j+1},
 \qquad D_j=3^{a_j-1}.                            \tag{2}
\]

T52 proves that \(D_j\) is exactly the complete three-primary part of the
reduced denominator of \(y_j\). Write

\[
 \{y_j\}={b_j\over Q_j},\qquad Q_j=F_jD_j,
 \qquad b_j=F_jc_j+r_j,\qquad
 0\le c_j<D_j,\qquad 0\le r_j<F_j.              \tag{3}
\]

Thus \((F_j,D_j)=1\), \(c_j=\lfloor D_j\{y_j\}\rfloor\), and

\[
 \{y_j\}={c_j\over D_j}+{r_j\over F_jD_j}.
                                                               \tag{4}
\]

The exact finite seed formula is

\[
 M_{3j}=
 \sum_{\substack{1\le u\le d_j\\u\text{ odd}}}
 {4\chi_4(u)(4\cdot239^u-5^u)\over u5^u239^u}
 -{4\over(d_j+2)239^{d_j+2}},                    \tag{5}
\]

where \(\chi_4(u)=(-1)^{(u-1)/2}\). Define the integer three-adic unit

\[
                   U(u):={4\cdot239^u-5^u\over3}. \tag{6}
\]

T52 proves precisely that \(v_3(U(u))=0\).

Congruences below are in the localization \(\mathbb Z_{(3)}\): a rational
denominator prime to three is inverted modulo \(3^k\).

## 2. Sparse leading-unit window

Fix \(1\le k\le a_j-1\), and abbreviate

\[
 g=3^{a_j-k+1},\qquad h=\left\lfloor{d_j\over g}\right\rfloor<3^k.
                                                               \tag{7}
\]

For an odd \(t\le h\), write \(t=3^st_0\) with \(3\nmid t_0\). Define

\[
 \begin{aligned}
 W_{j,k}(t):={}&4\chi_4(gt)3^{k-1-s}U(gt)\\
 &\cdot\bigl(t_0 5^{gt}239^{gt}\bigr)^{-1}
       \pmod {3^k}.                              \tag{8}
 \end{aligned}
\]

### Lemma 1 (`proof sketch`): exact sparse window

\[
 \boxed{
 D_jy_j\equiv10^j
   \sum_{\substack{1\le t\le h\\t\text{ odd}}}W_{j,k}(t)
       \pmod {3^k}.}                              \tag{9}
\]

**Derivation.** The common pair at exponent \(u\) in (5) has valuation
\(1-v_3(u)\). After multiplication by \(D_j\), its valuation is

\[
                         a_j-v_3(u).              \tag{10}
\]

It therefore vanishes modulo \(3^k\) unless
\(v_3(u)\ge a_j-k+1\), exactly when \(u=gt\) for one of the fewer than
\(3^k\) odd values in (7). For such a value, direct cancellation gives

\[
 D_j{4\chi_4(u)(4\cdot239^u-5^u)\over u5^u239^u}
 ={4\chi_4(gt)3^{k-1-s}U(gt)\over
       t_0 5^{gt}239^{gt}},                       \tag{11}
\]

which is (8). Since \(d_j+2\equiv2\pmod3\), the endpoint in (5) has
valuation zero; after multiplication by \(D_j\) its valuation is
\(a_j-1\ge k\), so it vanishes as well. This proves (9). \(\square\)

The key point is uniformity: for fixed \(k\), the number of surviving
exponents is bounded independently of \(j\). This is more information than
the single leading unit used in T52.

## 3. Stable renormalization at fixed depth

Suppose now that

\[
                         a_j\ge2k-1.              \tag{12}
\]

Put \(e=a_j-k+1\), so \(e\ge k\). For every odd \(t\),

\[
                    3^et\equiv3^k\pmod {2\cdot3^k}. \tag{13}
\]

For each \(q\in\{5,239\}\), odd-exponent LTE gives

\[
 v_3(q^{3^k}+1)=v_3(q+1)+k=k+1.                 \tag{14}
\]

Euler periodicity modulo \(3^{k+1}\) and (13) consequently imply

\[
 5^{3^et}\equiv239^{3^et}\equiv-1\pmod {3^{k+1}},
 \quad U(3^et)\equiv-1\pmod {3^k},
 \quad5^{3^et}239^{3^et}\equiv1\pmod {3^k}.     \tag{15}
\]

Define the finite signed harmonic staircase

\[
 H_k(h):=\sum_{\substack{1\le t\le h\\t\text{ odd}}}
 \chi_4(t)3^{k-1-v_3(t)}
 \left({t\over3^{v_3(t)}}\right)^{-1}\pmod {3^k}. \tag{16}
\]

### Lemma 2 (`proof sketch`): stable fixed-\(k\) formula

Under (12),

\[
 \boxed{
 D_jy_j\equiv
 -4\,10^j(-1)^{a_j-k+1}H_k(h)\pmod {3^k}.}       \tag{17}
\]

**Derivation.** Substitute (15) into (8) and use the multiplicativity
\(\chi_4(3^et)=(-1)^e\chi_4(t)\). \(\square\)

This also gives an exact sparse cross-index recurrence. If \(j,j+1\) remain
in the same \(a\)-band, put

\[
 h_i=\left\lfloor{12i+3\over3^{a-k+1}}\right\rfloor
 \quad(i=j,j+1).
\]

Then

\[
 \boxed{
 L_{j+1,k}-10L_{j,k}\equiv
 -4(-1)^{a-k+1}10^{j+1}
       \bigl(H_k(h_{j+1})-H_k(h_j)\bigr)\pmod {3^k}.}         \tag{18}
\]

where \(L_{j,k}=D_jy_j\pmod {3^k}\). Away from a newly crossed odd
renormalized exponent, the right side is zero. Thus the leading unit follows
the multiplier ten with sparse, completely explicit impulses. Formula (18)
does not cover a tripling boundary, where \(a_j\) changes.

## 4. The explicit residues modulo three and nine

Taking \(k=1\) in (17) leaves only \(t=1\). For every \(j\ge1\),

\[
 \boxed{D_jy_j\equiv
 \begin{cases}1\pmod3,&a_j\text{ odd},\\
               2\pmod3,&a_j\text{ even}.
 \end{cases}}                                      \tag{19}
\]

For \(k=2\), condition (12) is \(a_j\ge3\), equivalently \(j\ge2\).
Now

\[
 h=\left\lfloor{d_j\over D_j}\right\rfloor\in\{3,4,5,6,7,8\},
\]

and direct evaluation of (16) gives

\[
 H_2(h)\equiv
 \begin{cases}
 2\pmod9,&3\le h<5,\\
 8\pmod9,&5\le h<7,\\
 5\pmod9,&7\le h<9.
 \end{cases}                                      \tag{20}
\]

Since \(10^j\equiv1\pmod9\), (17) becomes the three-step staircase

\[
 \boxed{
 D_jy_j\equiv
 \begin{array}{c|ccc}
  &3\le h<5&5\le h<7&7\le h<9\\ \hline
  a_j\text{ odd}&1&4&7\\
  a_j\text{ even}&8&5&2
 \end{array}\pmod9.}                             \tag{21}
\]

The exceptional first seed has \(a_1=2,D_1=3\), so a congruence modulo nine
is not available from the coarse split; direct exact evaluation happens to
give \(D_1y_1\equiv2\pmod9\), but it is not part of (21).

## 5. Exact coarse/fine selector

Let \(n_j=\lfloor y_j\rfloor\). Equations (3)--(4) give the rational
identity

\[
 D_jy_j=D_jn_j+c_j+{r_j\over F_j}.                \tag{22}
\]

Because \(3^k\mid D_j\) whenever \(k\le a_j-1\), (22) and Lemma 1 give:

### Lemma 3 (`proof sketch`): actual coarse-class correlation

\[
 \boxed{
 c_j+ r_jF_j^{-1}\equiv L_{j,k}\pmod {3^k},
 \qquad
 c_j\equiv L_{j,k}-r_jF_j^{-1}\pmod {3^k}.}       \tag{23}
\]

Here \(L_{j,k}\) can be computed by the sparse formula (9), or by the stable
formula (17) when (12) holds. In particular, (19) and (21) give completely
explicit selectors modulo three and nine.

This is a genuine correlation, not a distribution theorem. The leading unit
alone does **not** determine \(c_j\); the fine term \(r_jF_j^{-1}\) is
essential.

The selector propagates through the entire ordinary decimal pulse of the
fixed seed. Define

\[
 b_{j,t}:=10^tb_j\bmod Q_j=F_jc_{j,t}+r_{j,t},
 \qquad 0\le c_{j,t}<D_j,\quad 0\le r_{j,t}<F_j.  \tag{23a}
\]

T53's exact carry recurrence writes

\[
 \begin{aligned}
 r_{j,t+1}&=10r_{j,t}-F_j\kappa_{j,t},\\
 c_{j,t+1}&=10c_{j,t}+\kappa_{j,t}-D_j\delta_{j,t},
 \end{aligned}                                   \tag{23b}
\]

where \(\kappa_{j,t}=\lfloor10r_{j,t}/F_j\rfloor\) and
\(\delta_{j,t}\) is the decimal carry. Adding the two lines after dividing
the first by \(F_j\), and using \(3^k\mid D_j\), gives

\[
 \boxed{
 c_{j,t}+r_{j,t}F_j^{-1}
 \equiv10^tL_{j,k}\pmod {3^k}.}                  \tag{23c}
\]

Thus the selected coarse class does not need to be recomputed from scratch
at every digit once the **actual fine state** is supplied: its fine carries
transport the class exactly. This is still a correlation with actual fine
data, not a leading-unit-only selection rule.

There is a direct shifted-grid consequence. Let

\[
 C_{j,k}:=L_{j,k}-r_jF_j^{-1}\pmod {3^k}.
\]

Then the smaller grid

\[
 \boxed{
 G_{j,k}=\left\{
 {C_{j,k}+3^kt\over D_j}+{r_j\over F_jD_j}:
 0\le t<{D_j\over3^k}\right\}\pmod1}             \tag{24}
\]

contains the actual point \(\{y_j\}\). It has \(D_j/3^k\) points, rather
than \(D_j\). Its Fourier resonances occur at multiples of
\(D_j/3^k\), rather than multiples of \(D_j\). The smaller zero mode and the
denser resonant lattice are the exact tradeoff.

For \(k=2\), (24) identifies the actual one of nine coarse cosets. Under the
T53 map the common fine carry translates all nine cosets equally, while
multiplication by ten preserves their pairwise classes modulo nine. This
supplies the missing selector behind the nine-class observation in the
nested three-primary resonance note.

## 6. Exact falsification and finite occupancy audit

The checker
[`machin_three_adic_coarse_correlation_check.py`](machin_three_adic_coarse_correlation_check.py)
recomputes every seed as an exact `Fraction`. Through \(j=80\) and every
valid \(k\le5\), it checked:

- 314 instances of the sparse window (9);
- 220 instances of the stable collapse (17);
- 314 coarse/fine selectors (23);
- 6,594 propagated fixed-seed pulse selectors (23c), through 20 decimal
  transitions per checked pair;
- 80 modulo-three values and 79 modulo-nine staircase values;
- 209 same-band impulse recurrences (18), of which 15 had a nonzero impulse.

These counts are an `experiment`, not a formal proof. The derivations above
are retained as a `proof sketch` until formalized and axiom-audited.

The same exact run falsifies several tempting stronger statements:

1. **The actual coarse class is not constant inside an epoch.** At
   \(j=2,3\), both seeds have \(a=3,D=9\), but
   \(c_2\equiv1\pmod9\) and \(c_3\equiv5\pmod9\).
2. **There is no carry-free recurrence
   \(c_{j+1}\equiv10c_j\pmod9\).** The same pair is a counterexample.
3. **Even the leading unit has impulses.** From \(j=3\) to \(j=4\),
   \(L_{j,2}\) changes from \(1\) to \(4\pmod9\), rather than following
   \(L_{j+1,2}\equiv10L_{j,2}\). This is exactly the \(h=5\) impulse in
   (18), not an error in the staircase.
4. **The leading unit alone does not select the coarse class.** At
   \(j=2,3\), both leading units are \(1\pmod9\), while the coarse classes
   are \(1\) and \(5\). The fine residues in (23) account for the difference.
5. Through \(j=80\), both \(c_j\pmod9\) and
   \(r_jF_j^{-1}\pmod9\) attain all nine residues. This finite observation
   rules out a missing-residue conjecture on that range; it proves no
   asymptotic equidistribution.

As a targeted occupancy `experiment`, the checker formed the modulo-nine
class from the leading-unit formula **and the actual exact fine remainder**
via (23), without reading the already computed coarse quotient, and sampled
one-digit avoidance at length \(2j\). For \(2\le j\le80\), it performed 953
exact prefix checks. No selected-class grid contained a one-digit-avoiding
point after \(j=16\) on this finite range. However, the naive relative
discrepancy estimate still failed 42 times. The largest ratio was at
\(j=16,D/9=3\), for forbidden digit 4 or 7:

\[
 N=1,\qquad {D\over9}(9/10)^{32}=0.103010514608\ldots,
 \qquad {N\over(D/9)(9/10)^{32}}=9.7077468625\ldots.           \tag{25}
\]

Thus the exact selector materially shrinks the finite grid, but it does not
repair the false pointwise relative-resonance bound.

## 7. What this changes, and what remains

The useful new input is the selector tower (23)--(24): the actual
three-primary coarse state is no longer an arbitrary member of all \(D_j\)
grid classes once the fine remainder is fixed. At every fixed depth \(k\),
its class is governed by the finite staircase (17) and sparse impulses (18).

The obstruction is equally exact:

- fixed \(k\) buys only a constant factor \(3^k\), insufficient against a
  general actual-shift resonance term;
- increasing \(k\) makes the survivor window grow like \(3^k\); at
  \(k=a_j-1\), the selector is a singleton encoding of the original actual
  numerator;
- the finite mod-nine occupancy improvement does not imply an eventual
  theorem, a prescribed word hit, normality, or V1;
- a complete proof still needs cancellation tied to the actual fine phase,
  or a multiscale argument that exploits the entire selector tower without
  degenerating into the singleton tautology.

The canonical every-word statement therefore remains a `conjecture`, and no
completion notification is warranted.
