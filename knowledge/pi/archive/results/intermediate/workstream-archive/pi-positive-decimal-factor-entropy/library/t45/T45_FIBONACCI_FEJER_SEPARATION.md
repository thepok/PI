# T45: Fibonacci-word finite-irrationality sibling separation

Status: `proof sketch`

Scope label: **non-pi sibling separation only**. This note neither proves nor
disproves C1 for pi, and it proves no cancellation statement for the fixed
decimal orbit of pi.

## 1. Provenance and immutable problem

- Canonical local source: `pi-positive-decimal-factor-entropy.txt`, retained
  byte-for-byte beside this note.
- Canonical source URL: none recorded; the question was formulated locally.
- Canonical SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Accessed and hash-checked: 2026-08-01.
- T45 is a sibling test. The canonical question about pi remains open.

The canonical statement asks whether one fixed `eta > 0` gives
`p_pi(m) >= 10^(eta*m)` for every sufficiently large `m`. Nothing below
changes that quantifier or substitutes the sibling real for pi.

## 2. Normalized conventions and theorem

Let `sigma` be the morphism

```text
sigma(0) = 01,    sigma(1) = 0.
```

The words `sigma^k(0)` are nested prefixes. Define the zero-indexed Fibonacci
word `f = (f_j)_(j>=0)` to be their limit:

```text
f = 010010100100101001010010010100...
```

Define the one explicitly indexed decimal real

```text
x := sum_(j>=0) f_j / 10^(j+1)
   = 0.010010100100101001010010010100... (base 10).
```

All digits are `0` or `1`. Moreover,
`sigma^(k+1)(0)=sigma^k(0)sigma^(k-1)(0)` for `k>=1`, so the limit has
infinitely many `1`s and is not eventually zero. Thus this series is the
convention and gives the usual unique nonterminating decimal expansion. For
`m>=1`, define

```text
F_x(m) := { (f_i,...,f_(i+m-1)) : i>=0 },
p_x(m) := |F_x(m)|.
```

Thus factors are contiguous factors at all starts in the infinite word, not
aligned blocks and not factors restricted to one finite prefix.

Put

```text
e(t) := exp(2*pi*i*t),
y_j := frac(10^j*x) = sum_(k>=0) f_(j+k)/10^(k+1),
S_M(h) := sum_(j=0)^(M-1) e(h*y_j).
```

For integers `M,H>=1`, use the complete strict-band triangular energy

```text
E_H(M) := sum_(h in Z, |h|<H) (1-|h|/H) |S_M(h)|^2.       (2.1)
```

The sum includes `h=0` and both signs of every nonzero frequency. On the pair
side it includes every ordered pair `(i,j)`, including the diagonal.

Let

```text
phi := (1+sqrt(5))/2,        mu(x) := ordinary irrationality exponent.
```

### Theorem T45

For the fixed real `x` above:

1. `p_x(m)=m+1` for every integer `m>=1`.
2. `mu(x)=phi^2=(3+sqrt(5))/2`.
3. There exists an integer `Q0>=1`, not numerically determined here, such
   that for every integer `q>=Q0` and every `z in Z`,

   ```text
   1/q^3 < |x-z/q|.                                           (2.2)
   ```

4. Set `M_n=10^n` and `H_n=M_n/2` for `n>=1`. For every
   `r=0,...,n-1`, let `h_(n,r)=10^r`. Then

   ```text
   0 < h_(n,r) < H_n,    |S_(M_n)(h_(n,r))| > M_n/2.          (2.3)
   ```

   Consequently, for every requested integer endpoint `R>=0`, every `n>=R+1`
   supplies the strictly admissible chain `10^r`, `0<=r<=R`, with the one
   uniform linear amplitude constant `1/2`.
5. With

   ```text
   D_n := floor(n/3)+1,
   L_n := ceil(M_n/D_n),
   A   := 1+27*pi^2/64,
   ```

   the complete energy satisfies the explicit bounds

   ```text
   E_(H_n)(M_n)/(H_n*M_n^2)
      <= A*L_n/M_n
      <= A*(1/D_n+1/M_n)
      <  A*(3/n+1/10^n),                                    (2.4)
   ```

   and hence

   ```text
   lim_(n->infinity) E_(H_n)(M_n)/(H_n*M_n^2) = 0.           (2.5)
   ```

Items 3, 4, and 5 hold simultaneously for this same fixed irrational `x`.

## 3. Exact source pins

The retained files and their hashes are listed in `SOURCE_MANIFEST.md` and
checked by `verify.sh`. Page locators below refer to the displayed PDF page
number, with printed page numbers stated where they differ.

### 3.1 Complexity and irrationality exponent

Y. Bugeaud and D. H. Kim, *A new complexity function, repetitions in Sturmian
words, and irrationality exponents of Sturmian numbers*, Transactions of the
American Mathematical Society 371 (2019), 3281-3308, DOI
`10.1090/tran/7378`. Retained open version: arXiv `1510.00279v3`.

Exact locators in `bugeaud-kim-1510.00279v3.pdf`:

- PDF p. 1 defines
  `p(n,w)=#{w_k...w_(k+n-1):k>=1}`.
- Definition 1.2, PDF p. 2, defines a Sturmian word by
  `p(n,w)=n+1` for every `n>=1`.
- PDF p. 5, the paragraph beginning "Let f denote the Fibonacci word",
  identifies `f=01001010...` and states: "The Fibonacci word is a Sturmian
  word".
- Definition 3.2, PDF p. 6, defines
  `rep(w)=liminf r(n,w)/n`.
- PDF p. 7, the paragraph immediately after Theorem 3.4, states
  `rep(f)=phi`.
- Definition 4.1, PDF p. 8, defines the ordinary irrationality exponent via
  infinitely many rational solutions to `|xi-p/q|<1/q^mu`.
- Theorem 4.5, PDF p. 10, states for every integer base `b>=2` and every
  Sturmian word `w=w_1w_2...` that

  ```text
  mu(sum_(k>=1) w_k/b^k) = rep(w)/(rep(w)-1).                (3.1)
  ```

Our zero-indexed `f_j` is their one-indexed `f_(j+1)`, and our series is
exactly their series at `b=10`. Thus Definition 1.2 and the PDF p. 5 statement
give item 1. Equation (3.1), `rep(f)=phi`, and `phi-1=1/phi` give

```text
mu(x)=phi/(phi-1)=phi^2=(3+sqrt(5))/2,                       (3.2)
```

which proves item 2. This is the ordinary unrestricted irrationality exponent,
not the combinatorial critical exponent of the word.

### 3.2 Fixed-point convention and fourth-power exclusion

F. Mignosi and G. Pirillo, *Repetitions in the Fibonacci infinite word*,
RAIRO Informatique theorique et applications 26 (1992), 199-204, DOI
`10.1051/ita/1992260301991`.

Exact locators in `mignosi-pirillo-1992.pdf`:

- Printed p. 200, PDF p. 3, defines the Fibonacci infinite word by iterating
  `psi(a)=ab`, `psi(b)=a` from `a`, obtaining
  `abaababaabaabab...`.
- Proposition 1, printed p. 201, PDF p. 4, records Karhumaki's result: "The
  Fibonacci infinite word f contains no 4-power."
- Proposition 6, printed pp. 202-203, PDF pp. 5-6, proves the sharper critical
  exponent `2+(sqrt(5)+1)/2`, which is strictly below `4`.

The coding `a->0`, `b->1` intertwines `psi` with `sigma` letter by letter:

```text
a -> ab -> 01 = sigma(0),       b -> a -> 0 = sigma(1).
```

Therefore their word is exactly our word, with no reversal, shift, or
complement. Karhumaki's fourth-power exclusion, as stated in their Proposition
1, applies verbatim after this renaming. Proposition 6 is Mignosi-Pirillo's
sharper critical-exponent result.

## 4. Eventual T36-shaped irrationality bound

This section proves item 3 and deliberately does not claim an effective value
of `Q0`.

By (3.2),

```text
mu(x)=phi^2<3.                                             (4.1)
```

If (2.2) failed for every onset, there would be unbounded positive
denominators `q` and integers `z` with

```text
|x-z/q| <= q^(-3).                                        (4.2)
```

Equality in (4.2) is impossible: it would make
`x=z/q+q^(-3)` or `x=z/q-q^(-3)` rational, while Theorem 4.5 explicitly
applies to the irrational number represented by the Sturmian expansion.
Thus every selected pair satisfies the strict inequality
`|x-z/q|<q^(-3)`.

These unbounded denominators give infinitely many rational values satisfying
that inequality. Indeed, if only finitely many rational values `rho` occurred,
then every fixed positive distance `|x-rho|` would force
`q<|x-rho|^(-1/3)`, bounding all their denominators. Infinitely many rational
approximations at exponent `3` contradict (4.1) and Definition 4.1. Hence an
existential `Q0` in (2.2) exists.

In the exact terminology of the kernel-checked T36 module, this says

```text
exists Q0 : N, EffectiveIrrationality x 3 Q0,
```

where `EffectiveIrrationality x mu Q0` is line 67 of T36 and means

```text
1<mu and, for all q>=Q0 with q>0 and all z in Z,
1/q^mu < |x-z/q|.
```

The onset is existential because the cited irrationality-exponent theorem is
not used here with an effective enumeration of the exceptional rationals.
For comparison only, applying T36's
`effectiveIrrationality_periodic_window_gap` at `mu=3` says that any exact
decimal periodic window with preperiod `a`, period `p`, length `L`, and
displayed denominator at least `Q0` obeys

```text
L <= 2*a+3*p+1.                                           (4.3)
```

No periodic-window premise is used in the chain or energy proof below.

## 5. Explicit decimal-frequency chains

This section proves item 4. It uses exactly T40's convention

```text
decimalFrequency(h,r)=10^r*h,
DecimalFrequencyAdmissible(H,h,r) iff 10^r*|h|<H.
```

It also uses the fixed-real orbit-sum shape of T42, but with the present fixed
seed `x`: `S_M(h)` is the sum of `phase h` over `baseTenOrbit x j`.
No theorem about T42's different fixed seed is transferred to `x`.

First, every suffix lies in one fixed short arc:

```text
0 <= y_j <= sum_(k>=0) 10^(-(k+1)) = 1/9.                 (5.1)
```

Multiplication of the frequency by `10^r` is the exact decimal index shift:

```text
e(10^r*y_j)=e(10^(j+r)*x)=e(y_(j+r)).                     (5.2)
```

The equality uses only that `e` is invariant under integer translation.
Since `0<=2*pi*y_k<=2*pi/9<pi/3`,

```text
Re(e(y_k)) = cos(2*pi*y_k) >= cos(2*pi/9) > 1/2.          (5.3)
```

For every `M>=1` and every `r>=0`, (5.2)-(5.3) therefore give the uniform
bound

```text
|S_M(10^r)| >= Re(S_M(10^r)) > M/2.                       (5.4)
```

Now fix `n>=1`, `M=10^n`, and `H=M/2=5*10^(n-1)`. For the complete range
`0<=r<=n-1`,

```text
1 <= 10^r <= 10^(n-1) = H/5 < H.                         (5.5)
```

Equations (5.4)-(5.5) prove (2.3), including strict admissibility, all range
endpoints, and the uniform amplitude constant `1/2`. For a requested chain
`0<=r<=R` for an integer `R>=0`, choose any `n>=R+1`; this is stronger than merely having a
cofinal subsequence of scales.

For later comparison, these positive and negative chain frequencies alone
give the completely explicit lower bound

```text
E_H(M)
 >= M^2 + 2*(M^2/4)*sum_(r=0)^(n-1) (1-10^r/H)
 =  M^2 + (M^2/2)*(n-2*(M-1)/(9*M)).                      (5.6)
```

After division by `H*M^2`, (5.6) is of order `n/M` and therefore does not
conflict with the vanishing upper bound proved next.

## 6. Finite-prefix multiplicity, proved directly

The only combinatorial input in this section is the source-pinned exclusion of
fourth powers. Unique ergodicity and limiting factor frequencies are not used.

### Lemma 6.1: repeated-factor spacing

If equal length-`ell` factors begin at `a<b`, then

```text
b-a > ell/3.                                               (6.1)
```

Proof. Put `d=b-a`. Equality gives
`f_(a+t)=f_(a+d+t)` for every `0<=t<ell`. If `3*d<=ell`, the length-`4*d`
factor beginning at `a` has period `d`, hence is the fourth power of its first
`d` letters. This contradicts Karhumaki's result as recorded in
Mignosi-Pirillo Proposition 1. Therefore
`3*d>ell`, which is (6.1). QED.

### Lemma 6.2: finite-prefix multiplicity

Among the starts `0,...,M-1`, every fixed length-`ell` factor occurs at most

```text
L(M,ell) := ceil(M/(floor(ell/3)+1))                       (6.2)
```

times.

Proof. Let `D=floor(ell/3)+1`. By (6.1), consecutive occurrences are at
integer distance at least `D`. Thus `q` occurrences span at least
`(q-1)D` positions inside an interval of length `M-1`, so

```text
q <= floor((M-1)/D)+1 = ceil(M/D).                         (6.3)
```

QED.

At the energy scale we take `ell=n`, so (6.2) is exactly the displayed `L_n`
from the theorem.

## 7. Decimal suffix separation

For general `ell>=1`, let the integer label of the length-`ell` prefix of
suffix `y_j` be

```text
P_j^(ell) := sum_(k=0)^(ell-1) f_(j+k)*10^(ell-1-k).
```

Then

```text
y_j = P_j^(ell)/10^ell + R_j^(ell),
0 <= R_j^(ell) <= 1/(9*10^ell).                            (7.1)
```

### Lemma 7.1: distinct-prefix separation

If `P_i^(ell) != P_j^(ell)`, then

```text
|y_i-y_j| >= 8/(9*10^ell).                                (7.2)
```

Proof. Distinct integer labels differ by at least `1`. The difference of two
remainders from the interval in (7.1) has absolute value at most
`1/(9*10^ell)`, not twice that value. The reverse triangle inequality gives
(7.2). QED.

By (5.1), `|y_i-y_j|<=1/9<1/2`; hence circular distance is ordinary distance:

```text
||y_i-y_j||_(R/Z) = |y_i-y_j|.                            (7.3)
```

This verifies explicitly that no decimal or circle wraparound is hidden.

### Lemma 7.2: ranked decimal shells

Fix `ell=n`, so `10^ell=M`. Fix an index `i`. Order the distinct occupied
prefix labels greater than `P_i^(n)`. If a label is the `r`-th such label,
where `r>=1`, then every suffix `y_j` in that label class obeys

```text
y_j-y_i >= (r-1/9)/M >= 8*r/(9*M).                        (7.4)
```

The same estimate holds in absolute value for the `r`-th occupied label to
the left. Each such right or left shell contains at most `L_n` indices by
Lemma 6.2. Every index with a prefix different from `i` lies in exactly one of
these shells.

Proof. Distinct integer labels on one side differ from `P_i^(n)` by at least
`r`; (7.1) then gives `(r-1/9)/M`. The second inequality in (7.4) is equivalent
to `r>=1`. Multiplicity and exhaustion follow from Lemma 6.2 and ordering the
finite set of occupied labels. QED.

This ranked shell statement is stronger for the present purpose than a bare
count below one radius: it retains both shell sides, shell range `r>=1`, shell
cardinality `L_n`, and the exact separation constant `8/9`.

## 8. Fejer-kernel shell calculation

Define the order-`H-1` normalized Fejer kernel

```text
K_H(t) := sum_(h in Z, |h|<H) (1-|h|/H)e(h*t)
        = (1/H)*(sin(pi*H*t)/sin(pi*t))^2.                 (8.1)
```

The continuous value at an integer is `K_H(0)=H`. Standard elementary sine
bounds give, for every real `t`,

```text
0 <= K_H(t) <= H,                                         (8.2)
```

and, when `delta=||t||_(R/Z)>0`,

```text
K_H(t) <= 1/(4*H*delta^2).                                (8.3)
```

Indeed, the numerator in (8.1) has absolute value at most `1`, while
`|sin(pi*t)|=sin(pi*delta)>=2*delta` for `0<=delta<=1/2`.
This is the same inverse-square decay and strict-band normalization used by
the kernel-checked T8 theorem
`fejerKernel_pred_le_of_dyadicCutoff_le`; here it is applied to the ranked
decimal shells of Lemma 7.2.

Expanding the square in (2.1) and interchanging finite sums gives the exact
complete ordered-pair identity

```text
E_H(M) = sum_(0<=i,j<M) K_H(y_j-y_i).                      (8.4)
```

We now bound every pair in (8.4), with `M=10^n`, `H=M/2`, `D=D_n`, and
`L=L_n`.

### 8.1 Equal-prefix pairs

Let the occupied length-`n` prefix classes have sizes `q_alpha`. Then
`q_alpha<=L` and `sum_alpha q_alpha=M`. There are `M` diagonal ordered pairs,
contributing exactly `M*H`. The equal-prefix off-diagonal contribution is at
most

```text
H*sum_alpha q_alpha*(q_alpha-1)
 <= H*(L-1)*sum_alpha q_alpha
 =  M*(L-1)*H.                                            (8.5)
```

Thus all equal-prefix pairs, including every diagonal pair, contribute at most

```text
L*M*H.                                                     (8.6)
```

### 8.2 One ranked shell

For fixed `i`, one side, and rank `r>=1`, (7.4), (8.3), and the shell
cardinality bound give

```text
shell contribution
 <= L / (4*H*(8*r/(9*M))^2)
 = 81*L*M^2/(256*H*r^2).                                  (8.7)
```

There are at most two shells of each rank, one on each side. Extending the
finite occupied-label sum to all `r>=1` and using
`sum_(r>=1)r^(-2)=pi^2/6`, the different-prefix contribution for fixed `i`
is at most

```text
2*sum_(r>=1) 81*L*M^2/(256*H*r^2)
 = 27*pi^2*L*M^2/(256*H).                                 (8.8)
```

Summing (8.8) over all `M` first coordinates and then using `H=M/2` gives

```text
different-prefix contribution
 <= 27*pi^2*L*M^3/(256*H)
 =  27*pi^2*L*M^2/128.                                    (8.9)
```

No pair is omitted: equal labels are in (8.6), and every unequal label is in
one unique left or right ranked shell for each fixed first coordinate.

### 8.3 Complete bound and limit

Combining (8.6) and (8.9),

```text
E_H(M) <= L*M*H + 27*pi^2*L*M^2/128.                      (8.10)
```

Divide by `H*M^2` and use `H=M/2`:

```text
E_H(M)/(H*M^2)
 <= L/M + (27*pi^2/64)*L/M
 =  (1+27*pi^2/64)*L/M.                                  (8.11)
```

Finally, `L=ceil(M/D)` implies

```text
L/M <= 1/D+1/M.                                           (8.12)
```

Because `D=floor(n/3)+1>n/3` and `M=10^n`, (8.11)-(8.12) give exactly
(2.4). Its right side tends to zero, proving (2.5).

## 9. What the example separates

The same fixed real has all of the following:

- exact linear factor complexity `p_x(m)=m+1`;
- finite ordinary irrationality exponent `phi^2` and the eventual strict
  `q^(-3)` lower bound with an existential onset;
- for every requested length, a strictly admissible decimal-frequency chain
  with the uniform orbit-sum lower bound `M/2`;
- complete normalized Fejer energy density tending to zero at
  `M=10^n`, `H=M/2`.

Therefore replacing T42's seed by a different fixed seed that has finite
irrationality repairs the missing T36 premise at `mu=3`, but it does **not**
turn arbitrarily long decimal-frequency chains into positive complete
normalized spectral density in general. T42's original seed still fails every
fixed T36 effective-irrationality instance. The chains here arise from all
suffixes lying in the short interval `[0,1/9]`, not from T42's long periodic
windows.

This is only a non-pi sibling separation. In particular:

- it makes no assertion about the decimal factor complexity of pi;
- it does not prove or disprove C1;
- it does not transfer the chain to pi;
- it does not prove fixed-pi Fourier cancellation;
- it does not use finite computation as proof.

## 10. Kernel-checked definition pins

These accepted Lean modules were inspected rather than duplicated:

| Module artifact | SHA-256 | Definitions/results used for convention |
|---|---|---|
| `t7/T7FejerSpectralCriterion.lean` | `00c48b94fff7a0df1379d0f46db67cf9599938f7c80f532e3dc2c5d06b1d3c71` | strict signed band, triangular weight, complete pair identity |
| `t8/T8DyadicShellFejer.lean` | `dd73354bf5d978e97722f8c13eda61305c279a5bee8d7c107db04168c1f21ce1` | order-`H-1` kernel height and inverse-square shell decay |
| `t36/T36DecimalPeriodicWindowGap.lean` | `900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781` | `EffectiveIrrationality`, onset quantifier, rounding constant `1` |
| `t40/T40DecimalFrequencyDecimation.lean` | `9eb6b791140f6af579841ea3705b76a2decca224eb8139de456099e98bd4f5e2` | `decimalFrequency`, strict admissibility, exact shift and endpoint convention |
| `t42/T42FixedRealDecimalChains.lean` | `28fd0892cc34baba54c21c34c3bbc30ffa58de5d1f0929299f455a7aed3dbaab` | fixed-real orbit-sum and chain-contribution shapes |

The T42 seed and its theorems are not asserted for this Fibonacci seed. The
analogous Fibonacci claims are proved directly in Sections 5-8.

## 11. Literature search log and review status

| Date | Query/source | Finding |
|---|---|---|
| 2026-08-01 | Bugeaud-Kim arXiv v3 and DOI record | Exact Sturmian complexity convention, Fibonacci identification, `rep(f)=phi`, and Theorem 4.5 giving `mu(x)=phi^2` |
| 2026-08-01 | Mignosi-Pirillo NUMDAM archival PDF | Exact morphism convention and Proposition 1 excluding fourth powers |

Statement checked internally against the canonical hash and the displayed
T40/T42 definitions. Proof and attribution await independent skeptical review;
this note is not a `candidate resolution` or a `verified resolution`.
